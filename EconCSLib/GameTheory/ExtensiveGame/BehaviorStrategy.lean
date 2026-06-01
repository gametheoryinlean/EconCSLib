/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Subgame
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy

Behavior-strategy primitives for the Arena-based extensive-game framework.

This file starts the infrastructure needed for MSZ Theorem 7.5.  The
probabilistic definitions are fuel-indexed so they fit the current Arena
framework, which supports both finite and infinite games.

## Main definitions

* `ExtensiveGame.BehaviorStrategy` - a player chooses a probability
  distribution over actions at each state they control.
* `ExtensiveGame.BehaviorProfile` - one behavior strategy for each player.
* `ExtensiveGame.BehaviorStrategy.IsCompletelyMixed` - every available action
  at a controlled state receives positive probability.
* `ExtensiveGame.BehaviorProfile.probAt` - probability assigned to an action at
  a player-controlled state.
* `ExtensiveGame.reachProb` - finite-fuel probability of reaching a state.
* `ExtensiveGame.expectedPayoff` - finite-fuel expected payoff under a behavior
  profile.
* `ExtensiveGame.BehaviorProfile.deviate` - unilateral behavior-strategy
  deviations.
* `ExtensiveGame.ReachedSubgamePayoffTransfer` - affine payoff-transfer data for
  a positively reached subgame.
* `ExtensiveGame.IsBehaviorNashEq` - finite-fuel behavioral Nash equilibrium.
* `ExtensiveGame.BehaviorProfile.restrictSubgame` - restriction to `subgameAt`.
* `ExtensiveGame.BehaviorProfile.liftReachableSubgame` - local lift of
  reachable-subgame deviations, preserving the baseline profile outside the
  reached subgame.

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Definition 7.6 and Theorem 7.5.
-/

namespace ExtensiveGame

variable {iota U : Type*}

/-! ### Subgame simp lemmas -/

@[simp]
theorem subgameAt_init (G : ExtensiveGame iota U) (s : G.State) :
    (G.subgameAt s).init = s := rfl

@[simp]
theorem subgameAt_mover (G : ExtensiveGame iota U) (s t : G.State) :
    (G.subgameAt s).mover t = G.mover t := rfl

@[simp]
theorem subgameAt_payoff (G : ExtensiveGame iota U) (s t : G.State) (i : iota) :
    (G.subgameAt s).payoff t i = G.payoff t i := rfl

@[simp]
theorem subgameAt_next (G : ExtensiveGame iota U) (s t : G.State)
    (a : G.Action t) :
    (G.subgameAt s).next t a = G.next t a := rfl

instance subgameAt_action_fintype (G : ExtensiveGame iota U) (root : G.State)
    [inst : (s : G.State) -> Fintype (G.Action s)] :
    (s : (G.subgameAt root).State) -> Fintype ((G.subgameAt root).Action s) :=
  inst

instance subgameAt_isEmpty_decidable (G : ExtensiveGame iota U) (root : G.State)
    [inst : (s : G.State) -> Decidable (IsEmpty (G.Action s))] :
    (s : (G.subgameAt root).State) ->
      Decidable (IsEmpty ((G.subgameAt root).Action s)) :=
  inst

instance reachableSubgameAt_action_fintype (G : ExtensiveGame iota U)
    (root : G.State) [inst : (s : G.State) -> Fintype (G.Action s)] :
    (s : (G.reachableSubgameAt root).State) ->
      Fintype ((G.reachableSubgameAt root).Action s) :=
  fun s => inst s.1

instance reachableSubgameAt_isEmpty_decidable (G : ExtensiveGame iota U)
    (root : G.State)
    [inst : (s : G.State) -> Decidable (IsEmpty (G.Action s))] :
    (s : (G.reachableSubgameAt root).State) ->
      Decidable (IsEmpty ((G.reachableSubgameAt root).Action s)) :=
  fun s => inst s.1

/-! ### Behavior strategies -/

/-- A behavior strategy for player `i`: at every state controlled by `i`, choose
    a probability distribution over the actions available at that state.

This is a state-based primitive.  A later imperfect-information layer can impose
the usual information-set consistency condition by requiring equal
distributions across states in the same information set. -/
def BehaviorStrategy (G : ExtensiveGame iota U) (i : iota)
    [(s : G.State) -> Fintype (G.Action s)] : Type _ :=
  (s : G.State) -> G.mover s = some i -> stdSimplex Real (G.Action s)

/-- A behavior-strategy profile: one behavior strategy for every player. -/
def BehaviorProfile (G : ExtensiveGame iota U)
    [(s : G.State) -> Fintype (G.Action s)] : Type _ :=
  (i : iota) -> G.BehaviorStrategy i

namespace BehaviorStrategy

/-! ### Complete mixing -/

/-- A behavior strategy is completely mixed if every available action at every
state controlled by the player receives positive probability.

This is the state-based behavior-strategy part of MSZ Definition 7.6.  The
later imperfect-information layer can identify states inside the same
information set; this predicate is already the local full-support condition
used by the current Arena-based behavior-strategy API. -/
def IsCompletelyMixed {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) : Prop :=
  forall (s : G.State) (h : G.mover s = some i) (a : G.Action s),
    0 < (beta s h).val a

end BehaviorStrategy

namespace BehaviorProfile

/-! ### Complete mixing -/

/-- A behavior profile is completely mixed if each player's behavior strategy is
completely mixed. -/
def IsCompletelyMixed {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) : Prop :=
  forall i : iota, BehaviorStrategy.IsCompletelyMixed (G := G) (beta i)

/-- A completely mixed behavior profile gives a completely mixed behavior
strategy for each player. -/
theorem IsCompletelyMixed.player {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {beta : G.BehaviorProfile}
    (hbeta : IsCompletelyMixed beta) (i : iota) :
    BehaviorStrategy.IsCompletelyMixed (G := G) (beta i) :=
  hbeta i

/-- The probability that a behavior profile assigns to action `a` at a state
    controlled by player `i`. -/
def probAt {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile)
    {s : G.State} {i : iota} (h : G.mover s = some i) (a : G.Action s) : Real :=
  (beta i s h).val a

/-- The action probability induced by a behavior profile at a state.

At a player-controlled state this reads the controlling player's behavior
strategy.  At a chance state it returns `0`; this placeholder is compatible with
the `NoChance` layer and can be replaced by explicit chance probabilities in a
later stochastic layer. -/
def actionProb {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (s : G.State) (a : G.Action s) : Real :=
  match h : G.mover s with
  | some i => (beta i s h).val a
  | none => 0

/-- A behavior profile assigns nonnegative probability to every action. -/
theorem actionProb_nonneg {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (s : G.State) (a : G.Action s) :
    0 <= beta.actionProb s a := by
  unfold actionProb
  split
  · rename_i i hm
    exact (beta i s hm).property.1 a
  · norm_num

/-- At player-controlled states, a completely mixed behavior profile gives
positive probability to every available action. -/
theorem IsCompletelyMixed.actionProb_pos {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {beta : G.BehaviorProfile}
    (hbeta : IsCompletelyMixed beta) {s : G.State} {i : iota}
    (hm : G.mover s = some i) (a : G.Action s) :
    0 < beta.actionProb s a := by
  unfold actionProb
  split
  · rename_i j hs
    exact hbeta j s hs a
  · rename_i hs
    rw [hm] at hs
    cases hs

/-! ### Deviations -/

/-- Unilateral deviation of a behavior profile: player `who` switches to
`beta'`, while every other player keeps the original behavior strategy. -/
def deviate {G : ExtensiveGame iota U} [(s : G.State) -> Fintype (G.Action s)]
    [DecidableEq iota] (beta : G.BehaviorProfile) (who : iota)
    (beta' : G.BehaviorStrategy who) : G.BehaviorProfile :=
  Function.update beta who beta'

@[simp]
theorem deviate_same {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) (beta' : G.BehaviorStrategy who) :
    beta.deviate who beta' who = beta' := by
  simp [deviate]

@[simp]
theorem deviate_of_ne {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) (beta' : G.BehaviorStrategy who)
    {other : iota} (h : other ≠ who) :
    beta.deviate who beta' other = beta other := by
  simp [deviate, h]

end BehaviorProfile

namespace BehaviorStrategy

/-! ### Subgame restriction -/

/-- Restrict a behavior strategy to the subgame rooted at `root`.

Since `subgameAt` keeps the same state space, actions, and movers, this is just
the same local action distribution viewed from the subgame. -/
def restrictSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) (root : G.State) :
    (G.subgameAt root).BehaviorStrategy i :=
  fun s h => beta s h

theorem restrictSubgame_eq_self {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) (root : G.State) :
    beta.restrictSubgame root = beta := by
  funext s h
  rfl

/-- View a behavior strategy for a subgame as a behavior strategy for the
original game.

This is well-typed because `subgameAt` keeps the same state space, actions, and
movers; it only changes the initial state. -/
def liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    (beta : (G.subgameAt root).BehaviorStrategy i) : G.BehaviorStrategy i :=
  fun s h => beta s h

theorem liftSubgame_eq_self {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    (beta : (G.subgameAt root).BehaviorStrategy i) :
    beta.liftSubgame = beta := by
  funext s h
  rfl

@[simp]
theorem restrictSubgame_liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    (beta : (G.subgameAt root).BehaviorStrategy i) :
    beta.liftSubgame.restrictSubgame root = beta := by
  funext s h
  rfl

/-! ### Reachable-state subgame restriction -/

/-- Restrict a behavior strategy to the subtype subgame consisting only of
states reachable from `root`. -/
def restrictReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota}
    (beta : G.BehaviorStrategy i) (root : G.State) :
    (G.reachableSubgameAt root).BehaviorStrategy i :=
  fun s h => beta s.1 h

/-- Lift a reachable-subgame behavior strategy to the original game, preserving
the baseline strategy outside the reachable subgame. -/
def liftReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorStrategy i)
    (beta : (G.reachableSubgameAt root).BehaviorStrategy i) :
    G.BehaviorStrategy i :=
  fun s h =>
    if hs : Arena.Reachable G.toArena root s then
      beta ⟨s, hs⟩ h
    else
      base s h

@[simp]
theorem restrictReachableSubgame_liftReachableSubgame
    {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {i : iota} {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorStrategy i)
    (beta : (G.reachableSubgameAt root).BehaviorStrategy i) :
    (base.liftReachableSubgame beta).restrictReachableSubgame root = beta := by
  funext s h
  cases s with
  | mk state hstate =>
      simp [restrictReachableSubgame, liftReachableSubgame, hstate]

end BehaviorStrategy

namespace BehaviorProfile

/-- Restrict a behavior profile to the subgame rooted at `root`. -/
def restrictSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (root : G.State) :
    (G.subgameAt root).BehaviorProfile :=
  fun i => (beta i).restrictSubgame root

theorem restrictSubgame_eq_self {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (root : G.State) :
    beta.restrictSubgame root = beta := by
  funext i s h
  rfl

/-- View a behavior profile for a subgame as a behavior profile for the original
game. -/
def liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {root : G.State}
    (beta : (G.subgameAt root).BehaviorProfile) : G.BehaviorProfile :=
  fun i => (beta i).liftSubgame

@[simp]
theorem restrictSubgame_liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {root : G.State}
    (beta : (G.subgameAt root).BehaviorProfile) :
    beta.liftSubgame.restrictSubgame root = beta := by
  funext i s h
  rfl

/-- Restrict a behavior profile to the subtype subgame of states reachable from
`root`. -/
def restrictReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (root : G.State) :
    (G.reachableSubgameAt root).BehaviorProfile :=
  fun i => (beta i).restrictReachableSubgame root

/-- Lift a reachable-subgame behavior profile to the original game, preserving
the baseline profile outside the reachable subgame. -/
def liftReachableSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorProfile)
    (beta : (G.reachableSubgameAt root).BehaviorProfile) :
    G.BehaviorProfile :=
  fun i => (base i).liftReachableSubgame (beta i)

@[simp]
theorem restrictReachableSubgame_liftReachableSubgame
    {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (base : G.BehaviorProfile)
    (beta : (G.reachableSubgameAt root).BehaviorProfile) :
    (base.liftReachableSubgame beta).restrictReachableSubgame root = beta := by
  funext i s h
  simp [restrictReachableSubgame, liftReachableSubgame]

/-- A reachable-subgame deviation can be lifted to an original-game deviation
that changes the deviating player only below `root`. -/
theorem restrictReachableSubgame_deviate_liftReachableSubgame
    {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    {root : G.State}
    [(s : G.State) -> Decidable (Arena.Reachable G.toArena root s)]
    (beta : G.BehaviorProfile) (who : iota)
    (beta' : (G.reachableSubgameAt root).BehaviorStrategy who) :
    (beta.deviate who ((beta who).liftReachableSubgame beta')).restrictReachableSubgame root =
      (beta.restrictReachableSubgame root).deviate who beta' := by
  funext i s h
  by_cases hi : i = who
  · subst hi
    simp [restrictReachableSubgame]
  · simp [restrictReachableSubgame, deviate, hi]

@[simp]
theorem actionProb_restrictSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (root s : G.State) (a : G.Action s) :
    (beta.restrictSubgame root).actionProb s a = beta.actionProb s a := by
  change beta.actionProb s a = beta.actionProb s a
  rfl

/-- Restricting a deviated behavior profile to a subgame is the same as
restricting first and then applying the corresponding deviation inside the
subgame. -/
theorem restrictSubgame_deviate {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) (beta' : G.BehaviorStrategy who)
    (root : G.State) :
    (beta.deviate who beta').restrictSubgame root =
      (beta.restrictSubgame root).deviate who (beta'.restrictSubgame root) := by
  funext i s h
  by_cases hi : i = who
  · subst hi
    simp [restrictSubgame, BehaviorStrategy.restrictSubgame]
  · simp [restrictSubgame, BehaviorStrategy.restrictSubgame, deviate, hi]

/-- A subgame deviation can be lifted to an original-game deviation whose
restriction to the subgame is the intended subgame deviation. -/
theorem restrictSubgame_deviate_liftSubgame {G : ExtensiveGame iota U}
    [(s : G.State) -> Fintype (G.Action s)] [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) {root : G.State}
    (beta' : (G.subgameAt root).BehaviorStrategy who) :
    (beta.deviate who beta'.liftSubgame).restrictSubgame root =
      (beta.restrictSubgame root).deviate who beta' := by
  rw [restrictSubgame_deviate, BehaviorStrategy.restrictSubgame_liftSubgame]

end BehaviorProfile

/-! ### Reach probabilities -/

/-- Finite-fuel probability of reaching `target` from `start` under a behavior
profile.

The definition records the probability of hitting `target` within the remaining
fuel.  It is intentionally fuel-indexed, matching `ExtensiveGame.Play`, because
the Arena framework also supports infinite games. -/
noncomputable def reachProbFrom {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (start target : G.State) : Nat -> Real
  | 0 => if start = target then 1 else 0
  | fuel + 1 =>
      if start = target then
        1
      else
        Finset.univ.sum fun a : G.Action start =>
          beta.actionProb start a * reachProbFrom beta (G.next start a) target fuel

/-- Finite-fuel probability of reaching `target` from the initial state. -/
noncomputable def reachProb (G : ExtensiveGame iota U)
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (target : G.State) (fuel : Nat) : Real :=
  reachProbFrom beta G.init target fuel

namespace BehaviorProfile

/-- Completely mixed behavior together with the current positive-reach
interface for every subgame root at a fixed fuel.

In finite games with explicit positive chance probabilities, the second
component follows from complete mixing and reachability of every game-tree
vertex.  The Arena behavior layer currently keeps chance probabilities and
finite-depth bounds abstract, so Corollary 7.7 uses this as the precise bridge
from complete mixing to the positive-reach hypothesis of Theorem 7.5. -/
def IsCompletelyMixedWithPositiveReach {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    (beta : G.BehaviorProfile) (fuel : Nat) : Prop :=
  IsCompletelyMixed beta /\ forall root : G.State, 0 < reachProb G beta root fuel

/-- The complete-mixing component of
`IsCompletelyMixedWithPositiveReach`. -/
theorem IsCompletelyMixedWithPositiveReach.mixed {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hbeta : IsCompletelyMixedWithPositiveReach beta fuel) :
    IsCompletelyMixed beta :=
  hbeta.1

/-- The positive-reach component of
`IsCompletelyMixedWithPositiveReach`. -/
theorem IsCompletelyMixedWithPositiveReach.reach_pos {G : ExtensiveGame iota U}
    [DecidableEq G.State] [(s : G.State) -> Fintype (G.Action s)]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hbeta : IsCompletelyMixedWithPositiveReach beta fuel) (root : G.State) :
    0 < reachProb G beta root fuel :=
  hbeta.2 root

end BehaviorProfile

/-! ### Expected payoff -/

/-- Finite-fuel expected payoff from `start` under a behavior profile.

If the fuel runs out, or if a terminal state is reached, the current state's
payoff is used.  At a chance state without explicit chance probabilities, the
current payoff is also used; the intended no-chance use case rules out
nonterminal chance states by assuming `NoChance G`. -/
noncomputable def expectedPayoffFrom {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (start : G.State) : Nat -> iota -> Real
  | 0, who => G.payoff start who
  | fuel + 1, who =>
      if IsEmpty (G.Action start) then
        G.payoff start who
      else
        match G.mover start with
        | some _ =>
            Finset.univ.sum fun a : G.Action start =>
              beta.actionProb start a * expectedPayoffFrom beta (G.next start a) fuel who
        | none => G.payoff start who

/-- Finite-fuel expected payoff from the initial state under a behavior profile. -/
noncomputable def expectedPayoff (G : ExtensiveGame iota Real)
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (fuel : Nat) (who : iota) : Real :=
  expectedPayoffFrom beta G.init fuel who

@[simp]
theorem expectedPayoffFrom_restrictSubgame {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (root start : G.State) (fuel : Nat) (who : iota) :
    expectedPayoffFrom (G := G.subgameAt root) (beta.restrictSubgame root)
        start fuel who =
      expectedPayoffFrom (G := G) beta start fuel who := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      unfold expectedPayoffFrom
      by_cases hterm : IsEmpty (G.Action start)
      · have htermSub : IsEmpty ((G.subgameAt root).Action start) := hterm
        simp [hterm, htermSub]
      · have htermSub : ¬ IsEmpty ((G.subgameAt root).Action start) := hterm
        cases hm : G.mover start with
        | none => simp [hterm, htermSub, hm]
        | some mover =>
            simp [hterm, htermSub, hm, BehaviorProfile.actionProb_restrictSubgame]
            apply Finset.sum_congr rfl
            intro a _ha
            have hih := ih (G.next start a)
            rw [hih]

@[simp]
theorem expectedPayoff_restrictSubgame_init {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    (beta : G.BehaviorProfile) (fuel : Nat) (who : iota) :
    expectedPayoff (G.subgameAt G.init) (beta.restrictSubgame G.init) fuel who =
      expectedPayoff G beta fuel who := by
  simp [expectedPayoff]

/-- The subgame payoff of a lifted original-game deviation agrees with the
payoff of the corresponding subgame deviation. -/
theorem expectedPayoff_restrictSubgame_deviate_liftSubgame
    {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    (beta : G.BehaviorProfile) (who : iota) {root : G.State}
    (beta' : (G.subgameAt root).BehaviorStrategy who) (fuel : Nat) :
    expectedPayoff (G.subgameAt root)
        ((beta.deviate who beta'.liftSubgame).restrictSubgame root) fuel who =
      expectedPayoff (G.subgameAt root)
        ((beta.restrictSubgame root).deviate who beta') fuel who := by
  rw [BehaviorProfile.restrictSubgame_deviate_liftSubgame]

/-- Payoff-transfer data for a subgame reached with positive probability.

This is the numerical decomposition used in the proof of MSZ Theorem 7.5:
for each subgame deviation, the original-game payoff can be written as a common
outside term plus a positive scale times the payoff in the reached subgame.
Later finite-history probability work can prove this interface from the
concrete definition of `reachProb` and expected payoffs. -/
def ReachedSubgamePayoffTransfer (G : ExtensiveGame iota Real)
    [DecidableEq G.State]
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    (beta : G.BehaviorProfile) (root : G.State) (fuel : Nat) : Prop :=
  0 < reachProb G beta root fuel ->
    forall (who : iota) (beta' : (G.subgameAt root).BehaviorStrategy who),
      ∃ outside scale : Real,
        0 < scale ∧
          expectedPayoff G (beta.deviate who beta'.liftSubgame) fuel who =
            outside + scale *
              expectedPayoff (G.subgameAt root)
                ((beta.restrictSubgame root).deviate who beta') fuel who ∧
          expectedPayoff G beta fuel who =
            outside + scale *
              expectedPayoff (G.subgameAt root) (beta.restrictSubgame root) fuel who

/-- The payoff-transfer interface holds trivially for the root subgame. -/
theorem ReachedSubgamePayoffTransfer.init
    (G : ExtensiveGame iota Real)
    [DecidableEq G.State]
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    (beta : G.BehaviorProfile) (fuel : Nat) :
    ReachedSubgamePayoffTransfer G beta G.init fuel := by
  intro _hreach who beta'
  refine ⟨0, 1, by norm_num, ?_, ?_⟩
  · simp only [zero_add, one_mul, expectedPayoff]
    rw [← BehaviorProfile.restrictSubgame_deviate_liftSubgame beta who beta']
    rw [expectedPayoffFrom_restrictSubgame]
    simp
  · simp only [zero_add, one_mul, expectedPayoff]
    rw [expectedPayoffFrom_restrictSubgame]
    simp

/-! ### Behavioral Nash equilibrium -/

/-- A finite-fuel behavioral Nash equilibrium: no player can improve their
finite-fuel expected payoff by a unilateral behavior-strategy deviation. -/
def IsBehaviorNashEq (G : ExtensiveGame iota Real)
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota] (beta : G.BehaviorProfile) (fuel : Nat) : Prop :=
  forall (who : iota) (beta' : G.BehaviorStrategy who),
    expectedPayoff G (beta.deviate who beta') fuel who <=
      expectedPayoff G beta fuel who

/-- A finite-fuel behavioral subgame-perfect equilibrium: at every subgame root,
the restricted behavior profile is a finite-fuel behavioral Nash equilibrium of
that subgame. -/
def IsBehaviorSubgamePerfect (G : ExtensiveGame iota Real)
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota] (beta : G.BehaviorProfile) (fuel : Nat) : Prop :=
  forall root : G.State,
    IsBehaviorNashEq (G.subgameAt root) (beta.restrictSubgame root) fuel

/-- MSZ Theorem 7.5, finite-fuel behavior-strategy interface form.

If a behavior profile is a Nash equilibrium in the original game, a subgame root
is reached with positive probability, and the reached-subgame payoff transfer
interface holds, then the restricted behavior profile is a Nash equilibrium of
the subgame.

The transfer interface is affine rather than equality-based: the original-game
and subgame payoffs share the same outside term and a positive scale, so a
profitable subgame deviation would lift to a profitable original-game
deviation. -/
theorem IsBehaviorNashEq.restrictSubgame_of_reachProb_pos
    {G : ExtensiveGame iota Real}
    [DecidableEq G.State]
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    {beta : G.BehaviorProfile} {root : G.State} {fuel : Nat}
    (hNash : IsBehaviorNashEq G beta fuel)
    (hreach : 0 < reachProb G beta root fuel)
    (hpay : ReachedSubgamePayoffTransfer G beta root fuel) :
    IsBehaviorNashEq (G.subgameAt root) (beta.restrictSubgame root) fuel := by
  intro who beta'
  obtain ⟨outside, scale, hscale, hdev, hbase⟩ := hpay hreach who beta'
  have hglobal := hNash who beta'.liftSubgame
  rw [hdev, hbase] at hglobal
  have hscaled :
      scale *
          expectedPayoff (G.subgameAt root)
            ((beta.restrictSubgame root).deviate who beta') fuel who ≤
        scale *
          expectedPayoff (G.subgameAt root) (beta.restrictSubgame root) fuel who := by
    linarith
  nlinarith [hscale, hscaled]

/-- If every subgame root is reached with positive finite-fuel probability, a
behavioral Nash equilibrium restricts to a Nash equilibrium in every subgame.

This packages repeated applications of
`IsBehaviorNashEq.restrictSubgame_of_reachProb_pos`. -/
theorem IsBehaviorNashEq.toSubgamePerfect_of_reachProb_pos
    {G : ExtensiveGame iota Real}
    [DecidableEq G.State]
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hNash : IsBehaviorNashEq G beta fuel)
    (hreach : forall root : G.State, 0 < reachProb G beta root fuel)
    (hpay : forall root : G.State, ReachedSubgamePayoffTransfer G beta root fuel) :
    IsBehaviorSubgamePerfect G beta fuel := by
  intro root
  exact hNash.restrictSubgame_of_reachProb_pos (hreach root) (hpay root)

/-- MSZ Corollary 7.7, finite-fuel behavior-strategy interface form.

In the current Arena behavior layer, complete mixing is paired with an explicit
positive-reach interface for every subgame root. Under the same affine
payoff-transfer interface used by Theorem 7.5, a completely mixed behavioral
Nash equilibrium is behavioral subgame-perfect. -/
theorem IsBehaviorNashEq.toSubgamePerfect_of_isCompletelyMixed
    {G : ExtensiveGame iota Real}
    [DecidableEq G.State]
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hNash : IsBehaviorNashEq G beta fuel)
    (hbeta : BehaviorProfile.IsCompletelyMixedWithPositiveReach beta fuel)
    (hpay : forall root : G.State, ReachedSubgamePayoffTransfer G beta root fuel) :
    IsBehaviorSubgamePerfect G beta fuel :=
  hNash.toSubgamePerfect_of_reachProb_pos
    (fun root => hbeta.reach_pos root) hpay

/-- Root-subgame special case of the restriction theorem.

When the subgame root is the original initial state, no reach-probability
decomposition is needed: the subgame is definitionally the same continuation
problem with a different `subgameAt` view. -/
theorem IsBehaviorNashEq.restrictSubgame_init
    {G : ExtensiveGame iota Real}
    [(s : G.State) -> Fintype (G.Action s)]
    [(s : G.State) -> Decidable (IsEmpty (G.Action s))]
    [DecidableEq iota]
    {beta : G.BehaviorProfile} {fuel : Nat}
    (hNash : IsBehaviorNashEq G beta fuel) :
    IsBehaviorNashEq (G.subgameAt G.init) (beta.restrictSubgame G.init) fuel := by
  intro who beta'
  have hglobal := hNash who beta'.liftSubgame
  simpa [expectedPayoff, BehaviorProfile.restrictSubgame_deviate_liftSubgame] using hglobal

end ExtensiveGame
