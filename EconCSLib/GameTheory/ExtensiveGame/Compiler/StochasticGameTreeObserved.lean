/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

/-!
# Stochastic-game-tree compiler

This module compiles `StochasticGameTree` into the history-indexed
`ObservedChanceGame` interface.  The presentation is occurrence-sensitive:
private and public observations are complete typed histories, so equal subtree
values at different paths remain distinct decisions.

The compiler preserves the source tree's finite child-occurrence type and
chance `FiniteLaw` definitionally. A source pure policy induces a Dirac behavioral
profile.  Bounded execution then has exactly the same endpoint-subtree law as
the source recursive execution, not merely a coupling or simulation.

Only terminal payoffs are semantic.  The total payoff field required by
`ExtensiveGame` is zero at player and chance nodes.

## Main definitions

* `StochasticGameTree.toExtensiveGame`
* `StochasticGameTree.toObservedChanceGame`
* `StochasticGameTree.policyToBehavioralProfile`
* `StochasticGameTree.endpointLawWithFuel`

## Main results

* `policyHistoryPolicy_player` and `policyHistoryPolicy_chance`
* `stochasticHistoryLawFrom_map_endpoint`
* `stochasticHistoryLawFrom_map_payoff`
* `policyToBehavioralProfile_deviate`
-/

namespace StochasticGameTree

variable {N : Type*}

/-! ### Structural compiler -/

/-- Legal child occurrences at a stochastic-tree state. -/
def arenaAction : StochasticGameTree N → Type _
  | .Leaf _ => Empty
  | .Player _ arity _ => Fin (arity + 1)
  | .Chance arity _ _ => Fin (arity + 1)

/-- Follow a legal child occurrence. -/
def arenaNext :
    (tree : StochasticGameTree N) →
      arenaAction tree → StochasticGameTree N
  | .Leaf _, action => nomatch action
  | .Player _ _ child, action => child action
  | .Chance _ child _, action => child action

/-- The root-independent Arena of stochastic-tree states. -/
def treeArena (N : Type*) : Arena where
  State := StochasticGameTree N
  Action := arenaAction
  next := arenaNext

/-- Total payoff field used by the compiled extensive game.

Source leaf payoffs are preserved exactly.  The value is zero at nonterminal
states because those values are outside the terminal-payoff semantics. -/
def statePayoff : StochasticGameTree N → N → ℝ
  | .Leaf payoff => payoff
  | .Player _ _ _ => fun _ => 0
  | .Chance _ _ _ => fun _ => 0

/-- Compile the tree dynamics, movers, and terminal payoffs to the common
Arena-based extensive-game foundation. -/
def toExtensiveGame (root : StochasticGameTree N) :
    ExtensiveGame N ℝ where
  toArena := treeArena N
  init := root
  mover
    | .Leaf _ => none
    | .Player mover _ _ => some mover
    | .Chance _ _ _ => none
  payoff := statePayoff

@[simp]
theorem toExtensiveGame_init (root : StochasticGameTree N) :
    (toExtensiveGame root).init = root := rfl

@[simp]
theorem toExtensiveGame_action_leaf (root : StochasticGameTree N)
    (payoff : N → ℝ) :
    (toExtensiveGame root).Action (.Leaf payoff) = Empty := rfl

@[simp]
theorem toExtensiveGame_action_player (root : StochasticGameTree N)
    (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N) :
    (toExtensiveGame root).Action (.Player mover arity child) =
      Fin (arity + 1) := rfl

@[simp]
theorem toExtensiveGame_action_chance (root : StochasticGameTree N)
    (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1))) :
    (toExtensiveGame root).Action (.Chance arity child law) =
      Fin (arity + 1) := rfl

@[simp]
theorem toExtensiveGame_next_player (root : StochasticGameTree N)
    (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (action : Fin (arity + 1)) :
    (toExtensiveGame root).next (.Player mover arity child) action =
      child action := rfl

@[simp]
theorem toExtensiveGame_next_chance (root : StochasticGameTree N)
    (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1)))
    (action : Fin (arity + 1)) :
    (toExtensiveGame root).next (.Chance arity child law) action =
      child action := rfl

@[simp]
theorem toExtensiveGame_mover_player (root : StochasticGameTree N)
    (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N) :
    (toExtensiveGame root).mover (.Player mover arity child) =
      some mover := rfl

@[simp]
theorem toExtensiveGame_mover_chance (root : StochasticGameTree N)
    (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1))) :
    (toExtensiveGame root).mover (.Chance arity child law) = none := rfl

@[simp]
theorem toExtensiveGame_payoff_leaf (root : StochasticGameTree N)
    (payoff : N → ℝ) :
    (toExtensiveGame root).payoff (.Leaf payoff) = payoff := rfl

/-- Leaves are terminal in the compiled game. -/
theorem toExtensiveGame_isTerminal_leaf (root : StochasticGameTree N)
    (payoff : N → ℝ) :
    (toExtensiveGame root).isTerminal (.Leaf payoff) :=
  ⟨fun action => nomatch action⟩

/-- Player nodes are nonterminal in the compiled game. -/
theorem toExtensiveGame_not_isTerminal_player
    (root : StochasticGameTree N) (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N) :
    ¬ (toExtensiveGame root).isTerminal (.Player mover arity child) := by
  intro hterminal
  exact hterminal.false ⟨0, Nat.zero_lt_succ arity⟩

/-- Chance nodes are nonterminal in the compiled game. -/
theorem toExtensiveGame_not_isTerminal_chance
    (root : StochasticGameTree N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1))) :
    ¬ (toExtensiveGame root).isTerminal (.Chance arity child law) := by
  intro hterminal
  exact hterminal.false ⟨0, Nat.zero_lt_succ arity⟩

/-- Terminality is decidable by inspecting the tree constructor. -/
def toExtensiveGame_terminalDecidable (root : StochasticGameTree N) :
    (tree : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal tree)
  | .Leaf payoff =>
      isTrue (toExtensiveGame_isTerminal_leaf root payoff)
  | .Player mover arity child =>
      isFalse
        (toExtensiveGame_not_isTerminal_player
          root mover arity child)
  | .Chance arity child law =>
      isFalse
        (toExtensiveGame_not_isTerminal_chance
          root arity child law)

instance toExtensiveGame.instTerminalDecidable
    (root : StochasticGameTree N) :
    (tree : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal tree) :=
  toExtensiveGame_terminalDecidable root

/-! ### Occurrence-sensitive observations and chance laws -/

/-- The numeric child index carried by a legal action. -/
def actionIndex (tree : StochasticGameTree N) :
    arenaAction tree → ℕ :=
  match tree with
  | .Leaf _ => fun action => nomatch action
  | .Player _ _ _ => fun action => action.1
  | .Chance _ _ _ => fun action => action.1

/-- Recover the source policy's numeric occurrence path from a typed history. -/
def historyPath {root : StochasticGameTree N} :
    {tree : StochasticGameTree N} →
      (treeArena N).History root tree → List ℕ
  | _, .nil => []
  | _, .snoc history action =>
      historyPath history ++ [actionIndex _ action]

@[simp]
theorem historyPath_nil (root : StochasticGameTree N) :
    historyPath
      (Arena.History.nil :
        (treeArena N).History root root) = [] := rfl

@[simp]
theorem historyPath_snoc {root tree : StochasticGameTree N}
    (history : (treeArena N).History root tree)
    (action : arenaAction tree) :
    historyPath (history.snoc action) =
      historyPath history ++ [actionIndex tree action] := rfl

/-- A nonterminal player-controlled complete history occurrence. -/
abbrev OccurrenceInfo (root : StochasticGameTree N) (i : N) :=
  { history :
    (toExtensiveGame root).toArena.HistoryFrom root //
    (toExtensiveGame root).mover history.1 = some i ∧
      (toExtensiveGame root).toArena.IsDecision history.1 }

/-- Occurrence-sensitive observed presentation of a stochastic tree before its
chance kernels are attached. -/
def toObservedGame (root : StochasticGameTree N) :
    ExtensiveGame.ObservedGame N ℝ :=
  ExtensiveGame.ObservedGame.decisionHistoryInformation
    (toExtensiveGame root)
    (ExtensiveGame.ObservedGame.CompleteInformation.PublicObservationPresentation.trivial
      (toExtensiveGame root))

/-- Extract the constructor-provided chance law at a compiled chance state. -/
def chanceLawAt (root tree : StochasticGameTree N)
    (hchance : (toExtensiveGame root).isChanceState tree) :
    FiniteLaw ((toExtensiveGame root).Action tree) := by
  cases tree with
  | Leaf payoff =>
      exact
        (hchance.2
          (toExtensiveGame_isTerminal_leaf root payoff)).elim
  | Player mover arity child =>
      have : some mover = none := hchance.1
      contradiction
  | Chance arity child law =>
      exact law

/-- Compile a stochastic tree to the canonical observed chance-game layer. -/
def toObservedChanceGame (root : StochasticGameTree N) :
    ExtensiveGame.ObservedChanceGame N ℝ :=
  ExtensiveGame.ObservedChanceGame.withChanceKernel
    (toObservedGame root)
    (fun history hchance =>
      chanceLawAt root history.1 hchance)

@[simp]
theorem toObservedChanceGame_observed
    (root : StochasticGameTree N) :
    (toObservedChanceGame root).observed = toObservedGame root := rfl

@[simp]
theorem chanceLawAt_chance (root : StochasticGameTree N)
    (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1)))
    (hchance :
      (toExtensiveGame root).isChanceState
        (.Chance arity child law)) :
    chanceLawAt root (.Chance arity child law) hchance = law := rfl

/-! ### Source policies and exact compiled execution -/

/-- The concrete action selected by a source policy at an occurrence
information state. -/
def policyActionAt (root : StochasticGameTree N)
    (policy : Policy N) (i : N)
    (information : OccurrenceInfo root i) :
    (toExtensiveGame root).Action information.1.1 := by
  rcases information with
    ⟨⟨tree, history⟩, hmover, _hnonterminal⟩
  cases tree with
  | Leaf payoff =>
      simp [toExtensiveGame] at hmover
  | Player mover arity child =>
      exact policy (historyPath history) mover arity child
  | Chance arity child law =>
      simp [toExtensiveGame] at hmover

/-- A source pure policy as a Dirac behavioral profile on the occurrence
presentation. -/
def policyToBehavioralProfile
    (root : StochasticGameTree N) (policy : Policy N) :
    (toObservedGame root).BehavioralProfile :=
  fun i information =>
    FiniteLaw.pure (policyActionAt root policy i information.1)

/-- At a player occurrence, compiled behavioral execution selects exactly the
source policy's child occurrence. -/
theorem policyHistoryPolicy_player
    (root : StochasticGameTree N) (policy : Policy N)
    (mover : N) (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (history :
      (toExtensiveGame root).toArena.History
        root (.Player mover arity child))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal
        (.Player mover arity child)) :
    ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
        (toObservedChanceGame root)
        (policyToBehavioralProfile root policy)
        ⟨.Player mover arity child, history⟩ hnonterminal =
      FiniteLaw.pure
        (policy (historyPath history) mover arity child) := by
  rw [ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
    _ _ _ hnonterminal mover rfl]
  unfold
    ExtensiveGame.ObservedGame.BehavioralProfile.actionLawAt
    ExtensiveGame.ObservedGame.BehavioralStrategy.actionLawAt
    policyToBehavioralProfile
  change
    (FiniteLaw.pure
      (policyActionAt root policy mover
        ⟨⟨.Player mover arity child, history⟩,
          rfl,
          (toExtensiveGame root).toArena
            |>.isDecision_of_not_isTerminal _ hnonterminal⟩)).map id =
      FiniteLaw.pure
        (policy (historyPath history) mover arity child)
  change
    FiniteLaw.map id
        (FiniteLaw.pure
          (policy (historyPath history) mover arity child)) =
      FiniteLaw.pure
        (policy (historyPath history) mover arity child)
  exact FiniteLaw.map_id _

/-- At a chance occurrence, compiled behavioral execution uses exactly the
source constructor's normalized law. -/
theorem policyHistoryPolicy_chance
    (root : StochasticGameTree N) (policy : Policy N)
    (arity : ℕ)
    (child : Fin (arity + 1) → StochasticGameTree N)
    (law : FiniteLaw (Fin (arity + 1)))
    (history :
      (toExtensiveGame root).toArena.History
        root (.Chance arity child law))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal
        (.Chance arity child law)) :
    ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
        (toObservedChanceGame root)
        (policyToBehavioralProfile root policy)
        ⟨.Chance arity child law, history⟩ hnonterminal =
      law := by
  rw [ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
    _ _ _ hnonterminal rfl]
  rfl

/-- Source-side bounded endpoint law.  It stops at leaves and otherwise uses
the same pure player choice and chance bind as the compiled execution. -/
def endpointLawWithFuel :
    ℕ → Policy N → List ℕ → StochasticGameTree N →
      FiniteLaw (StochasticGameTree N)
  | 0, _policy, _path, tree => FiniteLaw.pure tree
  | _fuel + 1, _policy, _path, .Leaf payoff =>
      FiniteLaw.pure (.Leaf payoff)
  | fuel + 1, policy, path, .Player mover arity child =>
      let choice := policy path mover arity child
      endpointLawWithFuel fuel policy
        (path ++ [choice.1]) (child choice)
  | fuel + 1, policy, path, .Chance _arity child law =>
      law.bind fun choice =>
        endpointLawWithFuel fuel policy
          (path ++ [choice.1]) (child choice)

/-- Bounded compiled execution has exactly the source endpoint-subtree law.

This is an equality of finite laws after forgetting the complete target history,
not a strict isomorphism of the source and target presentations. -/
theorem stochasticHistoryLawFrom_map_endpoint
    (root : StochasticGameTree N) (policy : Policy N)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) :
    ((toExtensiveGame root).toArena.stochasticHistoryLawFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame root)
          (policyToBehavioralProfile root policy))
        current fuel).map Sigma.fst =
      endpointLawWithFuel fuel policy
        (historyPath current.2) current.1 := by
  induction fuel generalizing current with
  | zero =>
      rw [Arena.stochasticHistoryLawFrom_zero, FiniteLaw.pure_map]
      rfl
  | succ fuel ih =>
      rcases current with ⟨tree, history⟩
      cases tree with
      | Leaf payoff =>
          rw [Arena.stochasticHistoryLawFrom_succ_of_terminal
            _ _ fuel
            (toExtensiveGame_isTerminal_leaf root payoff)]
          rw [FiniteLaw.pure_map]
          rfl
      | Player mover arity child =>
          have hnonterminal :=
            toExtensiveGame_not_isTerminal_player
              root mover arity child
          rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
            _ _ fuel hnonterminal]
          change
            FiniteLaw.map Sigma.fst
                ((ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                    (toObservedChanceGame root)
                    (policyToBehavioralProfile root policy)
                    ⟨.Player mover arity child, history⟩
                    hnonterminal).bind
                  (fun action =>
                    (toExtensiveGame root).toArena.stochasticHistoryLawFrom
                      (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                        (toObservedChanceGame root)
                        (policyToBehavioralProfile root policy))
                      ⟨child action, history.snoc action⟩ fuel)) =
              endpointLawWithFuel (fuel + 1) policy
                (historyPath history) (.Player mover arity child)
          rw [policyHistoryPolicy_player
            root policy mover arity child history hnonterminal]
          let choice :=
            policy (historyPath history) mover arity child
          change
            FiniteLaw.map Sigma.fst
                ((FiniteLaw.pure choice).bind
                  (fun action =>
                    (toExtensiveGame root).toArena.stochasticHistoryLawFrom
                      (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                        (toObservedChanceGame root)
                        (policyToBehavioralProfile root policy))
                      ⟨child action, history.snoc action⟩ fuel)) =
              endpointLawWithFuel fuel policy
                (historyPath history ++ [choice.1]) (child choice)
          calc
            _ =
                FiniteLaw.map Sigma.fst
                  ((toExtensiveGame root).toArena.stochasticHistoryLawFrom
                    (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                      (toObservedChanceGame root)
                      (policyToBehavioralProfile root policy))
                    ⟨child choice, history.snoc choice⟩ fuel) :=
              congrArg (FiniteLaw.map Sigma.fst) (FiniteLaw.pure_bind choice _)
            _ = endpointLawWithFuel fuel policy
                  (historyPath (history.snoc choice)) (child choice) :=
              ih
                (current :=
                  ⟨child choice, history.snoc choice⟩)
            _ = endpointLawWithFuel fuel policy
                  (historyPath history ++ [choice.1]) (child choice) := rfl
      | Chance arity child law =>
          have hnonterminal :=
            toExtensiveGame_not_isTerminal_chance
              root arity child law
          rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
            _ _ fuel hnonterminal]
          change
            FiniteLaw.map Sigma.fst
                ((ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                    (toObservedChanceGame root)
                    (policyToBehavioralProfile root policy)
                    ⟨.Chance arity child law, history⟩
                    hnonterminal).bind
                  (fun action =>
                    (toExtensiveGame root).toArena.stochasticHistoryLawFrom
                      (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
                        (toObservedChanceGame root)
                        (policyToBehavioralProfile root policy))
                      ⟨child action, history.snoc action⟩ fuel)) =
              endpointLawWithFuel (fuel + 1) policy
                (historyPath history) (.Chance arity child law)
          rw [policyHistoryPolicy_chance
            root policy arity child law history hnonterminal]
          rw [FiniteLaw.map_bind]
          simp only [endpointLawWithFuel]
          apply congrArg (FiniteLaw.bind law)
          funext choice
          simpa using
            ih
              (current :=
                ⟨child choice, history.snoc choice⟩)

/-- Mapping bounded compiled histories to the total payoff field yields
exactly the source endpoint law mapped through the same payoff function. -/
theorem stochasticHistoryLawFrom_map_payoff
    (root : StochasticGameTree N) (policy : Policy N)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) :
    ((toExtensiveGame root).toArena.stochasticHistoryLawFrom
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
          (toObservedChanceGame root)
          (policyToBehavioralProfile root policy))
        current fuel).map
          (fun history => (toExtensiveGame root).payoff history.1) =
      (endpointLawWithFuel fuel policy
        (historyPath current.2) current.1).map statePayoff := by
  calc
    ((toExtensiveGame root).toArena.stochasticHistoryLawFrom
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            (toObservedChanceGame root)
          (policyToBehavioralProfile root policy))
          current fuel).map
        (fun history => (toExtensiveGame root).payoff history.1) =
      (((toExtensiveGame root).toArena.stochasticHistoryLawFrom
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            (toObservedChanceGame root)
            (policyToBehavioralProfile root policy))
          current fuel).map Sigma.fst).map statePayoff := by
        let executionLaw :=
          (toExtensiveGame root).toArena.stochasticHistoryLawFrom
            (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
              (toObservedChanceGame root)
              (policyToBehavioralProfile root policy))
            current fuel
        change
          executionLaw.map (statePayoff ∘ Sigma.fst) =
            (executionLaw.map Sigma.fst).map statePayoff
        exact (FiniteLaw.map_comp Sigma.fst executionLaw statePayoff).symm
    _ = (endpointLawWithFuel fuel policy
          (historyPath current.2) current.1).map statePayoff := by
      rw [stochasticHistoryLawFrom_map_endpoint
        root policy current fuel]

/-! ### Unilateral source deviations -/

namespace Policy

/-- Two source policies differ only in player `who`'s choices. -/
def IVariant (who : N) (base deviation : Policy N) : Prop :=
  ∀ path mover arity child,
    mover ≠ who →
      base path mover arity child =
        deviation path mover arity child

end Policy

/-- Translating a source unilateral deviation is the target behavioral
deviation by the translated deviator strategy. -/
theorem policyToBehavioralProfile_deviate [DecidableEq N]
    (root : StochasticGameTree N)
    (base deviation : Policy N) (who : N)
    (hvariant : Policy.IVariant who base deviation) :
    (policyToBehavioralProfile root base).deviate
        (toObservedGame root) who
        (policyToBehavioralProfile root deviation who) =
      policyToBehavioralProfile root deviation := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [ExtensiveGame.ObservedGame.BehavioralProfile.deviate,
      ExtensiveGame.ControlledObservedGame.BehavioralProfile.deviate]
  · simp only [ExtensiveGame.ObservedGame.BehavioralProfile.deviate,
      ExtensiveGame.ControlledObservedGame.BehavioralProfile.deviate,
      Function.update_of_ne hi]
    funext information
    unfold policyToBehavioralProfile
    congr 1
    rcases information.1 with
      ⟨⟨tree, history⟩, hmover, _hnonterminal⟩
    cases tree with
    | Leaf payoff =>
        simp [toExtensiveGame] at hmover
    | Player mover arity child =>
        have hmover_i : mover = i :=
          Option.some.inj hmover
        apply hvariant
        simpa [hmover_i] using hi
    | Chance arity child law =>
        simp [toExtensiveGame] at hmover

end StochasticGameTree
