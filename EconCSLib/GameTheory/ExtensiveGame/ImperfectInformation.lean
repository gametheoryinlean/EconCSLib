/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation

A finite-state interface for imperfect-information extensive games.

This is intentionally a lightweight structural layer. It records vertices,
available actions, transitions, mover ownership, terminal payoffs,
information-set labels, an abstract action type for every information set, and
explicit equivalences to concrete legal actions. Mover and decision-node
well-formedness conditions remain predicates so theorem statements can assume
exactly the conditions they need.

Only the state carrier is structurally finite. The interface does not itself
assert acyclicity, termination, reachability of every state, or finiteness of
unused information/action carriers; results needing those properties must
state them separately.

## Main definitions

* `FiniteImperfectGame` — compact finite-state imperfect-information game data.
* `FiniteImperfectGame.subgameAt` — the same game rooted at a chosen state.
* `SameMoverOnInfo` — nodes in one information set have the same mover.
* `SameActionsOnInfo` — nodes in one information set have the same action type.
* `NoChanceOnDecisionInfo` — information sets are only used at player nodes.
* `PlayerInfoSet` — information sets witnessed for one player.
* `PureStrategy` — abstract choices indexed only by that player's information
  sets.
* `PureStrategy.actionAt` — induced action at a concrete state.
-/

/-- Compact finite-state imperfect-information extensive game data.

`info s = none` means the state is not in a strategic information set, typically
because it is terminal or chance-controlled.  `info s = some k` places state `s`
in information set `k`.

The structure name is historical: only `State` is required to be finite.
Termination, acyclicity, and any additional finiteness assumptions are
deliberately theorem-local. -/
structure FiniteImperfectGame (N U : Type*) where
  State : Type*
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  InfoSet : Type*
  [infoDecidableEq : DecidableEq InfoSet]
  /-- One abstract action type for each strategic information set. -/
  InfoAction : InfoSet → Type*
  Action : State → Type*
  next : (s : State) → Action s → State
  init : State
  mover : State → Option N
  info : State → Option InfoSet
  /-- Concrete legal actions at a labeled node are coherently represented by
  the abstract actions of that information set. -/
  actionEquiv :
    (s : State) → (k : InfoSet) → info s = some k →
      InfoAction k ≃ Action s
  payoff : State → N → U

attribute [instance] FiniteImperfectGame.stateFintype
attribute [instance] FiniteImperfectGame.stateDecidableEq
attribute [instance] FiniteImperfectGame.infoDecidableEq

namespace FiniteImperfectGame

variable {N U : Type*} (G : FiniteImperfectGame N U)

/-- A state is terminal when it has no available actions. -/
def IsTerminal (s : G.State) : Prop := IsEmpty (G.Action s)

/-- The subgame starting at state `s`: same finite game data with a different
initial state.  Extra validity conditions, such as whether `s` is a legitimate
imperfect-information subroot, can be imposed by theorem statements using this
operation. -/
def subgameAt (s : G.State) : FiniteImperfectGame N U :=
  { G with init := s }

/-- The initial state of `subgameAt` is the chosen root. -/
theorem subgameAt_init (s : G.State) : (G.subgameAt s).init = s := rfl

/-- States in the same information set have the same mover. -/
def SameMoverOnInfo : Prop :=
  ∀ {s t : G.State} {k : G.InfoSet},
    G.info s = some k → G.info t = some k → G.mover s = G.mover t

/-- States in the same information set expose equivalent action types. -/
def SameActionsOnInfo : Prop :=
  ∀ {s t : G.State} {k : G.InfoSet},
    G.info s = some k → G.info t = some k → Nonempty (G.Action s ≃ G.Action t)

/-- Explicit abstract-to-concrete action equivalences imply action-type
coherence at every information set. -/
theorem sameActionsOnInfo : G.SameActionsOnInfo := by
  intro s t k hs ht
  exact
    ⟨(G.actionEquiv s k hs).symm.trans
      (G.actionEquiv t k ht)⟩

/-- Strategic information sets are attached only to player-controlled states. -/
def NoChanceOnDecisionInfo : Prop :=
  ∀ {s : G.State} {k : G.InfoSet}, G.info s = some k → ∃ i : N, G.mover s = some i

/-- Basic well-formedness package for information-set reasoning. -/
def InfoWellFormed : Prop :=
  G.SameMoverOnInfo ∧ G.NoChanceOnDecisionInfo

/-- Re-rooting a finite-state imperfect-information game preserves the local
information-set well-formedness package. -/
theorem subgameAt_infoWellFormed {s : G.State} (h : G.InfoWellFormed) :
    (G.subgameAt s).InfoWellFormed := by
  simpa [subgameAt, InfoWellFormed, SameMoverOnInfo,
    NoChanceOnDecisionInfo] using h

/-- An information set witnessed at a decision of player `i`. -/
def PlayerInfoSet (i : N) :=
  { k : G.InfoSet //
    ∃ s : G.State,
      G.info s = some k ∧ G.mover s = some i }

/-- A pure strategy chooses one abstract action at each information set at
which player `i` can move.

The domain contains only information sets witnessed for that player. Most
importantly, the strategy cannot inspect a concrete state after receiving the
information-set label. -/
def PureStrategy (i : N) : Type _ :=
  (k : G.PlayerInfoSet i) → G.InfoAction k.1

/-- A pure strategy profile. -/
def PureStrategyProfile : Type _ :=
  (i : N) → G.PureStrategy i

/-- The action prescribed at a concrete player-controlled state in an
    information set. -/
def PureStrategy.actionAt {i : N} (σ : G.PureStrategy i) {s : G.State}
    {k : G.InfoSet} (hinfo : G.info s = some k) (hmover : G.mover s = some i) :
    G.Action s :=
  G.actionEquiv s k hinfo
    (σ ⟨k, ⟨s, hinfo, hmover⟩⟩)

/-- Actions prescribed at two nodes in the same information set become equal
after transporting them back to that information set's abstract action
type. This is the actual information-consistency property. -/
theorem actionAt_same_info {i : N} (σ : G.PureStrategy i)
    {s t : G.State} {k : G.InfoSet}
    (hs : G.info s = some k) (ht : G.info t = some k)
    (hms : G.mover s = some i) (hmt : G.mover t = some i) :
    (G.actionEquiv s k hs).symm
        (PureStrategy.actionAt G σ hs hms) =
      (G.actionEquiv t k ht).symm
        (PureStrategy.actionAt G σ ht hmt) := by
  simp only [PureStrategy.actionAt, Equiv.symm_apply_apply]

end FiniteImperfectGame
