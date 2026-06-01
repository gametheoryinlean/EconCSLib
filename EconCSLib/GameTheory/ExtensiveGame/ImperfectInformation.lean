/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation

A finite interface for imperfect-information extensive games.

This is intentionally a lightweight structural layer.  It records vertices,
available actions, transitions, mover ownership, terminal payoffs, and
information-set labels.  Well-formedness conditions are predicates, not fields,
so examples can start small while later theorem statements can assume exactly
the conditions they need.

## Main definitions

* `FiniteImperfectGame` — finite imperfect-information extensive game data.
* `FiniteImperfectGame.subgameAt` — the same game rooted at a chosen state.
* `SameMoverOnInfo` — nodes in one information set have the same mover.
* `SameActionsOnInfo` — nodes in one information set have the same action type.
* `NoChanceOnDecisionInfo` — information sets are only used at player nodes.
* `PureStrategy` — choices indexed by player and information set.
* `PureStrategy.actionAt` — induced action at a concrete state.
-/

/-- Finite imperfect-information extensive game data.

`info s = none` means the state is not in a strategic information set, typically
because it is terminal or chance-controlled.  `info s = some k` places state `s`
in information set `k`. -/
structure FiniteImperfectGame (N U : Type*) where
  State : Type*
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  InfoSet : Type*
  [infoDecidableEq : DecidableEq InfoSet]
  Action : State → Type*
  next : (s : State) → Action s → State
  init : State
  mover : State → Option N
  info : State → Option InfoSet
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

/-- Strategic information sets are attached only to player-controlled states. -/
def NoChanceOnDecisionInfo : Prop :=
  ∀ {s : G.State} {k : G.InfoSet}, G.info s = some k → ∃ i : N, G.mover s = some i

/-- Basic well-formedness package for information-set reasoning. -/
def InfoWellFormed : Prop :=
  G.SameMoverOnInfo ∧ G.SameActionsOnInfo ∧ G.NoChanceOnDecisionInfo

/-- Re-rooting a finite imperfect-information game preserves the local
information-set well-formedness package. -/
theorem subgameAt_infoWellFormed {s : G.State} (h : G.InfoWellFormed) :
    (G.subgameAt s).InfoWellFormed := by
  simpa [subgameAt, InfoWellFormed, SameMoverOnInfo, SameActionsOnInfo,
    NoChanceOnDecisionInfo] using h

/-- A pure strategy chooses one abstract action for each player and information set.

The action type is indexed by a representative state for that information set.
For a concrete state `s`, `actionAt` below specializes this choice at `s`, so
choices are constant on information sets by construction at the API boundary. -/
def PureStrategy (i : N) : Type _ :=
  (k : G.InfoSet) → (s : G.State) → G.info s = some k → G.mover s = some i → G.Action s

/-- A pure strategy profile. -/
def PureStrategyProfile : Type _ :=
  (i : N) → G.PureStrategy i

/-- The action prescribed at a concrete player-controlled state in an
    information set. -/
def PureStrategy.actionAt {i : N} (σ : G.PureStrategy i) {s : G.State}
    {k : G.InfoSet} (hinfo : G.info s = some k) (hmover : G.mover s = some i) :
    G.Action s :=
  σ k s hinfo hmover

/-- If two states are in the same information set, a strategy is queried through
    the same information-set label at both states.  This is the formal
    constancy-by-indexing property; comparing concrete action values requires
    an action equivalence from `SameActionsOnInfo`. -/
theorem actionAt_same_info_label {i : N} (σ : G.PureStrategy i)
    {s t : G.State} {k : G.InfoSet}
    (hs : G.info s = some k) (ht : G.info t = some k)
    (hms : G.mover s = some i) (hmt : G.mover t = some i) :
    PureStrategy.actionAt G σ hs hms = σ k s hs hms ∧
      PureStrategy.actionAt G σ ht hmt = σ k t ht hmt :=
  ⟨rfl, rfl⟩

end FiniteImperfectGame

/-! ### Small example -/

namespace Examples.ImperfectInformation

inductive Player | P0 | P1
  deriving DecidableEq

inductive State | root | left | right | stop
  deriving DecidableEq

instance : Fintype State :=
  ⟨⟨[State.root, State.left, State.right, State.stop], by decide⟩,
    fun x => by cases x <;> decide⟩

inductive Info | hiddenChoice
  deriving DecidableEq

inductive RootAction | L | R
  deriving DecidableEq

inductive P1Action | Stop
  deriving DecidableEq

/-- A tiny imperfect-information game where player 1 cannot distinguish two
    singleton-action states reached after player 0's root choice. -/
def tiny : FiniteImperfectGame Player ℤ where
  State := State
  InfoSet := Info
  Action
    | .root => RootAction
    | .left => P1Action
    | .right => P1Action
    | .stop => PEmpty
  next
    | .root, RootAction.L => .left
    | .root, RootAction.R => .right
    | .left, P1Action.Stop => .stop
    | .right, P1Action.Stop => .stop
  init := .root
  mover
    | .root => some .P0
    | .left => some .P1
    | .right => some .P1
    | .stop => none
  info
    | .left => some .hiddenChoice
    | .right => some .hiddenChoice
    | _ => none
  payoff _ _ := 0

theorem tiny_same_mover : tiny.SameMoverOnInfo := by
  intro s t k hs ht
  cases s <;> cases t <;> cases k <;> simp [tiny] at hs ht ⊢

theorem tiny_no_chance_on_info : tiny.NoChanceOnDecisionInfo := by
  intro s k hs
  cases s <;> cases k <;> simp [tiny] at hs ⊢

end Examples.ImperfectInformation
