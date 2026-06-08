/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# ExtensiveGame.ImperfectInformation

A finite interface for imperfect-information extensive games.

This is intentionally a lightweight structural layer.  It records vertices,
available actions, transitions, mover ownership, terminal payoffs, and
information-set labels.  Well-formedness conditions are predicates, not fields,
so examples can start small while later theorem statements can assume exactly
the conditions they need.

## Main definitions

* `FiniteImperfectGame` — finite imperfect-information extensive game data.
* `FiniteImperfectGame.subgameAt` — the same game rooted at a chosen state.
* `FiniteImperfectGame.Reachable` / `FiniteImperfectGame.IsReachable` —
  path reachability in the finite state graph.
* `SameMoverOnInfo` — nodes in one information set have the same mover.
* `SameActionsOnInfo` — nodes in one information set have the same action type.
* `NoChanceOnDecisionInfo` — information sets are only used at player nodes.
* `PureStrategy` — choices indexed by player and information set.
* `PureStrategy.actionAt` — induced action at a concrete state.
* `PureStrategy.restrictToSubgame` / `BehaviorStrategy.restrictToSubgame` —
  strategy restriction to a re-rooted subgame.
* `BehaviorStrategy` — a mixed action at each information-set query.
* `IsCompletelyMixedBehaviorStrategy` / `IsCompletelyMixedBehaviorProfile` —
  every available action has positive probability.
-/

/-- Finite imperfect-information extensive game data.

`info s = none` means the state is not in a strategic information set, typically
because it is terminal or chance-controlled.  `info s = some k` places state `s`
in information set `k`. -/
structure FiniteImperfectGame (ι U : Type*) where
  State : Type*
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  InfoSet : Type*
  [infoDecidableEq : DecidableEq InfoSet]
  Action : State → Type*
  next : (s : State) → Action s → State
  init : State
  mover : State → Option ι
  info : State → Option InfoSet
  payoff : State → ι → U

attribute [instance] FiniteImperfectGame.stateFintype
attribute [instance] FiniteImperfectGame.stateDecidableEq
attribute [instance] FiniteImperfectGame.infoDecidableEq

namespace FiniteImperfectGame

variable {ι U : Type*} (G : FiniteImperfectGame ι U)

/-- A state is terminal when it has no available actions. -/
def IsTerminal (s : G.State) : Prop := IsEmpty (G.Action s)

/-- The subgame starting at state `s`: same finite game data with a different
initial state.  Extra validity conditions, such as whether `s` is a legitimate
imperfect-information subroot, can be imposed by theorem statements using this
operation. -/
def subgameAt (s : G.State) : FiniteImperfectGame ι U :=
  { G with init := s }

/-- The initial state of `subgameAt` is the chosen root. -/
theorem subgameAt_init (s : G.State) : (G.subgameAt s).init = s := rfl

/-- Re-rooting does not change the available actions at a state. -/
theorem subgameAt_action (root s : G.State) :
    (G.subgameAt root).Action s = G.Action s := rfl

/-- Re-rooting does not change the transition function. -/
theorem subgameAt_next (root s : G.State) (a : G.Action s) :
    (G.subgameAt root).next s a = G.next s a := rfl

/-- Re-rooting does not change the mover at a state. -/
theorem subgameAt_mover (root s : G.State) :
    (G.subgameAt root).mover s = G.mover s := rfl

/-- Re-rooting does not change information-set labels. -/
theorem subgameAt_info (root s : G.State) :
    (G.subgameAt root).info s = G.info s := rfl

/-- Re-rooting does not change payoff labels. -/
theorem subgameAt_payoff (root s : G.State) (i : ι) :
    (G.subgameAt root).payoff s i = G.payoff s i := rfl

/-! ### Reachability -/

/-- `Reachable s t` means that `t` can be reached from `s` by following zero or
more actions in the finite game graph. -/
inductive Reachable : G.State → G.State → Prop where
  | refl (s : G.State) : Reachable s s
  | step {s t : G.State} (a : G.Action s) (h : Reachable (G.next s a) t) :
      Reachable s t

/-- Reachability is transitive. -/
theorem Reachable.trans {s t u : G.State}
    (h1 : G.Reachable s t) (h2 : G.Reachable t u) :
    G.Reachable s u := by
  induction h1 with
  | refl => exact h2
  | step a _ ih => exact Reachable.step a (ih h2)

/-- One transition extends reachability. -/
theorem Reachable.step' {s t : G.State}
    (h : G.Reachable s t) (a : G.Action t) :
    G.Reachable s (G.next t a) :=
  Reachable.trans G h (Reachable.step a (Reachable.refl (G := G) _))

/-- A state is reachable in the game if it is reachable from the initial state. -/
def IsReachable (s : G.State) : Prop :=
  G.Reachable G.init s

/-- The initial state is reachable. -/
theorem isReachable_init : G.IsReachable G.init :=
  Reachable.refl _

/-- Taking one action from a reachable state reaches the successor state. -/
theorem IsReachable.next {s : G.State}
    (h : G.IsReachable s) (a : G.Action s) :
    G.IsReachable (G.next s a) :=
  Reachable.step' G h a

/-- The chosen root is reachable in its re-rooted subgame. -/
theorem subgameAt_isReachable_root (root : G.State) :
    (G.subgameAt root).IsReachable root :=
  isReachable_init (G := G.subgameAt root)

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
  ∀ {s : G.State} {k : G.InfoSet}, G.info s = some k → ∃ i : ι, G.mover s = some i

/-- Basic well-formedness package for information-set reasoning. -/
def InfoWellFormed : Prop :=
  G.SameMoverOnInfo ∧ G.SameActionsOnInfo ∧ G.NoChanceOnDecisionInfo

/-- Re-rooting preserves the same-mover-on-information-set condition. -/
theorem subgameAt_sameMoverOnInfo {s : G.State} (h : G.SameMoverOnInfo) :
    (G.subgameAt s).SameMoverOnInfo := by
  intro t u k ht hu
  exact h (by simpa [subgameAt] using ht) (by simpa [subgameAt] using hu)

/-- Re-rooting preserves the same-action-types-on-information-set condition. -/
theorem subgameAt_sameActionsOnInfo {s : G.State} (h : G.SameActionsOnInfo) :
    (G.subgameAt s).SameActionsOnInfo := by
  intro t u k ht hu
  exact h (by simpa [subgameAt] using ht) (by simpa [subgameAt] using hu)

/-- Re-rooting preserves the condition that strategic information sets are not
    chance nodes. -/
theorem subgameAt_noChanceOnDecisionInfo {s : G.State}
    (h : G.NoChanceOnDecisionInfo) :
    (G.subgameAt s).NoChanceOnDecisionInfo := by
  intro t k ht
  exact h (by simpa [subgameAt] using ht)

/-- Re-rooting a finite imperfect-information game preserves the local
information-set well-formedness package. -/
theorem subgameAt_infoWellFormed {s : G.State} (h : G.InfoWellFormed) :
    (G.subgameAt s).InfoWellFormed := by
  exact ⟨G.subgameAt_sameMoverOnInfo h.1,
    G.subgameAt_sameActionsOnInfo h.2.1,
    G.subgameAt_noChanceOnDecisionInfo h.2.2⟩

/-- A pure strategy chooses one abstract action for each player and information set.

The action type is indexed by a representative state for that information set.
For a concrete state `s`, `actionAt` below specializes this choice at `s`, so
choices are constant on information sets by construction at the API boundary. -/
def PureStrategy (i : ι) : Type _ :=
  (k : G.InfoSet) → (s : G.State) → G.info s = some k → G.mover s = some i → G.Action s

/-- A pure strategy profile. -/
def PureStrategyProfile : Type _ :=
  (i : ι) → G.PureStrategy i

/-- The action prescribed at a concrete player-controlled state in an
    information set. -/
def PureStrategy.actionAt {i : ι} (σ : G.PureStrategy i) {s : G.State}
    {k : G.InfoSet} (hinfo : G.info s = some k) (hmover : G.mover s = some i) :
    G.Action s :=
  σ k s hinfo hmover

/-- If two states are in the same information set, a strategy is queried through
    the same information-set label at both states.  This is the formal
    constancy-by-indexing property; comparing concrete action values requires
    an action equivalence from `SameActionsOnInfo`. -/
theorem actionAt_same_info_label {i : ι} (σ : G.PureStrategy i)
    {s t : G.State} {k : G.InfoSet}
    (hs : G.info s = some k) (ht : G.info t = some k)
    (hms : G.mover s = some i) (hmt : G.mover t = some i) :
    PureStrategy.actionAt G σ hs hms = σ k s hs hms ∧
      PureStrategy.actionAt G σ ht hmt = σ k t ht hmt :=
  ⟨rfl, rfl⟩

/-- Restrict a pure strategy to the subgame rooted at `root`.

The state, action, mover, and information-set data are unchanged by
`subgameAt`; only the initial state changes. -/
def PureStrategy.restrictToSubgame {i : ι} (σ : G.PureStrategy i)
    (root : G.State) : (G.subgameAt root).PureStrategy i :=
  fun k s hinfo hmover =>
    σ k s (by simpa [subgameAt] using hinfo) (by simpa [subgameAt] using hmover)

/-- Restricting a pure strategy does not change the action prescribed at any
    concrete information-set query. -/
theorem PureStrategy.restrictToSubgame_actionAt {i : ι} (σ : G.PureStrategy i)
    (root : G.State) {s : G.State} {k : G.InfoSet}
    (hinfo : (G.subgameAt root).info s = some k)
    (hmover : (G.subgameAt root).mover s = some i) :
    PureStrategy.actionAt (G.subgameAt root)
        (PureStrategy.restrictToSubgame G σ root) hinfo hmover =
      PureStrategy.actionAt G σ
        (by simpa [subgameAt] using hinfo)
        (by simpa [subgameAt] using hmover) := by
  simp [PureStrategy.actionAt, PureStrategy.restrictToSubgame]

/-- Restrict a pure strategy profile to the subgame rooted at `root`. -/
def PureStrategyProfile.restrictToSubgame (σ : G.PureStrategyProfile)
    (root : G.State) : (G.subgameAt root).PureStrategyProfile :=
  fun i => PureStrategy.restrictToSubgame G (σ i) root

/-- Restricting a pure strategy profile does not change the action prescribed
    by any player at any concrete information-set query. -/
theorem PureStrategyProfile.restrictToSubgame_actionAt (σ : G.PureStrategyProfile)
    (root : G.State) (i : ι) {s : G.State} {k : G.InfoSet}
    (hinfo : (G.subgameAt root).info s = some k)
    (hmover : (G.subgameAt root).mover s = some i) :
    PureStrategy.actionAt (G.subgameAt root)
        ((PureStrategyProfile.restrictToSubgame G σ root) i) hinfo hmover =
      PureStrategy.actionAt G (σ i)
        (by simpa [subgameAt] using hinfo)
        (by simpa [subgameAt] using hmover) :=
  PureStrategy.restrictToSubgame_actionAt (G := G) (σ i) root hinfo hmover

/-! ### Behavior strategies -/

/-- A behavior strategy for player `i`: at each information-set query, choose a
    mixed action at the concrete state used for that query. This is a structural
    behavior-strategy layer; equivalences between action types inside one
    information set are supplied separately by `SameActionsOnInfo`. -/
def BehaviorStrategy (i : ι) : Type _ :=
  (k : G.InfoSet) → (s : G.State) → (hinfo : G.info s = some k) →
    (hmover : G.mover s = some i) → [Fintype (G.Action s)] →
      stdSimplex ℚ (G.Action s)

/-- A behavior-strategy profile. -/
def BehaviorProfile : Type _ :=
  (i : ι) → G.BehaviorStrategy i

/-- The mixed action prescribed at a concrete player-controlled state in an
    information set. -/
def BehaviorStrategy.mixedActionAt {i : ι} (β : G.BehaviorStrategy i)
    {s : G.State} {k : G.InfoSet} (hinfo : G.info s = some k)
    (hmover : G.mover s = some i) [Fintype (G.Action s)] :
    stdSimplex ℚ (G.Action s) :=
  β k s hinfo hmover

/-- Restrict a behavior strategy to the subgame rooted at `root`.

As for pure strategies, re-rooting changes only `init`, so the same local mixed
actions are reused in the subgame. -/
def BehaviorStrategy.restrictToSubgame {i : ι} (β : G.BehaviorStrategy i)
    (root : G.State) : (G.subgameAt root).BehaviorStrategy i :=
  fun k s hinfo hmover hfin => by
    letI : Fintype (G.Action s) := hfin
    exact β k s (by simpa [subgameAt] using hinfo)
      (by simpa [subgameAt] using hmover)

/-- Restricting a behavior strategy does not change the probability assigned
    to any concrete action at an information-set query. -/
theorem BehaviorStrategy.restrictToSubgame_mixedActionAt_apply {i : ι}
    (β : G.BehaviorStrategy i) (root : G.State) {s : G.State} {k : G.InfoSet}
    (hinfo : (G.subgameAt root).info s = some k)
    (hmover : (G.subgameAt root).mover s = some i)
    [Fintype (G.Action s)] (a : G.Action s) :
    (@BehaviorStrategy.mixedActionAt ι U (G.subgameAt root) i
        (BehaviorStrategy.restrictToSubgame G β root) s k hinfo hmover
        (by simpa [subgameAt] using (inferInstance : Fintype (G.Action s)))).val
        (by simpa [subgameAt] using a) =
      (@BehaviorStrategy.mixedActionAt ι U G i β s k
        (by simpa [subgameAt] using hinfo)
        (by simpa [subgameAt] using hmover)
        (inferInstance : Fintype (G.Action s))).val a := by
  rfl

/-- Restrict a behavior-strategy profile to the subgame rooted at `root`. -/
def BehaviorProfile.restrictToSubgame (β : G.BehaviorProfile)
    (root : G.State) : (G.subgameAt root).BehaviorProfile :=
  fun i => BehaviorStrategy.restrictToSubgame G (β i) root

/-- Restricting a behavior profile does not change the probability assigned by
    any player to any concrete action at an information-set query. -/
theorem BehaviorProfile.restrictToSubgame_mixedActionAt_apply
    (β : G.BehaviorProfile) (root : G.State) (i : ι)
    {s : G.State} {k : G.InfoSet}
    (hinfo : (G.subgameAt root).info s = some k)
    (hmover : (G.subgameAt root).mover s = some i)
    [Fintype (G.Action s)] (a : G.Action s) :
    (@BehaviorStrategy.mixedActionAt ι U (G.subgameAt root) i
        ((BehaviorProfile.restrictToSubgame G β root) i) s k hinfo hmover
        (by simpa [subgameAt] using (inferInstance : Fintype (G.Action s)))).val
        (by simpa [subgameAt] using a) =
      (@BehaviorStrategy.mixedActionAt ι U G i (β i) s k
        (by simpa [subgameAt] using hinfo)
        (by simpa [subgameAt] using hmover)
        (inferInstance : Fintype (G.Action s))).val a :=
  BehaviorStrategy.restrictToSubgame_mixedActionAt_apply
    (G := G) (β := β i) root hinfo hmover a

/-- A behavior strategy is completely mixed at every information-set query if
    every available action at that query has positive probability. This is the
    behavior-strategy part of MSZ Definition 7.6 at the structural API level. -/
def IsCompletelyMixedBehaviorStrategy {i : ι} (β : G.BehaviorStrategy i) : Prop :=
  ∀ (k : G.InfoSet) (s : G.State) (hinfo : G.info s = some k)
    (hmover : G.mover s = some i) [Fintype (G.Action s)] (a : G.Action s),
      0 < (β.mixedActionAt G hinfo hmover).val a

/-- A behavior profile is completely mixed if every player's behavior strategy
    is completely mixed. -/
def IsCompletelyMixedBehaviorProfile (β : G.BehaviorProfile) : Prop :=
  ∀ i : ι, G.IsCompletelyMixedBehaviorStrategy (β i)

/-- A completely mixed behavior profile gives a completely mixed behavior
    strategy for each player. -/
theorem IsCompletelyMixedBehaviorProfile.player {β : G.BehaviorProfile}
    (hβ : G.IsCompletelyMixedBehaviorProfile β) (i : ι) :
    G.IsCompletelyMixedBehaviorStrategy (β i) :=
  hβ i

/-- Complete mixing is preserved when a behavior strategy is restricted to a
    re-rooted subgame. -/
theorem isCompletelyMixedBehaviorStrategy_restrictToSubgame {i : ι}
    {β : G.BehaviorStrategy i} (hβ : G.IsCompletelyMixedBehaviorStrategy β)
    (root : G.State) :
    (G.subgameAt root).IsCompletelyMixedBehaviorStrategy
      (BehaviorStrategy.restrictToSubgame G β root) := by
  intro k s hinfo hmover hfin a
  letI : Fintype (G.Action s) := hfin
  exact hβ k s (by simpa [subgameAt] using hinfo)
    (by simpa [subgameAt] using hmover) a

/-- Complete mixing is preserved when a behavior profile is restricted to a
    re-rooted subgame. -/
theorem isCompletelyMixedBehaviorProfile_restrictToSubgame {β : G.BehaviorProfile}
    (hβ : G.IsCompletelyMixedBehaviorProfile β) (root : G.State) :
    (G.subgameAt root).IsCompletelyMixedBehaviorProfile
      (BehaviorProfile.restrictToSubgame G β root) := by
  intro i
  exact isCompletelyMixedBehaviorStrategy_restrictToSubgame
    (G := G) (β := β i) (IsCompletelyMixedBehaviorProfile.player (G := G) hβ i) root

/-- The uniform mixed action at a finite nonempty action set. -/
def uniformBehaviorAction {s : G.State} [Fintype (G.Action s)]
    [Nonempty (G.Action s)] : stdSimplex ℚ (G.Action s) where
  val _ := 1 / Fintype.card (G.Action s)
  property := ⟨fun _ => by positivity,
               by simp [Finset.sum_const, Finset.card_univ]⟩

/-- The uniform behavior action assigns positive probability to every action. -/
theorem uniformBehaviorAction_pos {s : G.State} [Fintype (G.Action s)]
    [Nonempty (G.Action s)] (a : G.Action s) :
    0 < (G.uniformBehaviorAction (s := s)).val a := by
  exact one_div_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := G.Action s)))

/-- Uniform behavior strategy, available when every queried information-set
    action type is nonempty. Finiteness is supplied by the behavior-strategy
    query itself. -/
def uniformBehaviorStrategy (i : ι)
    (hNonempty : ∀ (k : G.InfoSet) (s : G.State) (_hinfo : G.info s = some k)
      (_hmover : G.mover s = some i), Nonempty (G.Action s)) :
    G.BehaviorStrategy i :=
  fun k s hinfo hmover hfin => by
    letI : Fintype (G.Action s) := hfin
    letI : Nonempty (G.Action s) := hNonempty k s hinfo hmover
    exact G.uniformBehaviorAction (s := s)

/-- Uniform behavior profile. -/
def uniformBehaviorProfile
    (hNonempty : ∀ (i : ι) (k : G.InfoSet) (s : G.State)
      (_hinfo : G.info s = some k) (_hmover : G.mover s = some i),
        Nonempty (G.Action s)) :
    G.BehaviorProfile :=
  fun i => G.uniformBehaviorStrategy i (hNonempty i)

/-- The uniform behavior strategy is completely mixed. -/
theorem uniformBehaviorStrategy_isCompletelyMixed (i : ι)
    (hNonempty : ∀ (k : G.InfoSet) (s : G.State) (_hinfo : G.info s = some k)
      (_hmover : G.mover s = some i), Nonempty (G.Action s)) :
    G.IsCompletelyMixedBehaviorStrategy (G.uniformBehaviorStrategy i hNonempty) := by
  intro k s hinfo hmover hfin a
  letI : Fintype (G.Action s) := hfin
  letI : Nonempty (G.Action s) := hNonempty k s hinfo hmover
  change 0 < (G.uniformBehaviorAction (s := s)).val a
  exact G.uniformBehaviorAction_pos (s := s) a

/-- The uniform behavior profile is completely mixed. -/
theorem uniformBehaviorProfile_isCompletelyMixed
    (hNonempty : ∀ (i : ι) (k : G.InfoSet) (s : G.State)
      (_hinfo : G.info s = some k) (_hmover : G.mover s = some i),
        Nonempty (G.Action s)) :
    G.IsCompletelyMixedBehaviorProfile (G.uniformBehaviorProfile hNonempty) := by
  intro i
  exact G.uniformBehaviorStrategy_isCompletelyMixed i (hNonempty i)

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

theorem tiny_info_well_formed : tiny.InfoWellFormed := by
  refine ⟨tiny_same_mover, ?_, tiny_no_chance_on_info⟩
  intro s t k hs ht
  cases s <;> cases t <;> cases k <;> simp [tiny] at hs ht ⊢
  · exact ⟨Equiv.refl P1Action⟩
  · exact ⟨Equiv.refl P1Action⟩
  · exact ⟨Equiv.refl P1Action⟩
  · exact ⟨Equiv.refl P1Action⟩

/-- The left information-set state is reachable from the root. -/
theorem tiny_left_reachable : tiny.IsReachable State.left := by
  change tiny.Reachable State.root State.left
  exact FiniteImperfectGame.Reachable.step (G := tiny) RootAction.L
    (FiniteImperfectGame.Reachable.refl (G := tiny) State.left)

/-- Every player-1 information-set query in `tiny` has a nonempty action set. -/
theorem tinyP1_info_action_nonempty :
    ∀ (k : tiny.InfoSet) (s : tiny.State) (_hinfo : tiny.info s = some k)
      (_hmover : tiny.mover s = some Player.P1), Nonempty (tiny.Action s) := by
  intro k s hinfo hmover
  cases s <;> cases k <;> simp [tiny] at hinfo hmover ⊢
  · exact ⟨P1Action.Stop⟩
  · exact ⟨P1Action.Stop⟩

/-- A uniform behavior strategy for player 1 at the hidden-choice information
    set. -/
def tinyP1Behavior : tiny.BehaviorStrategy Player.P1 :=
  tiny.uniformBehaviorStrategy Player.P1 tinyP1_info_action_nonempty

/-- The singleton-action behavior strategy at the hidden-choice information set
    is completely mixed. -/
theorem tinyP1Behavior_completely_mixed :
    tiny.IsCompletelyMixedBehaviorStrategy tinyP1Behavior := by
  exact tiny.uniformBehaviorStrategy_isCompletelyMixed
    Player.P1 tinyP1_info_action_nonempty

/-- The subgame rooted at the left hidden-choice state. -/
def tinyLeftSubgame : FiniteImperfectGame Player ℤ :=
  tiny.subgameAt State.left

/-- The left state is the root of `tinyLeftSubgame`, hence reachable there. -/
theorem tinyLeftSubgame_left_reachable :
    tinyLeftSubgame.IsReachable State.left := by
  exact tiny.subgameAt_isReachable_root State.left

/-- The left subgame inherits the information-set well-formedness package. -/
theorem tinyLeftSubgame_info_well_formed :
    tinyLeftSubgame.InfoWellFormed := by
  exact tiny.subgameAt_infoWellFormed tiny_info_well_formed

/-- Re-rooting the tiny game at `left` does not change the hidden-choice
    information label there. -/
theorem tinyLeftSubgame_left_info :
    tinyLeftSubgame.info State.left = some Info.hiddenChoice := by
  rw [show tinyLeftSubgame.info State.left =
      tiny.info State.left from tiny.subgameAt_info State.left State.left]
  rfl

/-- Re-rooting the tiny game at `left` does not change the player at `left`. -/
theorem tinyLeftSubgame_left_mover :
    tinyLeftSubgame.mover State.left = some Player.P1 := by
  rw [show tinyLeftSubgame.mover State.left =
      tiny.mover State.left from tiny.subgameAt_mover State.left State.left]
  rfl

/-- The terminal stop state is reachable from the left subgame root. -/
theorem tinyLeftSubgame_stop_reachable :
    tinyLeftSubgame.IsReachable State.stop := by
  exact FiniteImperfectGame.IsReachable.next
    (G := tinyLeftSubgame) tinyLeftSubgame_left_reachable P1Action.Stop

/-- The terminal stop state is reachable in the original tiny game through the
    left hidden-choice state. -/
theorem tiny_stop_reachable_via_left_subgame :
    tiny.IsReachable State.stop :=
  FiniteImperfectGame.IsReachable.next
    (G := tiny) tiny_left_reachable P1Action.Stop

/-- Restrict the player-1 behavior strategy to the left subgame. -/
def tinyP1BehaviorOnLeft : tinyLeftSubgame.BehaviorStrategy Player.P1 :=
  tinyP1Behavior.restrictToSubgame tiny State.left

/-- The restricted behavior strategy remains completely mixed in the subgame. -/
theorem tinyP1BehaviorOnLeft_completely_mixed :
    tinyLeftSubgame.IsCompletelyMixedBehaviorStrategy tinyP1BehaviorOnLeft := by
  exact FiniteImperfectGame.isCompletelyMixedBehaviorStrategy_restrictToSubgame
    (G := tiny) (β := tinyP1Behavior) tinyP1Behavior_completely_mixed State.left

end Examples.ImperfectInformation
