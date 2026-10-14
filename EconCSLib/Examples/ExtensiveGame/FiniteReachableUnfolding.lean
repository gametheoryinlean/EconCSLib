/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding

/-!
# Finite reachable-unfolding regressions

These examples separate finite compact state from finite extensive form.

* `loopObserved` has one compact state but an unbounded legal history, so no
  `FiniteEFGHypotheses` certificate can exist.
* `oneStepObserved` has the infinite ambient state type `Nat`, but its
  occurrence-sensitive reachable unfolding is finite.
* two distinct root actions in `oneStepObserved` merge at endpoint `1`; the
  finite unfolding keeps the two histories separate and a terminal outcome
  may distinguish them.
-/

namespace FiniteReachableUnfolding

/-! ## Finite compact state with a cycle -/

abbrev loopArena : Arena where
  State := Unit
  Action := fun _ => Unit
  next := fun _ _ => ()

abbrev loopBase : ExtensiveGame Unit Unit :=
  ExtensiveGame.ofArena loopArena () (fun _ => some ())
    (fun _ _ => ())

abbrev loopObserved : ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation loopBase

def loopHistory : ∀ _length : ℕ,
    loopArena.History () ()
  | 0 => .nil
  | length + 1 => (loopHistory length).snoc ()

@[simp]
theorem loopHistory_length (length : ℕ) :
    (loopHistory length).length = length := by
  induction length with
  | zero =>
      rfl
  | succ length ih =>
      change (loopHistory length).length + 1 = length + 1
      rw [ih]

/-- A finite compact state type does not imply a finite EFG: the legal loop
violates every uniform history-length bound. -/
theorem loopObserved_not_finiteEFG :
    IsEmpty loopObserved.FiniteEFGHypotheses where
  false h := by
    have hterminal :=
      h.hasLengthBound
        (loopHistory h.lengthBound)
        (loopHistory_length h.lengthBound)
    exact hterminal.false ()

/-! ## Infinite ambient state with a finite reachable unfolding -/

abbrev oneStepArena : Arena where
  State := Nat
  Action := fun state =>
    if state = 0 then Bool else Empty
  next := fun _state _action => 1

abbrev oneStepBase : ExtensiveGame Unit Unit :=
  ExtensiveGame.ofArena
    oneStepArena 0
    (fun state => if state = 0 then some () else none)
    (fun _state _player => ())

abbrev oneStepObserved :
    ExtensiveGame.ObservedGame Unit Unit where
  base := oneStepBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _history _player _hmover _hnonterminal => ()
  infoAt_observe := by simp
  InfoAction := fun _ _ => Bool
  actionEquiv := by
    intro history player hmover _hnonterminal
    cases player
    have hstate : history.1 = 0 := by
      by_contra hne
      simp [oneStepBase, oneStepArena, hne] at hmover
    simpa [oneStepBase, oneStepArena, hstate] using
      (Equiv.refl Bool)

theorem oneStep_allDecisionInfoRepresented :
    oneStepObserved.AllDecisionInfoRepresented := by
  intro player information
  cases player
  cases information
  refine
    ⟨
      { history :=
          Arena.HistoryFrom.nil oneStepArena 0
        mover := by
          rfl
        decision := by
          exact ⟨false⟩
        infoAt_eq := rfl }⟩

theorem oneStep_decisionMoverCoherent :
    oneStepObserved.DecisionMoverCoherent := by
  change
    ∀ (history : oneStepArena.HistoryFrom 0) (player : Unit),
      (if history.1 = 0 then some () else none) = some player →
        Nonempty (if history.1 = 0 then Bool else Empty)
  intro history player hmover
  cases player
  by_cases hstate : history.1 = 0
  · simpa [hstate] using
      (show Nonempty Bool from ⟨false⟩)
  · simp [hstate] at hmover

theorem oneStep_hasLengthBound :
    oneStepArena.HasLengthBoundFrom (0 : Nat) 1 := by
  intro finish history hlength
  cases history with
  | nil =>
      simp at hlength
  | @snoc previous path action =>
      change IsEmpty
        (if (1 : Nat) = 0 then Bool else Empty)
      change IsEmpty Empty
      infer_instance

def oneStep_finiteEFG :
    oneStepObserved.FiniteEFGHypotheses where
  lengthBound := 1
  hasLengthBound := oneStep_hasLengthBound
  finiteAction := by
    change
      ∀ history : oneStepArena.HistoryFrom 0,
        Fintype
          (if history.1 = 0 then Bool else Empty)
    intro history
    by_cases hstate : history.1 = 0
    · simpa [hstate] using
          (show Fintype Bool from inferInstance)
    · simpa [hstate] using
        (show Fintype Empty from inferInstance)
  finiteDecisionPresentation := by
    intro player
    cases player
    let information : oneStepObserved.RepresentedInfo () :=
      oneStepObserved.representedInfoAt
        (Arena.HistoryFrom.nil oneStepArena 0)
        () rfl ⟨false⟩
    letI : Unique (oneStepObserved.RepresentedInfo ()) := {
      default := information
      uniq := fun other => by
        apply Subtype.ext
        exact Subsingleton.elim _ _ }
    exact
      ⟨⟨1, Equiv.ofUnique _ _⟩,
        fun _information => inferInstance⟩

/-- The finite unfolding is genuinely enumerable despite its infinite
ambient compact state type. -/
noncomputable example :
    Fintype oneStep_finiteEFG.toFiniteHistoryGame.State :=
  inferInstance

def leftHistory :
    oneStepArena.HistoryFrom (0 : Nat) :=
  ⟨(1 : Nat),
    (Arena.History.nil :
      oneStepArena.History (0 : Nat) (0 : Nat)).snoc false⟩

def rightHistory :
    oneStepArena.HistoryFrom (0 : Nat) :=
  ⟨(1 : Nat),
    (Arena.History.nil :
      oneStepArena.History (0 : Nat) (0 : Nat)).snoc true⟩

theorem merged_endpoint :
    leftHistory.1 = rightHistory.1 :=
  rfl

theorem distinct_histories :
    leftHistory ≠ rightHistory := by
  intro heq
  have hpath :
      (Arena.History.nil :
          oneStepArena.History (0 : Nat) (0 : Nat)).snoc false =
        (Arena.History.nil :
          oneStepArena.History (0 : Nat) (0 : Nat)).snoc true :=
    eq_of_heq (Sigma.ext_iff.mp heq).2
  cases hpath

def leftState :
    oneStep_finiteEFG.toFiniteHistoryGame.State :=
  ⟨leftHistory, by
    change 1 ≤ 1
    omega⟩

def rightState :
    oneStep_finiteEFG.toFiniteHistoryGame.State :=
  ⟨rightHistory, by
    change 1 ≤ 1
    omega⟩

/-- Occurrence-sensitive unfolding does not merge two histories merely
because their compact endpoints agree. -/
theorem distinct_unfolding_states :
    leftState ≠ rightState :=
  oneStep_finiteEFG.state_ne_of_originalHistory_ne
    distinct_histories

/-- Compare the complete one-step history, including its Boolean action. -/
local instance historyLeftDecidable (history : oneStepArena.HistoryFrom 0) :
    Decidable (history = leftHistory) := by
  rcases history with ⟨state, path⟩
  cases path with
  | nil => exact isFalse (by intro h; cases h)
  | @snoc previous path action =>
    cases path with
    | nil =>
      cases action
      · exact isTrue rfl
      · exact isFalse (by intro h; cases h)
    | snoc path previousAction => exact Empty.elim action

/-- Distinguish the two terminal occurrences by their full histories. -/
def routeTerminalOutcome :
    oneStepArena.TerminalOutcome (0 : Nat) Bool :=
  fun terminalHistory =>
    if terminalHistory.1 = leftHistory then false else true

theorem routeTerminalOutcome_left :
    routeTerminalOutcome
        ⟨leftHistory, by
          change IsEmpty
            (if (1 : Nat) = 0 then Bool else Empty)
          change IsEmpty Empty
          infer_instance⟩ =
      false := by
  classical
  simp [routeTerminalOutcome]

theorem routeTerminalOutcome_right :
    routeTerminalOutcome
        ⟨rightHistory, by
          change IsEmpty
            (if (1 : Nat) = 0 then Bool else Empty)
          change IsEmpty Empty
          infer_instance⟩ =
      true := by
  classical
  have hright : rightHistory ≠ leftHistory :=
    fun heq => distinct_histories heq.symm
  simp [routeTerminalOutcome, hright]

example :
    routeTerminalOutcome ⟨leftHistory, by exact ⟨Empty.elim⟩⟩ = false ∧
    routeTerminalOutcome ⟨rightHistory, by exact ⟨Empty.elim⟩⟩ = true := by
  native_decide

/-! ## Payoff-free preservation regressions -/

/-- Forgetting the irrelevant unit payoff produces the canonical payoff-free
presentation used by the finite preservation theorems. -/
abbrev oneStepControlled :
    ExtensiveGame.ControlledObservedGame Unit :=
  oneStepObserved.toControlledObservedGame

/-- The concrete finite certificate transports to the payoff-free carrier
without introducing a dummy objective. -/
def oneStep_controlledFinite :
    oneStepControlled.FiniteEFGHypotheses where
  lengthBound := oneStep_finiteEFG.lengthBound
  hasLengthBound := oneStep_finiteEFG.hasLengthBound
  finiteAction := oneStep_finiteEFG.finiteAction
  finiteDecisionPresentation :=
    oneStep_finiteEFG.finiteDecisionPresentation

/-- A nontrivial external root presentation selecting the initial history and
the left terminal occurrence. -/
def selectedRoots :
    oneStepControlled.ContinuationRootPresentation where
  IsRoot := fun history =>
    history =
        Arena.HistoryFrom.nil
          oneStepControlled.base.toArena
          oneStepControlled.base.init ∨
      history = leftHistory
  init_isRoot := Or.inl rfl

/-- The custom root set is preserved exactly by the canonical finite
occurrence isomorphism. -/
theorem selectedRoots_preserved :
    ExtensiveGame.ControlledObservedGame.Iso.PreservesRootPresentations
        oneStep_controlledFinite.toOriginalIso
        (oneStep_controlledFinite.pullRootPresentation
          selectedRoots)
        selectedRoots :=
  ExtensiveGame.ControlledObservedGame.FiniteEFGHypotheses.toOriginalIso_preservesRootPresentation
    oneStep_controlledFinite selectedRoots

/-- Classic recall is preserved and reflected by this finite unfolding. -/
theorem classic_recall_preserved :
    oneStep_controlledFinite.toFiniteObservedGame.PerfectRecall ↔
      oneStepControlled.PerfectRecall :=
  oneStep_controlledFinite.perfectRecall_iff

/-- Private-signal recall is preserved and reflected by this finite
unfolding. -/
theorem signal_recall_preserved :
    oneStep_controlledFinite.toFiniteObservedGame.EventClockSignalPerfectRecall ↔
      oneStepControlled.EventClockSignalPerfectRecall :=
  oneStep_controlledFinite.eventClockSignalPerfectRecall_iff

/-- Public-signal recall is preserved and reflected by this finite
unfolding. -/
theorem public_recall_preserved :
    ExtensiveGame.ControlledObservedGame.HasEventClockPublicPerfectRecall
        oneStep_controlledFinite.toFiniteObservedGame ↔
      oneStepControlled.HasEventClockPublicPerfectRecall :=
  oneStep_controlledFinite.eventClockPublicPerfectRecall_iff

/-- Every discrete chance law is pulled back pointwise at the represented
original occurrence. This regression instantiates the generic contract at the
infinite-ambient one-step example. -/
theorem discrete_chance_preserved
    (chanceKernel :
      (history : oneStepControlled.base.History) →
        oneStepControlled.base.isChanceState history.1 →
          FiniteLaw (oneStepControlled.base.Action history.1))
    (history :
      oneStep_controlledFinite.toFiniteObservedGame.base.History)
    (hchance :
      ControlledGame.isChanceState
        oneStep_controlledFinite.toFiniteObservedGame.base
        history.1) :
    oneStep_controlledFinite.pullDiscreteChanceKernel
        chanceKernel history hchance =
      chanceKernel
        (oneStep_controlledFinite.originalHistory history.1)
        hchance :=
  oneStep_controlledFinite.pullDiscreteChanceKernel_eq
    chanceKernel history hchance

end FiniteReachableUnfolding
