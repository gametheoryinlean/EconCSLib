/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization

/-!
# Strict clock-reset boundary for measurable-kernel restarts

This raw measurable-kernel arena has a time-dependent event policy. At the
second decision state the policy selects `false` at event time zero and
`true` at event time one.

The same state can therefore be presented in two operational ways:

* as coordinate zero of a fresh-clock restart;
* as coordinate one of the original absolute event prefix.

The resulting action laws are distinct Dirac measures. This is a strict
regression showing why `freshRestartStatePathMeasure` and the associated Nash
predicates are explicitly qualified: without a clock/prefix compatibility
assumption, a restart that resets time is not standard continuation
semantics. It also proves that this policy cannot factor through any
fresh-restart-invariant measurable history statistic and common action
kernel. In contrast, a stationary comparison policy factors through the
non-invariant pair of absolute clock and latest state because its action law
ignores the clock; this separates statistic equality from the weaker
behavioral equality actually needed.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.MeasurableKernelFreshRestartClockBoundary

open MeasurableKernelArena

/-- Two decision states followed by one of two terminal states. -/
inductive Node
  | root
  | second
  | terminalFalse
  | terminalTrue
  deriving DecidableEq, Fintype

/-- Both decision states have Boolean actions. -/
def nodeAction : Node → Type
  | .root => Bool
  | .second => Bool
  | .terminalFalse => Empty
  | .terminalTrue => Empty

/-- The root always advances to the second state. At the second state the
Boolean action selects the terminal label. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .root, _ => .second
  | .second, false => .terminalFalse
  | .second, true => .terminalTrue
  | .terminalFalse, action => nomatch action
  | .terminalTrue, action => nomatch action

/-- Discrete deterministic kernel arena. -/
def discreteArena : KernelArena where
  State := Node
  Action := nodeAction
  next := fun state action =>
    FiniteLaw.pure (nodeNext state action)

/-- Analytic top-measurable embedding of the finite arena. -/
noncomputable abbrev arena : MeasurableKernelArena :=
  discreteArena.toMeasurable

/-- Every legal dependent action bundle comes from one of the two Boolean
decision fibers. -/
def decodeActionBundle :
    Bool ⊕ Bool → arena.ActionBundle
  | .inl action => ⟨.root, action⟩
  | .inr action => ⟨.second, action⟩

theorem decodeActionBundle_surjective :
    Function.Surjective decodeActionBundle := by
  rintro ⟨state, action⟩
  cases state with
  | root => exact ⟨.inl action, rfl⟩
  | second => exact ⟨.inr action, rfl⟩
  | terminalFalse => exact Empty.elim action
  | terminalTrue => exact Empty.elim action

local instance actionBundleCountable :
    Countable arena.ActionBundle :=
  decodeActionBundle_surjective.countable

/-- Countable code for state/action events. -/
def decodePathEvent :
    Node × (Unit ⊕ (Bool ⊕ Bool)) →
      arena.PathEvent
  | (state, .inl _) =>
      (state, .inl ())
  | (state, .inr actionCode) =>
      (state, .inr (decodeActionBundle actionCode))

theorem decodePathEvent_surjective :
    Function.Surjective decodePathEvent := by
  rintro ⟨state, incoming⟩
  cases incoming with
  | inl marker =>
      cases marker
      exact ⟨(state, .inl ()), rfl⟩
  | inr bundle =>
      obtain ⟨actionCode, rfl⟩ :=
        decodeActionBundle_surjective bundle
      exact ⟨(state, .inr actionCode), rfl⟩

local instance pathEventCountable :
    Countable arena.PathEvent :=
  decodePathEvent_surjective.countable

local instance actionBundleMeasurableSingletonClass :
    MeasurableSingletonClass arena.ActionBundle where
  measurableSet_singleton := by
    intro _
    exact MeasurableSpace.measurableSet_top

local instance stateMeasurableSingletonClass :
    MeasurableSingletonClass arena.State where
  measurableSet_singleton := by
    intro _
    exact MeasurableSpace.measurableSet_top

local instance incomingMeasurableSingletonClass :
    MeasurableSingletonClass
      (Unit ⊕ arena.ActionBundle) where
  measurableSet_singleton := by
    intro incoming
    cases incoming with
    | inl marker =>
        have heq :
            ({Sum.inl marker} :
              Set (Unit ⊕ arena.ActionBundle)) =
              Sum.inl '' ({marker} : Set Unit) := by
          ext value
          simp
        rw [heq]
        exact
          (measurableSet_singleton marker).inl_image
    | inr bundle =>
        have heq :
            ({Sum.inr bundle} :
              Set (Unit ⊕ arena.ActionBundle)) =
              Sum.inr '' ({bundle} :
                Set arena.ActionBundle) := by
          ext value
          simp
        rw [heq]
        exact
          (measurableSet_singleton bundle).inr_image

local instance pathEventMeasurableSingletonClass :
    MeasurableSingletonClass arena.PathEvent := by
  infer_instance

/-- Terminal states of the analytic arena form a measurable set. -/
theorem terminalSet_measurable :
    MeasurableSet arena.terminalSet := by
  exact MeasurableSpace.measurableSet_top

/-- The time-dependent action bundle selected at a prefix.

At `second`, time zero selects `false` and every positive time selects
`true`. Values at terminal prefixes are irrelevant because the policy kills
their action mass. -/
def selectedBundle
    (time : ℕ)
    (events : arena.EventPrefix time) :
    arena.ActionBundle :=
  match ((events ⟨time, Finset.mem_Iic.mpr le_rfl⟩).1 : Node) with
  | .root => ⟨.root, false⟩
  | .second =>
      ⟨.second, decide (0 < time)⟩
  | .terminalFalse => ⟨.root, false⟩
  | .terminalTrue => ⟨.root, false⟩

/-- Time-dependent deterministic policy, with zero action mass at terminal
prefixes. -/
noncomputable def policy :
    arena.EventHistoryActionPolicy := by
  classical
  exact
    { kernel := fun time =>
        Kernel.piecewise
          (arena.measurableSet_eventPrefixTerminalSet
            terminalSet_measurable time)
          0
          (Kernel.deterministic
            (selectedBundle time)
            (measurable_of_countable _))
      terminal_zero := by
        intro time events hterminal
        rw [Kernel.piecewise_apply, if_pos]
        · rfl
        · exact hterminal
      nonterminal_isProbability := by
        intro time events hnonterminal
        rw [Kernel.piecewise_apply, if_neg]
        · rw [Kernel.deterministic_apply]
          infer_instance
        · exact hnonterminal
      legal := by
        intro time events hnonterminal
        rw [Kernel.piecewise_apply, if_neg]
        · rw [Kernel.deterministic_apply]
          apply
            (ae_dirac_iff
              (arena.measurableSet_actionFiber _)).2
          change (selectedBundle time events).1 =
            latestEventState time events
          unfold selectedBundle
          split <;> rename_i hstate
          all_goals change latestEventState time events = _ at hstate
          · exact hstate.symm
          · exact hstate.symm
          · exact (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
          · exact (hnonterminal (by
              rw [hstate]
              change IsEmpty Empty
              exact ⟨Empty.elim⟩)).elim
        · exact hnonterminal
        }

/-- A stationary discrete policy choosing `false` at both decision states.
-/
def stationaryDiscretePolicy :
    discreteArena.Policy :=
  fun state hnonterminal =>
    match state with
    | .root => FiniteLaw.pure false
    | .second => FiniteLaw.pure false
    | .terminalFalse =>
        (hnonterminal (by
          change IsEmpty Empty
          infer_instance)).elim
    | .terminalTrue =>
        (hnonterminal (by
          change IsEmpty Empty
          infer_instance)).elim

/-- Analytic stationary state-Markov version of
`stationaryDiscretePolicy`. -/
noncomputable def stationaryPolicy :
    arena.ActionPolicy :=
  stationaryDiscretePolicy.toMeasurable

/-- Complete-event-history embedding of the stationary comparison policy.
-/
noncomputable def stationaryEventPolicy :
    arena.EventHistoryActionPolicy :=
  stationaryPolicy.toHistoryActionPolicy.toEventHistoryActionPolicy

/-- Prefix of length zero obtained by starting fresh at the second state. -/
def freshSecondPrefix :
    arena.EventPrefix 0 :=
  fun _ => (.second, Sum.inl ())

/-- A valid length-one absolute prefix from `root` to `second`, recording the
root action occurrence. -/
def absoluteSecondPrefix :
    arena.EventPrefix 1 :=
  fun index =>
    if index.1 = 0 then
      (.root, Sum.inl ())
    else
      (.second, .inr (⟨.root, false⟩ : arena.ActionBundle))

@[simp]
theorem latestEventState_freshSecondPrefix :
    latestEventState 0 freshSecondPrefix = .second :=
  rfl

@[simp]
theorem latestEventState_absoluteSecondPrefix :
    latestEventState 1 absoluteSecondPrefix = .second := by
  rfl

-- Runtime regression: the same state at fresh and absolute times selects different actions.
example :
    (fun fresh retained : Bool => fresh = false ∧ retained = true)
      (selectedBundle 0 freshSecondPrefix).2
      (selectedBundle 1 absoluteSecondPrefix).2 := by
  native_decide

/-- The fresh second-state prefix is canonically rooted at the latest state
of the retained absolute prefix. -/
theorem freshSecondPrefix_rooted_at_absoluteSecondState :
    IsInitialEventRootedPrefix
      (latestEventState 1 absoluteSecondPrefix)
      0 freshSecondPrefix := by
  rw [latestEventState_absoluteSecondPrefix]
  unfold IsInitialEventRootedPrefix
  funext time
  have htime : time.1 = 0 :=
    Nat.eq_zero_of_le_zero
      (Finset.mem_Iic.mp time.2)
  simp [
    setInitialPrefix,
    initialEvent,
    freshSecondPrefix,
    htime]

/-- The clock-and-latest-state statistic is not literally restart invariant:
the same second state is tagged by absolute time one and fresh time zero.
-/
theorem not_clockAndLatestState_freshRestartInvariant :
    ¬ EventHistoryStatistic.IsFreshRestartInvariant
        (EventHistoryStatistic.clockAndLatestState arena) := by
  intro hinvariant
  have hvalue :=
    hinvariant
      1 absoluteSecondPrefix 0 freshSecondPrefix
      freshSecondPrefix_rooted_at_absoluteSecondState
  have hclock :=
    congrArg Prod.fst hvalue
  exact Nat.one_ne_zero hclock

/-- The stationary comparison policy factors through clock and latest state,
even though its common action law ignores the clock coordinate.
-/
theorem stationaryEventPolicy_factorsThroughClockAndLatestState :
    stationaryEventPolicy.FactorsThroughStatistic
      (EventHistoryStatistic.clockAndLatestState arena)
      (EventHistoryStatistic.actionLawIgnoringClock
        stationaryPolicy.kernel) := by
  simpa [stationaryEventPolicy] using
    ActionPolicy.toEventHistoryActionPolicy_factorsThroughClockAndLatestState
      stationaryPolicy

/-- The clock-ignoring action law is restart invariant even though the
clock-and-state statistic itself is not.
-/
theorem stationaryClockActionLaw_freshRestartInvariant :
    EventHistoryStatistic.IsFreshRestartActionLawInvariant
      (EventHistoryStatistic.clockAndLatestState arena)
      (EventHistoryStatistic.actionLawIgnoringClock
        stationaryPolicy.kernel) :=
  EventHistoryStatistic.clockAndLatestState_actionLawIgnoringClock_isFreshRestartInvariant
    stationaryPolicy.kernel

/-- The generalized action-law invariant constructor proves compatibility
through a statistic that is formally not value-invariant.
-/
theorem stationaryEventPolicy_freshRestartRootedActionKernelCompatible :
    EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
      stationaryEventPolicy :=
  EventHistoryActionPolicy.FactorsThroughStatistic.freshRestartRootedActionKernelCompatible_of_actionLawInvariant
    stationaryEventPolicy_factorsThroughClockAndLatestState
    stationaryClockActionLaw_freshRestartInvariant

/-- Resetting the event clock makes the policy choose `false` at the second
state. -/
theorem policy_fresh_second :
    policy.kernel 0 freshSecondPrefix =
      Measure.dirac
        (⟨.second, false⟩ : arena.ActionBundle) := by
  classical
  rw [policy, Kernel.piecewise_apply, if_neg]
  · rw [Kernel.deterministic_apply]
    rfl
  · change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false

/-- Retaining the absolute event clock makes the same policy choose `true` at
the second state. -/
theorem policy_absolute_second :
    policy.kernel 1 absoluteSecondPrefix =
      Measure.dirac
        (⟨.second, true⟩ : arena.ActionBundle) := by
  classical
  rw [policy, Kernel.piecewise_apply, if_neg]
  · rw [Kernel.deterministic_apply]
    rfl
  · change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false

/-- The fresh-clock and absolute-clock action laws at the same latest state
are genuinely different. -/
theorem fresh_action_law_ne_absolute_action_law :
    policy.kernel 0 freshSecondPrefix ≠
      policy.kernel 1 absoluteSecondPrefix := by
  rw [policy_fresh_second, policy_absolute_second]
  intro heq
  have hvalue :=
    congrArg
      (fun measure =>
        measure
          ({(⟨Node.second, false⟩ :
              arena.ActionBundle)}))
      heq
  have hfalseTrue :
      (⟨Node.second, false⟩ : arena.ActionBundle) ≠
        ⟨Node.second, true⟩ := by
    intro hbundle
    have haction := Sigma.mk.inj_iff.mp hbundle
    exact Bool.false_ne_true (eq_of_heq haction.2)
  change
    (Measure.dirac
      (⟨Node.second, false⟩ : arena.ActionBundle))
        {(⟨Node.second, false⟩ : arena.ActionBundle)} =
      (Measure.dirac
        (⟨Node.second, true⟩ : arena.ActionBundle))
          {(⟨Node.second, false⟩ : arena.ActionBundle)}
    at hvalue
  have hnotmem :
      (⟨Node.second, true⟩ : arena.ActionBundle) ∉
        ({(⟨Node.second, false⟩ :
            arena.ActionBundle)} :
          Set arena.ActionBundle) := by
    simpa only [Set.mem_singleton_iff] using hfalseTrue.symm
  rw [
    Measure.dirac_apply_of_mem (Set.mem_singleton _)]
      at hvalue
  have hzero :
      (Measure.dirac
        (⟨Node.second, true⟩ : arena.ActionBundle))
          ({(⟨Node.second, false⟩ :
              arena.ActionBundle)} :
            Set arena.ActionBundle) =
        0 := by
    simp [hnotmem]
  rw [hzero] at hvalue
  exact one_ne_zero hvalue

/-- The fresh-clock primitive next-event law records the `false` action. -/
theorem pathStepKernel_fresh_second_map_action :
    (policy.pathStepKernel
        terminalSet_measurable 0 freshSecondPrefix).map
        PathEvent.action =
      Measure.dirac
        (.inr
          (⟨.second, false⟩ :
            arena.ActionBundle)) := by
  have hnonterminal :
      ¬ IsEmpty
        (arena.Action
          (latestEventState 0 freshSecondPrefix)) := by
    change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false
  rw [
    EventHistoryActionPolicy.pathStepKernel_apply_nonterminal
      policy terminalSet_measurable 0
      freshSecondPrefix hnonterminal]
  change
    (policy.actionStepKernel 0 freshSecondPrefix).map
        PathEvent.action =
      Measure.dirac
        (.inr
          (⟨.second, false⟩ :
            arena.ActionBundle))
  rw [
    ← Kernel.map_apply _
      PathEvent.measurable_action,
    EventHistoryActionPolicy.actionStepKernel_map_action,
    Kernel.map_apply _ measurable_inr,
    policy_fresh_second,
    Measure.map_dirac' measurable_inr]

/-- The absolute-clock primitive next-event law records the `true` action.
-/
theorem pathStepKernel_absolute_second_map_action :
    (policy.pathStepKernel
        terminalSet_measurable 1 absoluteSecondPrefix).map
        PathEvent.action =
      Measure.dirac
        (.inr
          (⟨.second, true⟩ :
            arena.ActionBundle)) := by
  have hnonterminal :
      ¬ IsEmpty
        (arena.Action
          (latestEventState 1 absoluteSecondPrefix)) := by
    change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false
  rw [
    EventHistoryActionPolicy.pathStepKernel_apply_nonterminal
      policy terminalSet_measurable 1
      absoluteSecondPrefix hnonterminal]
  change
    (policy.actionStepKernel 1 absoluteSecondPrefix).map
        PathEvent.action =
      Measure.dirac
        (.inr
          (⟨.second, true⟩ :
            arena.ActionBundle))
  rw [
    ← Kernel.map_apply _
      PathEvent.measurable_action,
    EventHistoryActionPolicy.actionStepKernel_map_action,
    Kernel.map_apply _ measurable_inr,
    policy_absolute_second,
    Measure.map_dirac' measurable_inr]

/-- The primitive next-event kernels already distinguish the fresh and
absolute clocks at the retained second-state prefix. -/
theorem pathStepKernel_absolute_second_ne_fresh_second :
    policy.pathStepKernel
        terminalSet_measurable 1 absoluteSecondPrefix ≠
      policy.pathStepKernel
        terminalSet_measurable 0 freshSecondPrefix := by
  intro hequal
  have haction :=
    congrArg
      (fun measure =>
        measure.map PathEvent.action)
      hequal
  dsimp only at haction
  rw [
    pathStepKernel_absolute_second_map_action,
    pathStepKernel_fresh_second_map_action]
      at haction
  have hpoint :
      (Sum.inr
          (⟨Node.second, true⟩ :
            arena.ActionBundle) :
        Unit ⊕ arena.ActionBundle) ≠
      Sum.inr
          (⟨Node.second, false⟩ :
            arena.ActionBundle) := by
    simp
  exact (dirac_ne_dirac hpoint) haction

/-- The action actually recorded at the first step of the fresh-clock tail is
`false`. This is a statement about the generated path law, rather than only
about the policy kernel before execution. -/
theorem fresh_restart_next_recorded_action_law :
    (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 0 freshSecondPrefix).map
        (fun path => (path 1).action) =
      Measure.dirac
        (.inr
          (⟨.second, false⟩ :
            arena.ActionBundle)) := by
  have hnonterminal :
      ¬ IsEmpty
        (arena.Action
          (latestEventState 0 freshSecondPrefix)) := by
    change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false
  rw [
    policy.tailEventPathMeasureFromPrefix_coordinate_one_action
      terminalSet_measurable 0 freshSecondPrefix hnonterminal,
    policy_fresh_second,
    Measure.map_dirac' measurable_inr]

/-- The action actually recorded at the first step of the absolute-prefix
continuation tail is `true`. -/
theorem absolute_continuation_next_recorded_action_law :
    (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 1 absoluteSecondPrefix).map
        (fun path => (path 1).action) =
      Measure.dirac
        (.inr
          (⟨.second, true⟩ :
            arena.ActionBundle)) := by
  have hnonterminal :
      ¬ IsEmpty
        (arena.Action
          (latestEventState 1 absoluteSecondPrefix)) := by
    change ¬ IsEmpty Bool
    intro hempty
    exact hempty.false false
  rw [
    policy.tailEventPathMeasureFromPrefix_coordinate_one_action
      terminalSet_measurable 1 absoluteSecondPrefix hnonterminal,
    policy_absolute_second,
    Measure.map_dirac' measurable_inr]

/-- Resetting the clock and retaining the absolute prefix produce genuinely
different future event-path probability measures from the same latest
state. -/
theorem fresh_restart_tail_law_ne_absolute_continuation_tail_law :
    policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 0 freshSecondPrefix ≠
      policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hequal
  have hrecorded :=
    congrArg
      (fun measure =>
        measure.map
          (fun path => (path 1).action))
      hequal
  change
    (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 0 freshSecondPrefix).map
        (fun path => (path 1).action) =
      (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 1 absoluteSecondPrefix).map
        (fun path => (path 1).action)
    at hrecorded
  rw [
    fresh_restart_next_recorded_action_law,
    absolute_continuation_next_recorded_action_law]
      at hrecorded
  have hpoint :
      (Sum.inr
          (⟨Node.second, false⟩ :
            arena.ActionBundle) :
        Unit ⊕ arena.ActionBundle) ≠
      Sum.inr
          (⟨Node.second, true⟩ :
            arena.ActionBundle) := by
    simp
  exact (dirac_ne_dirac hpoint) hrecorded

/-- Erasing only the absolute continuation's coordinate-zero incoming-action
marker does not repair a genuine future clock mismatch. -/
theorem fresh_restart_tail_law_ne_normalized_absolute_continuation_tail_law :
    policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 0 freshSecondPrefix ≠
      (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 1 absoluteSecondPrefix).map
          MeasurableKernelArena.freshenInitialEvent := by
  intro hequal
  have hrecorded :=
    congrArg
      (fun measure =>
        measure.map
          (fun path => (path 1).action))
      hequal
  change
    (policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 0 freshSecondPrefix).map
        (fun path => (path 1).action) =
      ((policy.tailEventPathMeasureFromPrefix
        terminalSet_measurable 1 absoluteSecondPrefix).map
          MeasurableKernelArena.freshenInitialEvent).map
            (fun path => (path 1).action)
    at hrecorded
  rw [
    Measure.map_map
      (by
        fun_prop :
        Measurable
          (fun path : ℕ → arena.PathEvent =>
            (path 1).action))
      (MeasurableKernelArena.measurable_freshenInitialEvent
        (A := arena))]
      at hrecorded
  have hnormalize :
      (fun path : ℕ → arena.PathEvent =>
        (path 1).action) ∘
          MeasurableKernelArena.freshenInitialEvent =
      (fun path : ℕ → arena.PathEvent =>
        (path 1).action) := by
    funext path
    rfl
  rw [
    hnormalize,
    fresh_restart_next_recorded_action_law,
    absolute_continuation_next_recorded_action_law]
      at hrecorded
  have hpoint :
      (Sum.inr
          (⟨Node.second, false⟩ :
            arena.ActionBundle) :
        Unit ⊕ arena.ActionBundle) ≠
      Sum.inr
          (⟨Node.second, true⟩ :
            arena.ActionBundle) := by
    simp
  exact (dirac_ne_dirac hpoint) hrecorded

/-- The clock-dependent policy fails the distributional local step
compatibility condition already from the retained second-state prefix. -/
theorem not_freshRestartPartialStepCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartPartialStepCompatibleAt
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hcompatible
  have htrajectory :=
    policy.absolutePathMeasureFromPrefix_eq_spliced_of_partialStepCompatible
      terminalSet_measurable 1 absoluteSecondPrefix
      hcompatible
  have hnormalized :=
    policy.tailEventPathMeasureFromPrefix_map_freshen_eq_pathMeasure_of_eq_spliced
      terminalSet_measurable 1 absoluteSecondPrefix
      htrajectory
  have hfresh :
      policy.tailEventPathMeasureFromPrefix
          terminalSet_measurable 0 freshSecondPrefix =
        policy.pathMeasure terminalSet_measurable .second := by
    unfold
      MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix
      MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix
      MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure
    have hshift :
        MeasurableKernelArena.EventHistoryActionPolicy.tailEventPath
            (A := arena) 0 =
          id := by
      funext path time
      simp [
        MeasurableKernelArena.EventHistoryActionPolicy.tailEventPath]
    rw [hshift, Measure.map_id]
    rfl
  apply
    fresh_restart_tail_law_ne_normalized_absolute_continuation_tail_law
  exact hfresh.trans hnormalized.symm

/-- The strict clock-dependent model also fails the generated-law
almost-everywhere one-step kernel certificate. -/
theorem not_freshRestartStepKernelCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartStepKernelCompatibleAt
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hcompatible
  exact
    not_freshRestartPartialStepCompatibleAt_absoluteSecondPrefix
      hcompatible.partialStep

/-- Rooted behavioral action-kernel rebasing fails directly at fresh offset
zero. -/
theorem not_freshRestartRootedActionKernelCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartRootedActionKernelCompatibleAt
        1 absoluteSecondPrefix := by
  intro hcompatible
  have hzero :=
    hcompatible 0 freshSecondPrefix
      freshSecondPrefix_rooted_at_absoluteSecondState
  apply fresh_action_law_ne_absolute_action_law
  simpa using hzero.symm

/-- Consequently, the clock-dependent policy fails the stronger
root-uniform behavioral action-kernel certificate. -/
theorem not_freshRestartRootedActionKernelCompatible :
    ¬ policy.IsFreshRestartRootedActionKernelCompatible := by
  intro hcompatible
  exact
    not_freshRestartRootedActionKernelCompatibleAt_absoluteSecondPrefix
      (hcompatible.at 1 absoluteSecondPrefix)

/-- The strict clock policy cannot factor through any supplied statistic and
common action kernel whose resulting action law is fresh-restart invariant.

This is the exact negative boundary for the generalized sufficient
factorization constructor.
-/
theorem not_factorsThroughStatistic_of_freshRestartActionLawInvariant
    (statistic : arena.EventHistoryStatistic)
    (actionLaw :
      Kernel statistic.Value arena.ActionBundle)
    (hinvariant :
      statistic.IsFreshRestartActionLawInvariant
        actionLaw) :
    ¬ policy.FactorsThroughStatistic
        statistic actionLaw := by
  intro hfactor
  exact
    not_freshRestartRootedActionKernelCompatible
      (EventHistoryActionPolicy.FactorsThroughStatistic.freshRestartRootedActionKernelCompatible_of_actionLawInvariant
        hfactor hinvariant)

/-- In particular, the strict clock policy cannot factor through any supplied
literally fresh-restart-invariant measurable history statistic and common
action kernel.

This is a boundary for the sufficient factorization constructor, not a
converse characterization of arbitrary compatible policies.
-/
theorem not_factorsThroughStatistic_of_freshRestartInvariant
    (statistic : arena.EventHistoryStatistic)
    (actionLaw :
      Kernel statistic.Value arena.ActionBundle)
    (hinvariant :
      statistic.IsFreshRestartInvariant) :
    ¬ policy.FactorsThroughStatistic
        statistic actionLaw := by
  exact
    not_factorsThroughStatistic_of_freshRestartActionLawInvariant
      statistic actionLaw
      (hinvariant.actionLaw actionLaw)

/-- Primitive rooted next-event compatibility fails already at fresh offset
zero: the same second-state prefix selects different actions at absolute time
one and fresh time zero. -/
theorem not_freshRestartRootedPathStepKernelCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hcompatible
  have hzero :=
    hcompatible 0 freshSecondPrefix
      freshSecondPrefix_rooted_at_absoluteSecondState
  apply pathStepKernel_absolute_second_ne_fresh_second
  simpa using hzero

/-- The model also fails the weaker canonical-rooted pointwise certificate.
-/
theorem not_freshRestartRootedStepKernelCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartRootedStepKernelCompatibleAt
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hcompatible
  exact
    not_freshRestartPartialStepCompatibleAt_absoluteSecondPrefix
      hcompatible.partialStep

/-- Consequently, the strict clock-dependent model fails the stronger
pointwise one-step kernel certificate as well. -/
theorem not_freshRestartPointwiseStepKernelCompatibleAt_absoluteSecondPrefix :
    ¬ policy.IsFreshRestartPointwiseStepKernelCompatibleAt
        terminalSet_measurable 1 absoluteSecondPrefix := by
  intro hcompatible
  exact
    not_freshRestartRootedStepKernelCompatibleAt_absoluteSecondPrefix
      hcompatible.rootedStep

end Examples.MeasurableKernelFreshRestartClockBoundary
