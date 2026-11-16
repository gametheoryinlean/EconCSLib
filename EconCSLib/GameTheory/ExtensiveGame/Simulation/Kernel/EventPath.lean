/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Kernel.EventPath — joint state/action paths for measurable kernel arenas

Finite state prefixes erase which action was selected when different actions
produce the same successor state. This module retains that occurrence data in
a fixed measurable event coordinate:

```lean
PathEvent A = A.State × (Unit ⊕ A.ActionBundle)
```

The sum is the measurable equivalent of an optional value: `Sum.inl ()`
means no action and `Sum.inr action` records an occurrence. Coordinate zero
is `(initialState, Sum.inl ())`. A nonterminal successor coordinate is
`(nextState, Sum.inr selectedActionBundle)`, while terminal absorption records
`(currentState, Sum.inl ())` and invents no fallback action.

## Main definitions

* `MeasurableKernelArena.PathEvent` — current state and optional incoming
  selected action.
* `EventHistoryActionPolicy` — measurable action kernels on complete finite
  event prefixes.
* `recordedTransition` — a Markov kernel retaining the selected action beside
  its sampled successor state.
* `EventHistoryActionPolicy.pathMeasure` — the joint Ionescu--Tulcea event
  path law.

## Main results

* `recordedTransition_map_state` and `recordedTransition_map_action` — exact
  coordinate projections of a recorded transition.
* `HistoryActionPolicy.toEventHistoryActionPolicy_pathStepKernel_map_state` —
  exact one-step state projection for the state-history embedding.
* `EventHistoryActionPolicy.stateCoordinateMeasure_eq_coordinateMeasure_map_state`
  — a state-path coordinate is exactly the state projection of the matching
  event coordinate.
* `EventHistoryActionPolicy.statePathMeasure_terminal_absorbing_of_countable`
  — countable discrete event/state paths respect terminal absorption almost
  surely.
* `HistoryActionPolicy.toEventHistoryActionPolicy_statePathMeasure` — exact
  equality of the complete infinite state-path pushforward.

This is a raw operational history layer. It does not yet add players,
observations, information sets, payoff semantics, or equilibrium concepts.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- One state-path coordinate together with the action selected on the
preceding transition, when such an action exists. -/
abbrev PathEvent (A : MeasurableKernelArena) :=
  A.State × (Unit ⊕ A.ActionBundle)

/-- Time-indexed event coordinate type for Ionescu--Tulcea. -/
abbrev EventAt (A : MeasurableKernelArena) (_time : ℕ) :=
  A.PathEvent

/-- State stored in a path event. -/
def PathEvent.state (event : A.PathEvent) : A.State :=
  event.1

/-- Optional action occurrence stored in a path event. -/
def PathEvent.action (event : A.PathEvent) : Unit ⊕ A.ActionBundle :=
  event.2

theorem PathEvent.measurable_state :
    Measurable (@PathEvent.state A) :=
  measurable_fst

theorem PathEvent.measurable_action :
    Measurable (@PathEvent.action A) :=
  measurable_snd

/-- Latest event in a finite event prefix. -/
def latestEvent (time : ℕ)
    (history : Π _index : Finset.Iic time, EventAt A _index) :
    A.PathEvent :=
  history ⟨time, Finset.mem_Iic.mpr le_rfl⟩

/-- Latest state in a finite event prefix. -/
def latestEventState (time : ℕ)
    (history : Π _index : Finset.Iic time, EventAt A _index) :
    A.State :=
  (latestEvent time history).state

theorem measurable_latestEvent (time : ℕ) :
    Measurable (@latestEvent A time) := by
  exact @measurable_pi_apply
    (Finset.Iic time) (fun _ => A.PathEvent)
    (fun _ => inferInstance)
    ⟨time, Finset.mem_Iic.mpr le_rfl⟩

theorem measurable_latestEventState (time : ℕ) :
    Measurable (@latestEventState A time) :=
  PathEvent.measurable_state.comp (measurable_latestEvent time)

/-- Forget recorded actions from a finite event prefix. -/
def eventPrefixStates (time : ℕ)
    (history : Π _index : Finset.Iic time, EventAt A _index) :
    Π _index : Finset.Iic time, StateAt A _index :=
  fun index => (history index).state

theorem measurable_eventPrefixStates (time : ℕ) :
    Measurable (@eventPrefixStates A time) := by
  exact measurable_pi_lambda _ fun index =>
    PathEvent.measurable_state.comp
      (@measurable_pi_apply
        (Finset.Iic time) (fun _ => A.PathEvent)
        (fun _ => inferInstance) index)

/-- Forget recorded actions on an open interval of event coordinates. -/
def eventOpenIntervalStates (start stop : ℕ)
    (history : Π _index : Finset.Ioc start stop, A.PathEvent) :
    Π _index : Finset.Ioc start stop, A.State :=
  fun index => (history index).state

theorem measurable_eventOpenIntervalStates (start stop : ℕ) :
    Measurable (@eventOpenIntervalStates A start stop) := by
  exact measurable_pi_lambda _ fun index =>
    PathEvent.measurable_state.comp
      (@measurable_pi_apply
        (Finset.Ioc start stop) (fun _ => A.PathEvent)
        (fun _ => inferInstance) index)

theorem eventOpenIntervalStates_piSingleton (time : ℕ) :
    eventOpenIntervalStates time (time + 1) ∘
        (MeasurableEquiv.piSingleton
          (X := fun _ => A.PathEvent) time :
          A.PathEvent ≃ᵐ
            (Π _index : Finset.Ioc time (time + 1), A.PathEvent)) =
      (MeasurableEquiv.piSingleton
          (X := fun _ => A.State) time :
          A.State ≃ᵐ
            (Π _index : Finset.Ioc time (time + 1), A.State)) ∘
        PathEvent.state := by
  funext event
  funext index
  cases Nat.mem_Ioc_succ' index
  rfl

theorem eventPrefixStates_IicProdIoc (time : ℕ) :
    eventPrefixStates (time + 1) ∘
        (IicProdIoc
          (X := fun _ => A.PathEvent) time (time + 1)) =
      (IicProdIoc
          (X := fun _ => A.State) time (time + 1)) ∘
        Prod.map
          (eventPrefixStates time)
          (eventOpenIntervalStates time (time + 1)) := by
  funext history
  funext index
  simp only [Function.comp_apply, eventPrefixStates,
    IicProdIoc]
  split_ifs <;> rfl

@[simp]
theorem latestState_eventPrefixStates (time : ℕ)
    (history : Π _index : Finset.Iic time, EventAt A _index) :
    latestState time (eventPrefixStates time history) =
      latestEventState time history :=
  rfl

/-- Forget recorded actions coordinatewise from an infinite event path. -/
def eventPathStates (path : ℕ → A.PathEvent) : ℕ → A.State :=
  fun time => (path time).state

theorem measurable_eventPathStates :
    Measurable (@eventPathStates A) := by
  exact measurable_pi_lambda _ fun time =>
    PathEvent.measurable_state.comp
      (@measurable_pi_apply
        ℕ (fun _ => A.PathEvent)
        (fun _ => inferInstance) time)

/-- The initial event records the supplied state and no fictitious incoming
action. -/
def initialEvent (state : A.State) : A.PathEvent :=
  (state, Sum.inl ())

theorem measurable_initialEvent :
    Measurable (@initialEvent A) := by
  unfold initialEvent
  exact measurable_id.prodMk measurable_const

/-- Transition kernel that retains the selected action beside its sampled
successor state. -/
noncomputable def recordedTransition (A : MeasurableKernelArena) :
    Kernel A.ActionBundle A.PathEvent :=
  ((Kernel.id : Kernel A.ActionBundle A.ActionBundle) ×ₖ
      A.transition).map
    (fun actionNext =>
      (actionNext.2, Sum.inr actionNext.1))

instance recordedTransition_isMarkov (A : MeasurableKernelArena) :
    IsMarkovKernel A.recordedTransition := by
  rw [recordedTransition]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (by fun_prop :
      Measurable fun actionNext : A.ActionBundle × A.State =>
        (actionNext.2, Sum.inr actionNext.1))

/-- Forgetting the recorded action from `recordedTransition` recovers the
arena transition exactly. -/
theorem recordedTransition_map_state (A : MeasurableKernelArena) :
    A.recordedTransition.map PathEvent.state =
      A.transition := by
  rw [recordedTransition]
  rw [← Kernel.map_comp_right _
    (by fun_prop :
      Measurable fun actionNext : A.ActionBundle × A.State =>
        (actionNext.2, Sum.inr actionNext.1))
    PathEvent.measurable_state]
  have hcomp :
      PathEvent.state ∘
          (fun actionNext : A.ActionBundle × A.State =>
            (actionNext.2, Sum.inr actionNext.1)) =
        Prod.snd := by
    funext actionNext
    rfl
  rw [hcomp]
  rw [← Kernel.snd_eq]
  exact Kernel.snd_prod _ _

/-- Projecting a recorded transition to its action occurrence gives the
deterministic record of the selected input action. -/
theorem recordedTransition_map_action (A : MeasurableKernelArena) :
    A.recordedTransition.map PathEvent.action =
      Kernel.deterministic Sum.inr measurable_inr := by
  rw [recordedTransition]
  rw [← Kernel.map_comp_right _
    (by fun_prop :
      Measurable fun actionNext : A.ActionBundle × A.State =>
        (actionNext.2, Sum.inr actionNext.1))
    PathEvent.measurable_action]
  have hcomp :
      PathEvent.action ∘
          (fun actionNext : A.ActionBundle × A.State =>
            (actionNext.2, Sum.inr actionNext.1)) =
        Sum.inr ∘ Prod.fst := by
    funext actionNext
    rfl
  rw [hcomp]
  rw [Kernel.map_comp_right _
    measurable_fst measurable_inr]
  rw [← Kernel.fst_eq]
  rw [Kernel.fst_prod]
  exact Kernel.id_map measurable_inr

/-- Finite event prefixes whose latest state is terminal. -/
def eventPrefixTerminalSet (A : MeasurableKernelArena) (time : ℕ) :
    Set (Π index : Finset.Iic time, EventAt A index) :=
  {history | latestEventState time history ∈ A.terminalSet}

theorem measurableSet_eventPrefixTerminalSet
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    MeasurableSet (A.eventPrefixTerminalSet time) :=
  measurable_latestEventState time hterminal

/-- A measurable legal-action policy on complete finite state/action event
prefixes. -/
structure EventHistoryActionPolicy (A : MeasurableKernelArena) where
  /-- Measurable, possibly killed, action kernel at each event prefix. -/
  kernel :
    (time : ℕ) →
      Kernel
        (Π index : Finset.Iic time, EventAt A index)
        A.ActionBundle
  /-- Terminal prefixes produce no action mass. -/
  terminal_zero :
    ∀ time history,
      IsEmpty (A.Action (latestEventState time history)) →
        kernel time history = 0
  /-- Every nonterminal prefix has normalized action mass. -/
  nonterminal_isProbability :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestEventState time history)) →
        IsProbabilityMeasure (kernel time history)
  /-- At every nonterminal prefix, the selected bundled action lies in the
  latest state's dependent action fiber almost surely. -/
  legal :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestEventState time history)) →
        ∀ᵐ stateAction ∂kernel time history,
          stateAction ∈
            A.actionFiber (latestEventState time history)

namespace EventHistoryActionPolicy

/-- The selected action is legal for the latest event state almost surely. -/
theorem ae_mem_actionFiber (policy : A.EventHistoryActionPolicy)
    (time : ℕ)
    (history : Π index : Finset.Iic time, EventAt A index)
    (hnonterminal :
      ¬ IsEmpty (A.Action (latestEventState time history))) :
    ∀ᵐ stateAction ∂policy.kernel time history,
      stateAction ∈ A.actionFiber
        (latestEventState time history) := by
  exact policy.legal time history hnonterminal

/-- With measurable state singletons, genuine event-history legality implies
the numerical measure-one fiber equation. -/
theorem legal_mass_one (policy : A.EventHistoryActionPolicy)
    [MeasurableSingletonClass A.State]
    (time : ℕ)
    (history : Π index : Finset.Iic time, EventAt A index)
    (hnonterminal :
      ¬ IsEmpty (A.Action (latestEventState time history))) :
    policy.kernel time history
        (A.actionFiber (latestEventState time history)) = 1 := by
  letI : IsProbabilityMeasure (policy.kernel time history) :=
    policy.nonterminal_isProbability time history hnonterminal
  have hmeasure :=
    (ae_mem_iff_measure_eq
      (A.measurableSet_actionFiber
        (latestEventState time history)).nullMeasurableSet).mp
      (policy.ae_mem_actionFiber time history hnonterminal)
  simpa using hmeasure

/-- Select an action from an event prefix, sample its successor, and retain
the selected action in the next event. -/
noncomputable def actionStepKernel
    (policy : A.EventHistoryActionPolicy) (time : ℕ) :
    Kernel
      (Π index : Finset.Iic time, EventAt A index)
      (EventAt A (time + 1)) :=
  A.recordedTransition ∘ₖ policy.kernel time

/-- Forgetting recorded actions from a nonterminal joint step recovers
ordinary state transition after action selection. -/
theorem actionStepKernel_map_state
    (policy : A.EventHistoryActionPolicy) (time : ℕ) :
    (policy.actionStepKernel time).map PathEvent.state =
      A.transition ∘ₖ policy.kernel time := by
  rw [actionStepKernel, Kernel.map_comp]
  rw [A.recordedTransition_map_state]

/-- Projecting a nonterminal joint step to the recorded-action coordinate
recovers the selected action law, tagged by `Sum.inr`. -/
theorem actionStepKernel_map_action
    (policy : A.EventHistoryActionPolicy) (time : ℕ) :
    (policy.actionStepKernel time).map PathEvent.action =
      (policy.kernel time).map Sum.inr := by
  rw [actionStepKernel, Kernel.map_comp]
  rw [A.recordedTransition_map_action]
  rw [Kernel.deterministic_comp_eq_map]

/-- Terminal-absorbing joint state/action event step. -/
noncomputable def pathStepKernel
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    Kernel
      (Π index : Finset.Iic time, EventAt A index)
      (EventAt A (time + 1)) := by
  classical
  exact Kernel.piecewise
    (A.measurableSet_eventPrefixTerminalSet hterminal time)
    (Kernel.deterministic
      (fun history =>
        A.initialEvent (latestEventState time history))
      (measurable_initialEvent.comp
        (measurable_latestEventState time)))
    (policy.actionStepKernel time)

instance pathStepKernel_isMarkov
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    IsMarkovKernel (policy.pathStepKernel hterminal time) := by
  classical
  constructor
  intro history
  rw [pathStepKernel, Kernel.piecewise_apply]
  split_ifs with hhistory
  · infer_instance
  · have hnonterminal :
        ¬ IsEmpty (A.Action (latestEventState time history)) := by
      simpa only [eventPrefixTerminalSet, terminalSet,
        Set.mem_setOf_eq] using hhistory
    change
      IsProbabilityMeasure
        ((policy.kernel time history).bind A.recordedTransition)
    letI : IsProbabilityMeasure (policy.kernel time history) :=
      policy.nonterminal_isProbability time history hnonterminal
    exact MeasureTheory.isProbabilityMeasure_bind
      A.recordedTransition.aemeasurable
      (Filter.Eventually.of_forall fun stateAction => inferInstance)

@[simp]
theorem pathStepKernel_apply_terminal
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ)
    (history : Π index : Finset.Iic time, EventAt A index)
    (hstate :
      IsEmpty (A.Action (latestEventState time history))) :
    policy.pathStepKernel hterminal time history =
      Measure.dirac
        (A.initialEvent (latestEventState time history)) := by
  classical
  rw [pathStepKernel, Kernel.piecewise_apply, if_pos]
  · exact Kernel.deterministic_apply
      (measurable_initialEvent.comp
        (measurable_latestEventState time)) history
  · simpa only [eventPrefixTerminalSet, terminalSet,
      Set.mem_setOf_eq] using hstate

@[simp]
theorem pathStepKernel_apply_nonterminal
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ)
    (history : Π index : Finset.Iic time, EventAt A index)
    (hstate :
      ¬ IsEmpty (A.Action (latestEventState time history))) :
    policy.pathStepKernel hterminal time history =
      (policy.kernel time history).bind A.recordedTransition := by
  classical
  rw [pathStepKernel, Kernel.piecewise_apply, if_neg]
  · rfl
  · simpa only [eventPrefixTerminalSet, terminalSet,
      Set.mem_setOf_eq] using hstate

/-- Infinite discrete-event joint state/action event-path law. -/
noncomputable def pathMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    Measure (ℕ → A.PathEvent) :=
  Kernel.traj (policy.pathStepKernel hterminal) 0
    (fun _ => A.initialEvent initialState)

/-- The fixed-initial-prefix event path construction is the corresponding
`trajMeasure` started from a Dirac initial event. -/
theorem pathMeasure_eq_trajMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.pathMeasure hterminal initialState =
      Kernel.trajMeasure
        (Measure.dirac (A.initialEvent initialState))
        (policy.pathStepKernel hterminal) := by
  rw [pathMeasure, Kernel.trajMeasure]
  rw [Measure.map_dirac' (by fun_prop)]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rfl

instance pathMeasure_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    IsProbabilityMeasure
      (policy.pathMeasure hterminal initialState) := by
  rw [pathMeasure]
  infer_instance

/-- Joint finite-event-prefix marginal. -/
noncomputable def prefixMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure (Π _index : Finset.Iic time, A.PathEvent) :=
  (policy.pathMeasure hterminal initialState).map
    (Preorder.frestrictLe time)

/-- One-event coordinate marginal. -/
noncomputable def coordinateMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure A.PathEvent :=
  (policy.pathMeasure hterminal initialState).map
    (fun path => path time)

/-- State-path pushforward of the joint event-path law. -/
noncomputable def statePathMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    Measure (ℕ → A.State) :=
  (policy.pathMeasure hterminal initialState).map
    eventPathStates

/-- The state-path pushforward of an admissible event policy is a probability
measure. -/
instance statePathMeasure_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    IsProbabilityMeasure
      (policy.statePathMeasure hterminal initialState) := by
  rw [statePathMeasure]
  exact
    Measure.isProbabilityMeasure_map
      measurable_eventPathStates.aemeasurable

/-- One coordinate marginal of the state-path pushforward. -/
noncomputable def stateCoordinateMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (time : ℕ) :
    Measure A.State :=
  (policy.statePathMeasure hterminal initialState).map
    (fun path => path time)

/-- A state-path coordinate is exactly the state projection of the matching
event-coordinate marginal. -/
theorem stateCoordinateMeasure_eq_coordinateMeasure_map_state
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (time : ℕ) :
    policy.stateCoordinateMeasure hterminal initialState time =
      (policy.coordinateMeasure hterminal initialState time).map
        PathEvent.state := by
  rw [stateCoordinateMeasure, statePathMeasure, coordinateMeasure]
  rw [Measure.map_map
    (measurable_pi_apply time)
    measurable_eventPathStates]
  rw [Measure.map_map
    PathEvent.measurable_state
    (measurable_pi_apply time)]
  rfl

/-- An event-coordinate marginal is the latest-event pushforward of its
finite-prefix law. -/
theorem coordinateMeasure_eq_map_prefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time =
      (policy.prefixMeasure hterminal initialState time).map
        (latestEvent time) := by
  rw [coordinateMeasure, prefixMeasure]
  rw [Measure.map_map
    (measurable_latestEvent time)
    (by fun_prop)]
  rfl

/-- Every finite event-prefix marginal is the corresponding Mathlib partial
trajectory. -/
theorem prefixMeasure_eq_partialTraj
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.prefixMeasure hterminal initialState time =
      Kernel.partialTraj
        (policy.pathStepKernel hterminal) 0 time
        (fun _ => A.initialEvent initialState) := by
  rw [prefixMeasure, pathMeasure]
  exact
    @Kernel.traj_map_frestrictLe_apply
      (EventAt A) (fun _ => inferInstance)
      (policy.pathStepKernel hterminal)
      (fun _ => inferInstance)
      0 time (fun _ => A.initialEvent initialState)

/-- At time zero the event is the initial state with no recorded action. -/
@[simp]
theorem coordinateMeasure_zero
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.coordinateMeasure hterminal initialState 0 =
      Measure.dirac (A.initialEvent initialState) := by
  rw [coordinateMeasure, pathMeasure]
  have hprefix :=
    @Kernel.traj_map_frestrictLe_apply
      (EventAt A) (fun _ => inferInstance)
      (policy.pathStepKernel hterminal)
      (fun _ => inferInstance)
      0 0 (fun _ => A.initialEvent initialState)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at hprefix
  have hcoord :
      (fun path : ℕ → A.PathEvent => path 0) =
        (fun history0 : (Π _index : Finset.Iic 0, A.PathEvent) =>
          latestEvent 0 history0) ∘
          Preorder.frestrictLe 0 :=
    rfl
  rw [hcoord, ← Measure.map_map
    (measurable_latestEvent 0) (by fun_prop)]
  rw [hprefix]
  rw [Measure.map_dirac' (measurable_latestEvent 0)]
  rfl

/-- Pushing the next partial event trajectory to its newest coordinate is
exactly one event-history step after the preceding complete prefix. -/
theorem map_partialTraj_latestEvent_succ
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (time : ℕ) :
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestEvent time.succ) =
      policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time := by
  rw [← Kernel.partialTraj_comp_partialTraj
    (κ := policy.pathStepKernel hterminal)
    (a := 0) (b := time) (c := time.succ)
    (Nat.zero_le time) (Nat.le_succ time)]
  rw [Kernel.map_comp]
  have hlatest :
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        time time.succ).map (latestEvent time.succ) =
          policy.pathStepKernel hterminal time := by
    simpa only [Nat.succ_eq_add_one, latestEvent] using
      (@Kernel.map_partialTraj_succ_self
        (EventAt A) (fun _ => inferInstance)
        (policy.pathStepKernel hterminal)
        (fun _ => inferInstance)
        time)
  rw [hlatest]

/-- The next event-coordinate law integrates the next event-history step
against the complete preceding event-prefix law. -/
theorem coordinateMeasure_succ
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time.succ =
      policy.pathStepKernel hterminal time ∘ₘ
        policy.prefixMeasure hterminal initialState time := by
  rw [coordinateMeasure_eq_map_prefix,
    prefixMeasure_eq_partialTraj]
  have hstep := congrArg
    (fun kernel =>
      kernel
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState))
    (policy.map_partialTraj_latestEvent_succ hterminal time)
  change
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestEvent time.succ)
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState) =
      (policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time)
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState) at hstep
  rw [Kernel.map_apply _
    (measurable_latestEvent time.succ)] at hstep
  rw [Kernel.comp_apply] at hstep
  rw [hstep]
  rw [← prefixMeasure_eq_partialTraj]

/-- The first post-initial event coordinate is the time-zero step kernel
evaluated at the singleton initial prefix. -/
theorem coordinateMeasure_one
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.coordinateMeasure hterminal initialState 1 =
      policy.pathStepKernel hterminal 0
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState) := by
  rw [show 1 = Nat.succ 0 by rfl]
  rw [policy.coordinateMeasure_succ hterminal initialState 0]
  rw [prefixMeasure_eq_partialTraj]
  rw [Kernel.partialTraj_self, Kernel.id_apply]
  exact
    Measure.dirac_bind
      (policy.pathStepKernel hterminal 0).measurable
      (fun _ : Finset.Iic 0 =>
        A.initialEvent initialState)

/-- At a nonterminal initial state, the first state-coordinate law is the
arena transition integrated against the policy's concrete root-action law. -/
theorem stateCoordinateMeasure_one_of_nonterminal
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    (hnonterminal :
      ¬ IsEmpty (A.Action initialState)) :
    policy.stateCoordinateMeasure hterminal initialState 1 =
      A.transition ∘ₘ
        policy.kernel 0
          (fun _ : Finset.Iic 0 =>
            A.initialEvent initialState) := by
  rw [
    stateCoordinateMeasure_eq_coordinateMeasure_map_state,
    coordinateMeasure_one]
  rw [
    pathStepKernel_apply_nonterminal
      policy hterminal 0
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState)]
  · rw [Measure.map_comp
      (policy.kernel 0
        (fun _ : Finset.Iic 0 =>
          A.initialEvent initialState))
      A.recordedTransition
      PathEvent.measurable_state]
    rw [A.recordedTransition_map_state]
  · simpa using hnonterminal

/-- On countable discrete event-prefix carriers, the terminal-aware executor
is terminal-absorbing almost surely on state paths.

Event-carrier countability also gives state countability through the
measurable optional-action coordinate's `none` injection. Together with the
two measurable-singleton hypotheses it makes the varying prefix/state
equality event measurable. The singleton hypotheses remain explicit because
such a diagonal need not be measurable for an arbitrary measurable state
space. -/
theorem statePathMeasure_terminal_absorbing_of_countable
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State)
    [Countable A.PathEvent]
    [MeasurableSingletonClass A.PathEvent]
    [MeasurableSingletonClass A.State] :
    ∀ᵐ path ∂policy.statePathMeasure hterminal initialState,
      ∀ time, IsEmpty (A.Action (path time)) →
        path (time + 1) = path time := by
  letI : Countable A.State :=
    (show Function.Injective
        (fun state : A.State =>
          ((state,
              (Sum.inl () :
                Unit ⊕ A.ActionBundle)) : A.PathEvent)) by
      intro first second heq
      exact congrArg Prod.fst heq).countable
  have hevent :
      ∀ᵐ path ∂policy.pathMeasure hterminal initialState,
        ∀ time, IsEmpty (A.Action (path time).state) →
          (path (time + 1)).state = (path time).state := by
    rw [eventually_countable_forall]
    intro time
    have hjoint :
        (policy.pathMeasure hterminal initialState).map
              (Preorder.frestrictLe time) ⊗ₘ
            policy.pathStepKernel hterminal time =
          (policy.pathMeasure hterminal initialState).map
            (fun path =>
              (Preorder.frestrictLe time path,
                path (time + 1))) := by
      rw [policy.pathMeasure_eq_trajMeasure
        hterminal initialState]
      exact
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have hcomp :
        ∀ᵐ pair ∂
            ((policy.pathMeasure hterminal initialState).map
                (Preorder.frestrictLe time) ⊗ₘ
              policy.pathStepKernel hterminal time),
          IsEmpty
              (A.Action
                (latestEventState time pair.1)) →
            pair.2.state =
              latestEventState time pair.1 := by
      apply Measure.ae_compProd_of_ae_ae
        (Set.to_countable _).measurableSet
      refine Filter.Eventually.of_forall fun historyPrefix => ?_
      by_cases hstate :
          IsEmpty
            (A.Action
              (latestEventState time historyPrefix))
      · rw [
          policy.pathStepKernel_apply_terminal
            hterminal time historyPrefix hstate]
        simpa only [ae_dirac_eq, Filter.eventually_pure,
          initialEvent, PathEvent.state] using
          (show
            IsEmpty
                (A.Action
                  (latestEventState time historyPrefix)) →
              True from fun _ => trivial)
      · exact Filter.Eventually.of_forall fun _ hterminalState =>
          (hstate hterminalState).elim
    rw [hjoint] at hcomp
    have hpull := MeasureTheory.ae_of_ae_map
      (μ := policy.pathMeasure hterminal initialState)
      (f := fun path =>
        (Preorder.frestrictLe time path,
          path (time + 1)))
      (p := fun pair =>
        IsEmpty
            (A.Action
              (latestEventState time pair.1)) →
          pair.2.state =
            latestEventState time pair.1)
      (by fun_prop) hcomp
    simpa only [latestEventState, latestEvent] using hpull
  unfold statePathMeasure
  rw [MeasureTheory.ae_map_iff
    measurable_eventPathStates.aemeasurable]
  · simpa only [eventPathStates, PathEvent.state] using hevent
  · rw [show
        {path : ℕ → A.State |
            ∀ time, IsEmpty (A.Action (path time)) →
              path (time + 1) = path time} =
          ⋂ time,
            ({path : ℕ → A.State |
                IsEmpty (A.Action (path time))}ᶜ ∪
              {path : ℕ → A.State |
                path (time + 1) = path time}) by
        ext path
        simp only [Set.mem_setOf_eq, Set.mem_iInter,
          Set.mem_union, Set.mem_compl_iff]
        constructor
        · intro h time
          by_cases hstate :
              IsEmpty (A.Action (path time))
          · exact Or.inr (h time hstate)
          · exact Or.inl hstate
        · intro h time hstate
          rcases h time with hnonterminal | heq
          · exact (hnonterminal hstate).elim
          · exact heq]
    apply MeasurableSet.iInter
    intro time
    apply MeasurableSet.union
    · apply MeasurableSet.compl
      simpa only [terminalSet, Set.mem_setOf_eq] using
        hterminal.preimage (measurable_pi_apply time)
    · exact measurableSet_eq_fun
        (measurable_pi_apply (time + 1))
        (measurable_pi_apply time)

end EventHistoryActionPolicy

namespace HistoryActionPolicy

/-- Regard a finite-state-prefix policy as an event-history policy that
forgets all recorded actions before querying its action kernel. -/
def toEventHistoryActionPolicy
    (policy : A.HistoryActionPolicy) :
    A.EventHistoryActionPolicy where
  kernel := fun time =>
    Kernel.comap (policy.kernel time)
      (eventPrefixStates time)
      (measurable_eventPrefixStates time)
  terminal_zero := by
    intro time history hterminal
    change
      policy.kernel time (eventPrefixStates time history) = 0
    exact policy.terminal_zero _ _ hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    change
      IsProbabilityMeasure
        (policy.kernel time (eventPrefixStates time history))
    exact policy.nonterminal_isProbability _ _ hnonterminal
  legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂policy.kernel time (eventPrefixStates time history),
        stateAction ∈
          A.actionFiber
            (latestState time
              (eventPrefixStates time history))
    exact policy.legal _ _ hnonterminal

@[simp]
theorem toEventHistoryActionPolicy_kernel_apply
    (policy : A.HistoryActionPolicy) (time : ℕ)
    (history : Π index : Finset.Iic time, EventAt A index) :
    policy.toEventHistoryActionPolicy.kernel time history =
      policy.kernel time (eventPrefixStates time history) :=
  rfl

/-- The state projection of an embedded event-history step is exactly the
existing state-history step queried on the forgotten state prefix. -/
theorem toEventHistoryActionPolicy_pathStepKernel_map_state
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    (policy.toEventHistoryActionPolicy.pathStepKernel
        hterminal time).map PathEvent.state =
      Kernel.comap (policy.pathStepKernel hterminal time)
        (eventPrefixStates time)
        (measurable_eventPrefixStates time) := by
  apply Kernel.ext
  intro history
  rw [Kernel.map_apply _
    PathEvent.measurable_state]
  rw [Kernel.comap_apply _
    (measurable_eventPrefixStates time)]
  by_cases hstate :
      IsEmpty (A.Action (latestEventState time history))
  · have hstate' :
        IsEmpty
          (A.Action
            (latestState time
              (eventPrefixStates time history))) := by
      simpa using hstate
    rw [EventHistoryActionPolicy.pathStepKernel_apply_terminal
      _ hterminal time history hstate]
    rw [HistoryActionPolicy.pathStepKernel_apply_terminal
      _ hterminal time (eventPrefixStates time history) hstate']
    rw [Measure.map_dirac' PathEvent.measurable_state]
    rfl
  · have hstate' :
        ¬ IsEmpty
          (A.Action
            (latestState time
              (eventPrefixStates time history))) := by
      simpa using hstate
    rw [EventHistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ hterminal time history hstate]
    rw [HistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ hterminal time (eventPrefixStates time history) hstate']
    change
      ((policy.toEventHistoryActionPolicy.actionStepKernel time)
        history).map PathEvent.state =
        (policy.kernel time
          (eventPrefixStates time history)).bind A.transition
    rw [← Kernel.map_apply _
      PathEvent.measurable_state]
    rw [EventHistoryActionPolicy.actionStepKernel_map_state]
    rfl

/-- Extending an event prefix by one embedded-policy step and then forgetting
actions is exactly the ordinary one-step extension of the forgotten state
prefix. -/
theorem toEventHistoryActionPolicy_partialTraj_succ_map_states
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    (Kernel.partialTraj
      (policy.toEventHistoryActionPolicy.pathStepKernel hterminal)
      time (time + 1)).map (eventPrefixStates (time + 1)) =
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        time (time + 1)).comap
          (eventPrefixStates time)
          (measurable_eventPrefixStates time) := by
  rw [Kernel.partialTraj_succ_self,
    Kernel.partialTraj_succ_self]
  rw [← Kernel.map_comp_right _
    measurable_IicProdIoc
    (measurable_eventPrefixStates (time + 1))]
  rw [eventPrefixStates_IicProdIoc]
  rw [Kernel.map_comp_right _
    ((measurable_eventPrefixStates time).prodMap
      (measurable_eventOpenIntervalStates time (time + 1)))
    measurable_IicProdIoc]
  rw [← Kernel.map_prod_map _ _
    (measurable_eventPrefixStates time)
    (measurable_eventOpenIntervalStates time (time + 1))]
  rw [← Kernel.map_comp_right _
    (MeasurableEquiv.piSingleton
      (X := fun _ => A.PathEvent) time).measurable
    (measurable_eventOpenIntervalStates time (time + 1))]
  rw [eventOpenIntervalStates_piSingleton]
  rw [Kernel.map_comp_right _
    PathEvent.measurable_state
    (MeasurableEquiv.piSingleton
      (X := fun _ => A.State) time).measurable]
  rw [toEventHistoryActionPolicy_pathStepKernel_map_state]
  have hprod :
      ((Kernel.id :
          Kernel
            (Π _index : Finset.Iic time, A.PathEvent)
            (Π _index : Finset.Iic time, A.PathEvent)).map
          (eventPrefixStates time)) ×ₖ
        (((policy.pathStepKernel hterminal time).comap
            (eventPrefixStates time)
            (measurable_eventPrefixStates time)).map
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.State) time)) =
        (((Kernel.id :
            Kernel
              (Π _index : Finset.Iic time, A.State)
              (Π _index : Finset.Iic time, A.State)) ×ₖ
          ((policy.pathStepKernel hterminal time).map
            (MeasurableEquiv.piSingleton
              (X := fun _ => A.State) time))).comap
            (eventPrefixStates time)
            (measurable_eventPrefixStates time)) := by
    rw [Kernel.comap_prod _ _
      (measurable_eventPrefixStates time)]
    rw [Kernel.id_map (measurable_eventPrefixStates time),
      Kernel.id_comap (measurable_eventPrefixStates time)]
    rw [Kernel.comap_map_comm _
      (measurable_eventPrefixStates time)
      (MeasurableEquiv.piSingleton
        (X := fun _ => A.State) time).measurable]
  rw [hprod]
  exact (Kernel.comap_map_comm
    ((Kernel.id :
        Kernel
          (Π _index : Finset.Iic time, A.State)
          (Π _index : Finset.Iic time, A.State)) ×ₖ
      ((policy.pathStepKernel hterminal time).map
        (MeasurableEquiv.piSingleton
          (X := fun _ => A.State) time)))
    (measurable_eventPrefixStates time)
    (measurable_IicProdIoc :
      Measurable
        (IicProdIoc
          (X := fun _ => A.State) time (time + 1)))).symm

/-- Every finite event-prefix trajectory of an embedded state-history policy
projects to the corresponding finite state-prefix trajectory. -/
theorem toEventHistoryActionPolicy_partialTraj_map_states
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    (Kernel.partialTraj
      (policy.toEventHistoryActionPolicy.pathStepKernel hterminal)
      0 time).map (eventPrefixStates time) =
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        0 time).comap
          (eventPrefixStates 0)
          (measurable_eventPrefixStates 0) := by
  induction time with
  | zero =>
      rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
      rw [Kernel.id_map (measurable_eventPrefixStates 0),
        Kernel.id_comap (measurable_eventPrefixStates 0)]
  | succ time ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le time),
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le time)]
      rw [Kernel.map_comp]
      rw [toEventHistoryActionPolicy_partialTraj_succ_map_states]
      rw [← Kernel.comp_map _ _
        (measurable_eventPrefixStates time)]
      rw [ih]
      rw [← Kernel.comp_deterministic_eq_comap _
        (measurable_eventPrefixStates 0)]
      rw [← Kernel.comp_assoc]
      rw [← Kernel.partialTraj_succ_eq_comp (Nat.zero_le time)]
      rw [Kernel.comp_deterministic_eq_comap]

/-- Every finite state-prefix marginal is preserved exactly by the embedding
into event-history policies. -/
theorem toEventHistoryActionPolicy_prefixMeasure_map_states
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    (policy.toEventHistoryActionPolicy.prefixMeasure
      hterminal initialState time).map
        (eventPrefixStates time) =
      policy.prefixMeasure hterminal initialState time := by
  rw [EventHistoryActionPolicy.prefixMeasure_eq_partialTraj,
    HistoryActionPolicy.prefixMeasure_eq_partialTraj]
  rw [← Kernel.map_apply _
    (measurable_eventPrefixStates time)]
  rw [toEventHistoryActionPolicy_partialTraj_map_states]
  rw [Kernel.comap_apply _
    (measurable_eventPrefixStates 0)]
  rfl

/-- The state-path pushforward of the embedded event-history law is exactly
the original state-history path law. This equality is for the complete
infinite path measure, not only its one-coordinate marginals. -/
theorem toEventHistoryActionPolicy_statePathMeasure
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.toEventHistoryActionPolicy.statePathMeasure
        hterminal initialState =
      policy.pathMeasure hterminal initialState := by
  let statePrefixes := fun time =>
    Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time
      (fun _ => initialState)
  have hfamily :
      MeasureTheory.IsProjectiveMeasureFamily
        (MeasureTheory.inducedFamily statePrefixes) :=
    Kernel.isProjectiveMeasureFamily_partialTraj
      (policy.pathStepKernel hterminal)
      (fun _ => initialState)
  have hevent :
      MeasureTheory.IsProjectiveLimit
        (policy.toEventHistoryActionPolicy.statePathMeasure
          hterminal initialState)
        (MeasureTheory.inducedFamily statePrefixes) := by
    refine
      (MeasureTheory.isProjectiveLimit_nat_iff
        hfamily
        (policy.toEventHistoryActionPolicy.statePathMeasure
          hterminal initialState)).2 ?_
    intro time
    rw [MeasureTheory.inducedFamily_Iic]
    rw [EventHistoryActionPolicy.statePathMeasure]
    rw [Measure.map_map
      (by fun_prop)
      measurable_eventPathStates]
    have hrestrict :
        (Preorder.frestrictLe time :
            (ℕ → A.State) →
              (Π _index : Finset.Iic time, A.State)) ∘
            (@eventPathStates A) =
          (@eventPrefixStates A time) ∘
            (Preorder.frestrictLe time :
              (ℕ → A.PathEvent) →
                (Π _index : Finset.Iic time, A.PathEvent)) := by
      rfl
    rw [hrestrict]
    rw [← Measure.map_map
      (measurable_eventPrefixStates time)
      (by fun_prop)]
    change
      (policy.toEventHistoryActionPolicy.prefixMeasure
        hterminal initialState time).map
          (eventPrefixStates time) =
        statePrefixes time
    rw [toEventHistoryActionPolicy_prefixMeasure_map_states]
    exact HistoryActionPolicy.prefixMeasure_eq_partialTraj
      policy hterminal initialState time
  have hstate :
      MeasureTheory.IsProjectiveLimit
        (policy.pathMeasure hterminal initialState)
        (MeasureTheory.inducedFamily statePrefixes) := by
    rw [HistoryActionPolicy.pathMeasure]
    exact Kernel.isProjectiveLimit_trajFun
      (policy.pathStepKernel hterminal) 0
      (fun _ => initialState)
  exact hevent.unique hstate

end HistoryActionPolicy

end MeasurableKernelArena
