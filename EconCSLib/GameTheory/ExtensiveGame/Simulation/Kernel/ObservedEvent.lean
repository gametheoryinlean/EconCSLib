/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath

/-!
# Kernel.ObservedEvent — measurable information policies on event histories

`MeasurableKernelEventPath` lets an action kernel inspect a complete finite
state/action event prefix. This module factors that dependence through a fixed
measurable information map. Keeping the information map separate from the
policy is essential: all policies and deviations for one observed model must
share the same information partition.

An `EventInformation` supplies a measurable information value at every event
time. An `EventInformation.ActionPolicy` supplies an action kernel indexed
only by that value. Compilation by measurable comap produces the raw
`EventHistoryActionPolicy`, so information-set consistency is structural.

Information homomorphisms point from a finer information structure to a
coarser one. Pulling a coarse policy back along such a map preserves the
compiled raw executor, every stopped event step, and the whole event-path law
exactly.

## Main definitions

* `EventInformation` — a time-indexed measurable statistic of finite event
  prefixes.
* `EventInformation.Hom` — a measurable factor map from finer to coarser
  information.
* `EventInformation.ActionPolicy` — legal normalized action kernels indexed
  only by fixed information values.
* `EventInformation.ActionPolicy.toEventHistoryActionPolicy` — compilation to
  the raw event executor.
* `EventInformation.full`, `statePrefix`, and `latestState` — the complete
  event, complete state-prefix, and current-state information structures.

This is an analytic operational information layer. It does not yet choose a
player mover, bridge `ObservedGame`, define payoffs, or assert recall or
equilibrium properties.
-/

open MeasureTheory ProbabilityTheory

universe uS uA uI uJ uK

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- Two raw event-history policies are equal when their action-kernel
families are equal. The remaining fields are propositions. -/
@[ext]
theorem EventHistoryActionPolicy.ext
    {first second : A.EventHistoryActionPolicy}
    (hkernel : first.kernel = second.kernel) :
    first = second := by
  cases first
  cases second
  cases hkernel
  rfl

/-- Complete finite joint event prefix through `time`. -/
abbrev EventPrefix (A : MeasurableKernelArena) (time : ℕ) :=
  Π _index : Finset.Iic time, EventAt A _index

/-- A fixed measurable information statistic of every finite event prefix.

The information type may vary with event time. This supports
time-inhomogeneous observation spaces without adding any finiteness,
countability, or topological assumptions. -/
structure EventInformation (A : MeasurableKernelArena) where
  /-- Information values available at each event time. -/
  Information : ℕ → Type uI
  /-- Measurable structure on each information space. -/
  informationMeasurable :
    ∀ time, MeasurableSpace (Information time)
  /-- Information value represented by a complete event prefix. -/
  informationAt :
    (time : ℕ) → A.EventPrefix time → Information time
  /-- Every information map is measurable. -/
  informationAt_measurable :
    ∀ time,
      @Measurable
        (A.EventPrefix time) (Information time)
        inferInstance (informationMeasurable time)
        (informationAt time)

namespace EventInformation

instance (information : A.EventInformation) (time : ℕ) :
    MeasurableSpace (information.Information time) :=
  information.informationMeasurable time

/-- A measurable factor map from a finer event-information structure to a
coarser one. -/
structure Hom
    (fine : EventInformation A)
    (coarse : EventInformation A) where
  /-- Forgetful information map at each event time. -/
  map :
    (time : ℕ) →
      fine.Information time → coarse.Information time
  /-- Every forgetful map is measurable. -/
  map_measurable :
    ∀ time, Measurable (map time)
  /-- Computing fine information and then forgetting it gives exactly the
  coarse information of the same event prefix. -/
  map_informationAt :
    ∀ time history,
      map time (fine.informationAt time history) =
        coarse.informationAt time history

namespace Hom

variable
  {fine : EventInformation A}
  {middle : EventInformation A}
  {coarse : EventInformation A}

/-- Information factors are equal when their map families are equal. -/
@[ext]
theorem ext {first second : Hom fine coarse}
    (hmap : first.map = second.map) :
    first = second := by
  cases first
  cases second
  cases hmap
  rfl

/-- Identity information factor. -/
def id (information : A.EventInformation) :
    Hom information information where
  map := fun _ => _root_.id
  map_measurable := fun _ => measurable_id
  map_informationAt := by
    intro time history
    rfl

/-- Compose information factors from fine to coarse. -/
def trans (f : Hom fine middle) (g : Hom middle coarse) :
    Hom fine coarse where
  map := fun time => g.map time ∘ f.map time
  map_measurable := fun time =>
    (g.map_measurable time).comp (f.map_measurable time)
  map_informationAt := by
    intro time history
    rw [Function.comp_apply, f.map_informationAt,
      g.map_informationAt]

@[simp]
theorem id_map (information : A.EventInformation)
    (time : ℕ) (value : information.Information time) :
    (id information).map time value = value :=
  rfl

@[simp]
theorem trans_map (f : Hom fine middle) (g : Hom middle coarse)
    (time : ℕ) (value : fine.Information time) :
    (f.trans g).map time value =
      g.map time (f.map time value) :=
  rfl

@[simp]
theorem id_trans (f : Hom fine coarse) :
    (id fine).trans f = f := by
  apply ext
  funext time value
  rfl

@[simp]
theorem trans_id (f : Hom fine coarse) :
    f.trans (id coarse) = f := by
  apply ext
  funext time value
  rfl

theorem trans_assoc
    {coarsest : EventInformation A}
    (f : Hom fine middle) (g : Hom middle coarse)
    (h : Hom coarse coarsest) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  apply ext
  funext time value
  rfl

end Hom

/-- Full event-prefix information. -/
def full (A : MeasurableKernelArena) :
    EventInformation A where
  Information := fun time => A.EventPrefix time
  informationMeasurable := fun _ => inferInstance
  informationAt := fun _ history => history
  informationAt_measurable := fun _ => measurable_id

/-- Complete state-prefix information, forgetting every recorded action. -/
def statePrefix (A : MeasurableKernelArena) :
    EventInformation A where
  Information := fun time =>
    Π _index : Finset.Iic time, StateAt A _index
  informationMeasurable := fun _ => inferInstance
  informationAt := eventPrefixStates
  informationAt_measurable :=
    measurable_eventPrefixStates

/-- Current-state information, forgetting the rest of the event prefix. -/
def latestState (A : MeasurableKernelArena) :
    EventInformation A where
  Information := fun _ => A.State
  informationMeasurable := fun _ => inferInstance
  informationAt := latestEventState
  informationAt_measurable :=
    measurable_latestEventState

/-- Forget actions from full event information. -/
def fullToStatePrefix (A : MeasurableKernelArena) :
    Hom (full A) (statePrefix A) where
  map := fun time => @eventPrefixStates A time
  map_measurable := fun time =>
    @measurable_eventPrefixStates A time
  map_informationAt := by
    intro time history
    rfl

/-- Forget a complete state prefix down to its latest state. -/
def statePrefixToLatestState (A : MeasurableKernelArena) :
    Hom (statePrefix A) (latestState A) where
  map := fun time => MeasurableKernelArena.latestState time
  map_measurable := measurable_latestState
  map_informationAt := by
    intro time history
    rfl

/-- Forget a complete event prefix directly down to its latest state. -/
def fullToLatestState (A : MeasurableKernelArena) :
    Hom (full A) (latestState A) :=
  (fullToStatePrefix A).trans
    (statePrefixToLatestState A)

/-- A legal normalized action policy indexed only by a fixed event-information
structure.

Well-formedness is required at every concrete prefix represented by an
information value. The kernel's behavior at information values outside the
image of `informationAt` is intentionally unconstrained. -/
structure ActionPolicy
    (information : EventInformation A) where
  /-- Measurable, possibly killed, action kernel at each information value. -/
  kernel :
    (time : ℕ) →
      Kernel (information.Information time) A.ActionBundle
  /-- Information represented by a terminal prefix has zero action mass. -/
  terminal_zero :
    ∀ time history,
      IsEmpty (A.Action (latestEventState time history)) →
        kernel time
          (information.informationAt time history) = 0
  /-- Information represented by a nonterminal prefix has normalized action
  mass. -/
  nonterminal_isProbability :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestEventState time history)) →
        IsProbabilityMeasure
          (kernel time
            (information.informationAt time history))
  /-- The action law at represented nonterminal information lies in the
  latest concrete state's dependent action fiber almost surely. -/
  legal :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestEventState time history)) →
        ∀ᵐ stateAction
            ∂kernel time
              (information.informationAt time history),
          stateAction ∈
            A.actionFiber (latestEventState time history)

/-- Information-indexed policies are equal when their kernel families are
equal. The well-formedness fields are propositions. -/
@[ext]
theorem ActionPolicy.ext
    {information : EventInformation A}
    {first second : ActionPolicy information}
    (hkernel : first.kernel = second.kernel) :
    first = second := by
  cases first
  cases second
  cases hkernel
  rfl

namespace ActionPolicy

variable
  {information : EventInformation A}
  {fine : EventInformation A}
  {coarse : EventInformation A}

/-- Compile an information-indexed policy to the raw complete-event-prefix
executor by measurable comap along the fixed information statistic. -/
def toEventHistoryActionPolicy
    (policy : ActionPolicy information) :
    A.EventHistoryActionPolicy where
  kernel := fun time =>
    Kernel.comap (policy.kernel time)
      (information.informationAt time)
      (information.informationAt_measurable time)
  terminal_zero := by
    intro time history hterminal
    change
      policy.kernel time
          (information.informationAt time history) = 0
    exact policy.terminal_zero time history hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    change
      IsProbabilityMeasure
        (policy.kernel time
          (information.informationAt time history))
    exact policy.nonterminal_isProbability
      time history hnonterminal
  legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂policy.kernel time
            (information.informationAt time history),
        stateAction ∈ A.actionFiber
          (latestEventState time history)
    exact policy.legal time history hnonterminal

@[simp]
theorem toEventHistoryActionPolicy_kernel_apply
    (policy : ActionPolicy information)
    (time : ℕ) (history : A.EventPrefix time) :
    policy.toEventHistoryActionPolicy.kernel time history =
      policy.kernel time
        (information.informationAt time history) :=
  rfl

/-- Equal information values force exactly equal compiled action measures.
This is the operational information-set-consistency theorem. -/
theorem compiled_kernel_eq_of_informationAt_eq
    (policy : ActionPolicy information)
    (time : ℕ) (history₁ history₂ : A.EventPrefix time)
    (hsame :
      information.informationAt time history₁ =
        information.informationAt time history₂) :
    policy.toEventHistoryActionPolicy.kernel time history₁ =
      policy.toEventHistoryActionPolicy.kernel time history₂ := by
  rw [toEventHistoryActionPolicy_kernel_apply,
    toEventHistoryActionPolicy_kernel_apply, hsame]

/-- A concrete action-bundle policy cannot merge two different nonterminal
latest states into one information value.

This is an important expressiveness boundary of `ActionPolicy`: its kernel
lands in `A.ActionBundle`, and legality requires mass one on the latest
state's concrete action fiber. If equal information forced the same measure
at two prefixes, that probability measure would be almost surely based at
both states, so the states must coincide.

In particular, a genuine imperfect-information behavioral strategy whose one
abstract action law is realized separately at distinct complete-history states
needs an additional history-dependent action-realization layer; it cannot in
general be encoded by this concrete-bundle interface alone. -/
theorem latestEventState_eq_of_informationAt_eq
    (policy : ActionPolicy information)
    (time : ℕ) (history₁ history₂ : A.EventPrefix time)
    (hnonterminal₁ :
      ¬ IsEmpty (A.Action (latestEventState time history₁)))
    (hnonterminal₂ :
      ¬ IsEmpty (A.Action (latestEventState time history₂)))
    (hsame :
      information.informationAt time history₁ =
        information.informationAt time history₂) :
    latestEventState time history₁ =
      latestEventState time history₂ := by
  let compiled := policy.toEventHistoryActionPolicy
  have hkernel :
      compiled.kernel time history₁ =
        compiled.kernel time history₂ :=
    policy.compiled_kernel_eq_of_informationAt_eq
      time history₁ history₂ hsame
  letI : IsProbabilityMeasure
      (compiled.kernel time history₁) :=
    compiled.nonterminal_isProbability
      time history₁ hnonterminal₁
  have hfirst :
      ∀ᵐ stateAction ∂compiled.kernel time history₁,
        stateAction ∈
          A.actionFiber (latestEventState time history₁) :=
    compiled.ae_mem_actionFiber
      time history₁ hnonterminal₁
  have hsecondAtSecond :
      ∀ᵐ stateAction ∂compiled.kernel time history₂,
        stateAction ∈
          A.actionFiber (latestEventState time history₂) :=
    compiled.ae_mem_actionFiber
      time history₂ hnonterminal₂
  have hsecond :
      ∀ᵐ stateAction ∂compiled.kernel time history₁,
        stateAction ∈
          A.actionFiber (latestEventState time history₂) := by
    rw [hkernel]
    exact hsecondAtSecond
  have heventually :
      ∀ᵐ _stateAction ∂compiled.kernel time history₁,
        latestEventState time history₁ =
          latestEventState time history₂ := by
    filter_upwards [hfirst, hsecond] with stateAction hbase₁ hbase₂
    change
      stateAction.1 = latestEventState time history₁ at hbase₁
    change
      stateAction.1 = latestEventState time history₂ at hbase₂
    exact hbase₁.symm.trans hbase₂
  obtain ⟨_, hstates⟩ := heventually.exists
  exact hstates

/-- Pull a coarse-information policy back to a finer information structure.
The pulled policy still depends only on the coarse statistic. -/
def pullback
    (policy : ActionPolicy coarse)
    (f : Hom fine coarse) :
    ActionPolicy fine where
  kernel := fun time =>
    Kernel.comap (policy.kernel time)
      (f.map time) (f.map_measurable time)
  terminal_zero := by
    intro time history hterminal
    change
      policy.kernel time
          (f.map time
            (fine.informationAt time history)) = 0
    rw [f.map_informationAt]
    exact policy.terminal_zero time history hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    change
      IsProbabilityMeasure
        (policy.kernel time
          (f.map time
            (fine.informationAt time history)))
    rw [f.map_informationAt]
    exact policy.nonterminal_isProbability
      time history hnonterminal
  legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂policy.kernel time
            (f.map time
              (fine.informationAt time history)),
        stateAction ∈
          A.actionFiber (latestEventState time history)
    rw [f.map_informationAt]
    exact policy.legal time history hnonterminal

@[simp]
theorem pullback_kernel_apply
    (policy : ActionPolicy coarse)
    (f : Hom fine coarse)
    (time : ℕ) (value : fine.Information time) :
    (policy.pullback f).kernel time value =
      policy.kernel time (f.map time value) :=
  rfl

@[simp]
theorem pullback_id
    (policy : ActionPolicy information) :
    policy.pullback (Hom.id information) = policy := by
  apply EventInformation.ActionPolicy.ext
  funext time
  apply Kernel.ext
  intro value
  rfl

theorem pullback_trans
    {middle : EventInformation A}
    (policy : ActionPolicy coarse)
    (f : Hom fine middle) (g : Hom middle coarse) :
    (policy.pullback g).pullback f =
      policy.pullback (f.trans g) := by
  apply EventInformation.ActionPolicy.ext
  funext time
  apply Kernel.ext
  intro value
  rfl

/-- Pullback along an information factor leaves the compiled raw event policy
exactly unchanged. -/
theorem pullback_toEventHistoryActionPolicy
    (policy : ActionPolicy coarse)
    (f : Hom fine coarse) :
    (policy.pullback f).toEventHistoryActionPolicy =
      policy.toEventHistoryActionPolicy := by
  apply EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro history
  change
    policy.kernel time
        (f.map time (fine.informationAt time history)) =
      policy.kernel time
        (coarse.informationAt time history)
  rw [f.map_informationAt]

/-- Pullback along an information factor preserves every stopped raw event
step kernel. -/
theorem pullback_pathStepKernel
    (policy : ActionPolicy coarse)
    (f : Hom fine coarse)
    (hterminal : MeasurableSet A.terminalSet)
    (time : ℕ) :
    (policy.pullback f).toEventHistoryActionPolicy.pathStepKernel
        hterminal time =
      policy.toEventHistoryActionPolicy.pathStepKernel
        hterminal time := by
  rw [pullback_toEventHistoryActionPolicy]

/-- Pullback along an information factor preserves the complete infinite
event-path probability measure. -/
theorem pullback_pathMeasure
    (policy : ActionPolicy coarse)
    (f : Hom fine coarse)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    (policy.pullback f).toEventHistoryActionPolicy.pathMeasure
        hterminal initialState =
      policy.toEventHistoryActionPolicy.pathMeasure
        hterminal initialState := by
  rw [pullback_toEventHistoryActionPolicy]

end ActionPolicy

end EventInformation

namespace EventHistoryActionPolicy

/-- Regard a raw event-history policy as a full-information policy. -/
def toFullInformationActionPolicy
    (policy : A.EventHistoryActionPolicy) :
    EventInformation.ActionPolicy
      (EventInformation.full A) where
  kernel := policy.kernel
  terminal_zero := policy.terminal_zero
  nonterminal_isProbability :=
    policy.nonterminal_isProbability
  legal := policy.legal

/-- Compiling the full-information representation recovers the raw
event-history policy exactly. -/
theorem toFullInformationActionPolicy_toEventHistoryActionPolicy
    (policy : A.EventHistoryActionPolicy) :
    EventInformation.ActionPolicy.toEventHistoryActionPolicy
        policy.toFullInformationActionPolicy =
      policy := by
  apply EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro history
  rfl

/-- Full-information representation preserves the complete infinite raw event
path law exactly. -/
theorem toFullInformationActionPolicy_pathMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    (EventInformation.ActionPolicy.toEventHistoryActionPolicy
      policy.toFullInformationActionPolicy).pathMeasure
        hterminal initialState =
      policy.pathMeasure hterminal initialState := by
  rw [toFullInformationActionPolicy_toEventHistoryActionPolicy]

end EventHistoryActionPolicy

namespace HistoryActionPolicy

/-- Regard a finite-state-prefix policy as a policy on the fixed state-prefix
information structure. -/
def toStatePrefixInformationActionPolicy
    (policy : A.HistoryActionPolicy) :
    EventInformation.ActionPolicy
      (EventInformation.statePrefix A) where
  kernel := policy.kernel
  terminal_zero := by
    intro time history hterminal
    exact policy.terminal_zero time
      (eventPrefixStates time history) hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    exact policy.nonterminal_isProbability time
      (eventPrefixStates time history) hnonterminal
  legal := by
    intro time history hnonterminal
    exact policy.legal time
      (eventPrefixStates time history) hnonterminal

/-- The state-prefix information representation compiles to the existing
state-history embedding exactly. -/
theorem toStatePrefixInformationActionPolicy_toEventHistoryActionPolicy
    (policy : A.HistoryActionPolicy) :
    EventInformation.ActionPolicy.toEventHistoryActionPolicy
        policy.toStatePrefixInformationActionPolicy =
      policy.toEventHistoryActionPolicy := by
  apply EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro history
  rfl

/-- The state-prefix information representation recovers the complete
original infinite state-history path law after forgetting recorded actions.
-/
theorem toStatePrefixInformationActionPolicy_statePathMeasure
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    (EventInformation.ActionPolicy.toEventHistoryActionPolicy
      policy.toStatePrefixInformationActionPolicy).statePathMeasure
        hterminal initialState =
      policy.pathMeasure hterminal initialState := by
  rw [
    toStatePrefixInformationActionPolicy_toEventHistoryActionPolicy]
  exact policy.toEventHistoryActionPolicy_statePathMeasure
    hterminal initialState

end HistoryActionPolicy

namespace ActionPolicy

/-- Regard a stationary state-Markov policy as a policy on the fixed
latest-state information structure. -/
def toLatestStateInformationActionPolicy
    (policy : A.ActionPolicy) :
    EventInformation.ActionPolicy
      (EventInformation.latestState A) where
  kernel := fun _ => policy.kernel
  terminal_zero := by
    intro time history hterminal
    exact policy.terminal_zero
      (latestEventState time history) hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    exact policy.nonterminal_isProbability
      (latestEventState time history) hnonterminal
  legal := by
    intro time history hnonterminal
    exact policy.legal
      (latestEventState time history) hnonterminal

/-- The latest-state information representation compiles to the existing
stationary-through-state-history embedding exactly. -/
theorem toLatestStateInformationActionPolicy_toEventHistoryActionPolicy
    (policy : A.ActionPolicy) :
    EventInformation.ActionPolicy.toEventHistoryActionPolicy
        policy.toLatestStateInformationActionPolicy =
      policy.toHistoryActionPolicy.toEventHistoryActionPolicy := by
  apply EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro history
  rfl

/-- The latest-state information representation recovers the original
stationary infinite state-path law after forgetting recorded actions. -/
theorem toLatestStateInformationActionPolicy_statePathMeasure
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [PathExecution policy hterminal]
    (initialState : A.State) :
    (EventInformation.ActionPolicy.toEventHistoryActionPolicy
      policy.toLatestStateInformationActionPolicy).statePathMeasure
        hterminal initialState =
      policy.pathMeasure hterminal initialState := by
  rw [
    toLatestStateInformationActionPolicy_toEventHistoryActionPolicy]
  rw [
    HistoryActionPolicy.toEventHistoryActionPolicy_statePathMeasure]
  exact policy.toHistoryActionPolicy_pathMeasure
    hterminal initialState

end ActionPolicy

end MeasurableKernelArena
