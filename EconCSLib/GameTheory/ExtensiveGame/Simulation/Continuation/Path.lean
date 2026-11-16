/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath

/-!
# Continuation.Path — absolute-prefix paths for measurable kernel arenas

`EventHistoryActionPolicy.pathMeasure` starts at event time zero from one
state. A genuine continuation of a time-inhomogeneous, event-history-dependent
policy must instead retain both:

* the absolute starting time `start`;
* the complete joint state/action `EventPrefix start`.

This module starts Mathlib's Ionescu--Tulcea trajectory at exactly that
prefix. The resulting full path remains indexed by absolute time, so every
future policy kernel sees the original prefix and the original clock.
Tail-indexed event and state laws are then obtained by the measurable shift
`offset ↦ start + offset`.

No conditioning claim is made. These are constructive continuations from an
explicit supplied prefix, including prefixes whose probability under another
law may be zero.
-/

open MeasureTheory ProbabilityTheory

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- A complete absolute-time event prefix through `start`. -/
abbrev ContinuationPrefix
    (A : MeasurableKernelArena)
    (start : ℕ) :=
  Π index : Finset.Iic start, EventAt A index

namespace EventHistoryActionPolicy

/-- Full absolute-time event-path law continued from a supplied complete
event prefix. -/
noncomputable def absolutePathMeasureFromPrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Measure (ℕ → A.PathEvent) :=
  Kernel.traj
    (policy.pathStepKernel hterminal)
    start initialPrefix

/-- The absolute continuation law is a probability measure. -/
instance absolutePathMeasureFromPrefix_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    IsProbabilityMeasure
      (policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix) := by
  unfold absolutePathMeasureFromPrefix
  infer_instance

/-- The full prefix marginal through the continuation time is exactly the
supplied prefix. -/
theorem absolutePathMeasureFromPrefix_map_frestrictLe
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix).map
        (Preorder.frestrictLe start) =
      Measure.dirac initialPrefix := by
  rw [
    absolutePathMeasureFromPrefix,
    Kernel.traj_map_frestrictLe_apply,
    Kernel.partialTraj_self,
    Kernel.id_apply]

/-- Reindex a full absolute-time event path by offsets from `start`. -/
def tailEventPath
    (start : ℕ)
    (path : ℕ → A.PathEvent) :
    ℕ → A.PathEvent :=
  fun offset => path (start + offset)

/-- Reindexing a measurable event path by a fixed time shift is measurable.
-/
theorem measurable_tailEventPath
    (start : ℕ) :
    Measurable (tailEventPath (A := A) start) := by
  exact measurable_pi_lambda _ fun offset =>
    measurable_pi_apply (start + offset)

/-- Absolute continuation law viewed as a future event path whose coordinate
zero is the latest event of the supplied prefix. -/
noncomputable def tailEventPathMeasureFromPrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Measure (ℕ → A.PathEvent) :=
  (policy.absolutePathMeasureFromPrefix
    hterminal start initialPrefix).map
      (tailEventPath start)

/-- The tail event continuation law is a probability measure. -/
instance tailEventPathMeasureFromPrefix_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    IsProbabilityMeasure
      (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix) := by
  rw [tailEventPathMeasureFromPrefix]
  exact
    Measure.isProbabilityMeasure_map
      (measurable_tailEventPath (A := A) start).aemeasurable

/-- Coordinate zero of the tail event law is exactly the latest supplied
event. -/
@[simp]
theorem tailEventPathMeasureFromPrefix_coordinate_zero
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => path 0) =
      Measure.dirac
        (latestEvent start initialPrefix) := by
  rw [tailEventPathMeasureFromPrefix]
  rw [Measure.map_map
    (measurable_pi_apply 0)
    (measurable_tailEventPath (A := A) start)]
  have hevaluation :
      (fun path : ℕ → A.PathEvent => path 0) ∘
          tailEventPath start =
        latestEvent start ∘
          Preorder.frestrictLe start := by
    rfl
  rw [hevaluation]
  rw [← Measure.map_map
    (measurable_latestEvent start)
    (by fun_prop :
      Measurable
        (Preorder.frestrictLe start :
          (ℕ → A.PathEvent) →
            A.ContinuationPrefix start))]
  rw [
    policy.absolutePathMeasureFromPrefix_map_frestrictLe
      hterminal start initialPrefix,
    Measure.map_dirac' (measurable_latestEvent start)]

/-- Coordinate one of the tail law is exactly the absolute-time path-step
kernel evaluated at the complete supplied prefix.

In particular, the first continuation action is selected by the policy
component at time `start`, not by its time-zero component. -/
theorem tailEventPathMeasureFromPrefix_coordinate_one
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => path 1) =
      policy.pathStepKernel hterminal start initialPrefix := by
  rw [tailEventPathMeasureFromPrefix]
  rw [Measure.map_map
    (measurable_pi_apply 1)
    (measurable_tailEventPath (A := A) start)]
  change
    (policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path : ℕ → A.PathEvent =>
          path (start + 1)) =
      policy.pathStepKernel hterminal start initialPrefix
  unfold absolutePathMeasureFromPrefix
  rw [← Kernel.map_apply _
    (measurable_pi_apply (start + 1))]
  rw [Kernel.map_traj_succ_self]

/-- At a nonterminal supplied prefix, the action recorded in tail coordinate
one has exactly the absolute-time policy law, tagged as an incoming action
occurrence. -/
theorem tailEventPathMeasureFromPrefix_coordinate_one_action
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (hnonterminal :
      ¬ IsEmpty
        (A.Action
      (latestEventState start initialPrefix))) :
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => (path 1).action) =
      (policy.kernel start initialPrefix).map Sum.inr := by
  change
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        ((@PathEvent.action A) ∘
          (fun path : ℕ → A.PathEvent => path 1)) =
      (policy.kernel start initialPrefix).map Sum.inr
  rw [← Measure.map_map
    (@PathEvent.measurable_action A)
    (measurable_pi_apply 1 :
      Measurable
        (fun path : ℕ → A.PathEvent => path 1))]
  rw [
    policy.tailEventPathMeasureFromPrefix_coordinate_one
      hterminal start initialPrefix]
  rw [
    policy.pathStepKernel_apply_nonterminal
      hterminal start initialPrefix hnonterminal]
  change
    (policy.actionStepKernel start initialPrefix).map
        PathEvent.action =
      (policy.kernel start initialPrefix).map Sum.inr
  have hmap :=
    congrArg
      (fun kernel => kernel initialPrefix)
      (policy.actionStepKernel_map_action start)
  simpa only [
    Kernel.map_apply
      (policy.actionStepKernel start)
      PathEvent.measurable_action,
    Kernel.map_apply
      (policy.kernel start)
      measurable_inr] using hmap

/-- Forget recorded actions from the tail event continuation law. -/
noncomputable def tailStatePathMeasureFromPrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Measure (ℕ → A.State) :=
  (policy.tailEventPathMeasureFromPrefix
    hterminal start initialPrefix).map
      eventPathStates

/-- The tail state continuation law is a probability measure. -/
instance tailStatePathMeasureFromPrefix_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    IsProbabilityMeasure
      (policy.tailStatePathMeasureFromPrefix
        hterminal start initialPrefix) := by
  rw [tailStatePathMeasureFromPrefix]
  exact
    Measure.isProbabilityMeasure_map
      measurable_eventPathStates.aemeasurable

/-- Coordinate zero of the tail state law is exactly the latest state of the
supplied absolute prefix. -/
@[simp]
theorem tailStatePathMeasureFromPrefix_coordinate_zero
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.tailStatePathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => path 0) =
      Measure.dirac
        (latestEventState start initialPrefix) := by
  rw [tailStatePathMeasureFromPrefix]
  rw [Measure.map_map
    (measurable_pi_apply 0)
    measurable_eventPathStates]
  change
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        (PathEvent.state ∘
          (fun path : ℕ → A.PathEvent => path 0)) =
      Measure.dirac
        (latestEventState start initialPrefix)
  calc
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        ((@PathEvent.state A) ∘
          (fun path : ℕ → A.PathEvent => path 0)) =
      ((policy.tailEventPathMeasureFromPrefix
          hterminal start initialPrefix).map
          (fun path : ℕ → A.PathEvent => path 0)).map
        (@PathEvent.state A) := by
      rw [Measure.map_map
        (@PathEvent.measurable_state A)
        (measurable_pi_apply 0)]
    _ =
      (Measure.dirac
        (latestEvent start initialPrefix)).map
          (@PathEvent.state A) := by
      rw [
        policy.tailEventPathMeasureFromPrefix_coordinate_zero
          hterminal start initialPrefix]
    _ = Measure.dirac
        (latestEventState start initialPrefix) := by
      rw [
        Measure.map_dirac'
          (@PathEvent.measurable_state A)]
      rfl

/-- Coordinate one of the tail state law is the state projection of the
absolute-time path-step kernel at the complete supplied prefix. -/
theorem tailStatePathMeasureFromPrefix_coordinate_one
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.tailStatePathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => path 1) =
      (policy.pathStepKernel
        hterminal start initialPrefix).map
          PathEvent.state := by
  rw [tailStatePathMeasureFromPrefix]
  rw [Measure.map_map
    (measurable_pi_apply 1)
    measurable_eventPathStates]
  change
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
        ((@PathEvent.state A) ∘
          (fun path : ℕ → A.PathEvent => path 1)) =
      (policy.pathStepKernel
        hterminal start initialPrefix).map
          PathEvent.state
  rw [← Measure.map_map
    (@PathEvent.measurable_state A)
    (measurable_pi_apply 1 :
      Measurable
        (fun path : ℕ → A.PathEvent => path 1))]
  rw [
    policy.tailEventPathMeasureFromPrefix_coordinate_one
      hterminal start initialPrefix]

/-- At a nonterminal supplied prefix, tail state coordinate one is the arena
transition integrated against the absolute-time action law. -/
theorem tailStatePathMeasureFromPrefix_coordinate_one_of_nonterminal
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (hnonterminal :
      ¬ IsEmpty
        (A.Action
          (latestEventState start initialPrefix))) :
    (policy.tailStatePathMeasureFromPrefix
        hterminal start initialPrefix).map
        (fun path => path 1) =
      A.transition ∘ₘ
        policy.kernel start initialPrefix := by
  rw [
    policy.tailStatePathMeasureFromPrefix_coordinate_one
      hterminal start initialPrefix]
  rw [
    policy.pathStepKernel_apply_nonterminal
      hterminal start initialPrefix hnonterminal]
  change
    (policy.actionStepKernel start initialPrefix).map
        PathEvent.state =
      A.transition ∘ₘ
        policy.kernel start initialPrefix
  have hmap :=
    congrArg
      (fun kernel => kernel initialPrefix)
      (policy.actionStepKernel_map_state start)
  simpa only [
    Kernel.map_apply
      (policy.actionStepKernel start)
      PathEvent.measurable_state,
    Kernel.comp_apply] using hmap

end EventHistoryActionPolicy

end MeasurableKernelArena
