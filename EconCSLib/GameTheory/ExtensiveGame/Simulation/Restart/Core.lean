/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed

/-!
# Restart.Core — root normalization and splicing

This implementation module contains the representation-level operations
used by fresh-restart compatibility: initial-event normalization, canonical
root replacement, measurable full-path and finite-prefix splicing, and their
pointwise identities.  It introduces no equilibrium or observed-profile
semantics.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- Replace only event-path coordinate zero by the distinguished
no-incoming-action event at the same state. -/
def freshenInitialEvent
    (path : ℕ → A.PathEvent) :
    ℕ → A.PathEvent :=
  fun time =>
    if time = 0 then
      A.initialEvent (path 0).state
    else
      path time

/-- Normalizing the initial action marker is measurable. -/
theorem measurable_freshenInitialEvent :
    Measurable (freshenInitialEvent (A := A)) := by
  apply measurable_pi_lambda
  intro time
  by_cases htime : time = 0
  · subst time
    simpa [freshenInitialEvent] using
      A.measurable_initialEvent.comp
        (PathEvent.measurable_state.comp
          (measurable_pi_apply 0))
  · simpa [freshenInitialEvent, htime] using
      (measurable_pi_apply time :
        Measurable
          (fun path : ℕ → A.PathEvent => path time))

/-- Initial-action normalization does not alter any state coordinate. -/
@[simp]
theorem eventPathStates_freshenInitialEvent
    (path : ℕ → A.PathEvent) :
    eventPathStates (freshenInitialEvent path) =
      eventPathStates path := by
  funext time
  by_cases htime : time = 0
  · subst time
    rfl
  · simp [eventPathStates, freshenInitialEvent, htime]

/-- Replace coordinate zero by the distinguished initial event of a fixed
state, leaving every positive coordinate unchanged. -/
def setInitialEvent
    (initialState : A.State)
    (path : ℕ → A.PathEvent) :
    ℕ → A.PathEvent :=
  fun time =>
    if time = 0 then
      A.initialEvent initialState
    else
      path time

/-- Fixed-root initial-event replacement is measurable. -/
theorem measurable_setInitialEvent
    (initialState : A.State) :
    Measurable (setInitialEvent (A := A) initialState) := by
  apply measurable_pi_lambda
  intro time
  by_cases htime : time = 0
  · subst time
    simp [setInitialEvent]
  · simpa [setInitialEvent, htime] using
      (measurable_pi_apply time :
        Measurable
          (fun path : ℕ → A.PathEvent => path time))

/-- Replace finite-prefix coordinate zero by the distinguished initial event
of a fixed state, leaving every positive coordinate unchanged. -/
def setInitialPrefix
    (initialState : A.State)
    (offset : ℕ)
    (finitePrefix : A.ContinuationPrefix offset) :
    A.ContinuationPrefix offset :=
  fun time =>
    if time.1 = 0 then
      A.initialEvent initialState
    else
      finitePrefix time

/-- Fixed-root replacement of a finite prefix is measurable. -/
theorem measurable_setInitialPrefix
    (initialState : A.State)
    (offset : ℕ) :
    Measurable
      (setInitialPrefix (A := A) initialState offset) := by
  apply measurable_pi_lambda
  intro time
  by_cases htime : time.1 = 0
  · simp [setInitialPrefix, htime]
  · simpa [setInitialPrefix, htime] using
      (measurable_pi_apply time :
        Measurable
          (fun finitePrefix : A.ContinuationPrefix offset =>
            finitePrefix time))

/-- Fixed-root replacement of a finite prefix is idempotent. -/
@[simp]
theorem setInitialPrefix_idempotent
    (initialState : A.State)
    (offset : ℕ)
    (finitePrefix : A.ContinuationPrefix offset) :
    setInitialPrefix initialState offset
        (setInitialPrefix initialState offset finitePrefix) =
      setInitialPrefix initialState offset finitePrefix := by
  funext time
  by_cases htime : time.1 = 0
  · simp [setInitialPrefix, htime]
  · simp [setInitialPrefix, htime]

/-- Finite fixed-root replacement commutes with restriction of the
corresponding full-path replacement. -/
theorem setInitialPrefix_frestrictLe_setInitialEvent
    (initialState : A.State)
    (offset : ℕ)
    (path : ℕ → A.PathEvent) :
    setInitialPrefix initialState offset
        (frestrictLe offset path) =
      frestrictLe offset
        (setInitialEvent initialState path) := by
  funext time
  by_cases htime : time.1 = 0
  · simp [
      setInitialPrefix,
      setInitialEvent,
      htime]
  · simp [
      setInitialPrefix,
      setInitialEvent,
      htime]

/-- A finite prefix is canonically rooted at `initialState` when resetting
coordinate zero to that state's distinguished initial event changes
nothing. -/
def IsInitialEventRootedPrefix
    (initialState : A.State)
    (offset : ℕ)
    (finitePrefix : A.ContinuationPrefix offset) :
    Prop :=
  setInitialPrefix initialState offset finitePrefix =
    finitePrefix

/-- Resetting coordinate zero always produces a canonically rooted prefix. -/
theorem isInitialEventRootedPrefix_setInitialPrefix
    (initialState : A.State)
    (offset : ℕ)
    (finitePrefix : A.ContinuationPrefix offset) :
    IsInitialEventRootedPrefix
      initialState offset
      (setInitialPrefix initialState offset finitePrefix) := by
  unfold IsInitialEventRootedPrefix
  exact
    setInitialPrefix_idempotent
      initialState offset finitePrefix

/-- Splice a fresh-clock full event path after a retained absolute prefix.

Coordinates through `start` come from `initialPrefix`. At every strictly
later absolute coordinate `time`, the event comes from fresh coordinate
`time - start`; in particular the first new event is fresh coordinate one.
-/
def spliceContinuationPath
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent) :
    ℕ → A.PathEvent :=
  fun time =>
    if htime : time ≤ start then
      initialPrefix
        ⟨time, Finset.mem_Iic.mpr htime⟩
    else
      freshPath (time - start)

/-- Splicing is measurable as a function of the fresh future path. -/
theorem measurable_spliceContinuationPath
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Measurable
      (spliceContinuationPath start initialPrefix) := by
  apply measurable_pi_lambda
  intro time
  by_cases htime : time ≤ start
  · simp [spliceContinuationPath, htime]
  · simpa [spliceContinuationPath, htime] using
      (measurable_pi_apply (time - start) :
        Measurable
          (fun path : ℕ → A.PathEvent =>
            path (time - start)))

/-- Splicing preserves every coordinate of the retained absolute prefix. -/
@[simp]
theorem spliceContinuationPath_of_le
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent)
    (time : ℕ)
    (htime : time ≤ start) :
    spliceContinuationPath
        start initialPrefix freshPath time =
      initialPrefix
        ⟨time, Finset.mem_Iic.mpr htime⟩ := by
  simp [spliceContinuationPath, htime]

/-- At the splice time itself, the absolute prefix's latest event is
retained. -/
@[simp]
theorem spliceContinuationPath_add_zero
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent) :
    spliceContinuationPath
        start initialPrefix freshPath (start + 0) =
      latestEvent start initialPrefix := by
  simp [
    spliceContinuationPath,
    latestEvent]

/-- Every strictly future absolute coordinate is the corresponding positive
fresh coordinate. -/
@[simp]
theorem spliceContinuationPath_add_succ
    (start offset : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent) :
    spliceContinuationPath
        start initialPrefix freshPath
        (start + offset.succ) =
      freshPath offset.succ := by
  simp [
    spliceContinuationPath]

/-- Restricting a spliced path through the continuation time recovers the
supplied absolute prefix exactly. -/
@[simp]
theorem frestrictLe_spliceContinuationPath
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent) :
    frestrictLe start
        (spliceContinuationPath
          start initialPrefix freshPath) =
      initialPrefix := by
  funext time
  exact
    spliceContinuationPath_of_le
      start initialPrefix freshPath
      time (Finset.mem_Iic.mp time.2)

/-- Finite-prefix form of `spliceContinuationPath`: retain the complete
absolute prefix through `start`, then attach positive coordinates from a
fresh prefix through `offset`. -/
def spliceContinuationPrefix
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix offset) :
    A.ContinuationPrefix (start + offset) :=
  fun time =>
    if htime : time.1 ≤ start then
      initialPrefix
        ⟨time.1, Finset.mem_Iic.mpr htime⟩
    else
      freshPrefix
        ⟨time.1 - start, Finset.mem_Iic.mpr (by
          have habsolute :
              time.1 ≤ start + offset :=
            Finset.mem_Iic.mp time.2
          omega)⟩

/-- The finite splice is measurable as a function of its fresh prefix. -/
theorem measurable_spliceContinuationPrefix
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    Measurable
      (spliceContinuationPrefix
        start initialPrefix offset) := by
  apply measurable_pi_lambda
  intro time
  by_cases htime : time.1 ≤ start
  · simp [spliceContinuationPrefix, htime]
  · simpa [spliceContinuationPrefix, htime] using
      (measurable_pi_apply
        (⟨time.1 - start,
          Finset.mem_Iic.mpr (by
            have habsolute :
                time.1 ≤ start + offset :=
              Finset.mem_Iic.mp time.2
            omega)⟩ :
          Finset.Iic offset) :
        Measurable
          (fun freshPrefix :
              A.ContinuationPrefix offset =>
            freshPrefix
              ⟨time.1 - start,
                Finset.mem_Iic.mpr (by
                  have habsolute :
                      time.1 ≤ start + offset :=
                    Finset.mem_Iic.mp time.2
                  omega)⟩))

/-- A finite splice is exactly restriction of the corresponding full splice.
-/
theorem spliceContinuationPrefix_frestrictLe
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPath : ℕ → A.PathEvent) :
    spliceContinuationPrefix
        start initialPrefix offset
        (frestrictLe offset freshPath) =
      frestrictLe (start + offset)
        (spliceContinuationPath
          start initialPrefix freshPath) := by
  funext time
  by_cases htime : time.1 ≤ start
  · simp [
      spliceContinuationPrefix,
      spliceContinuationPath,
      htime]
  · simp [
      spliceContinuationPrefix,
      spliceContinuationPath,
      htime]

/-- At offset zero, finite splicing forgets the fresh restart marker and
returns exactly the retained absolute prefix. -/
@[simp]
theorem spliceContinuationPrefix_zero
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPrefix : A.ContinuationPrefix 0) :
    spliceContinuationPrefix
        start initialPrefix 0 freshPrefix =
      initialPrefix := by
  funext time
  have htime : time.1 ≤ start := by
    have := Finset.mem_Iic.mp time.2
    simpa using this
  simp [
    spliceContinuationPrefix,
    htime]

/-- Extend a finite continuation prefix by one event. This is the
point-valued counterpart of Mathlib's successor `partialTraj` kernel. -/
def appendContinuationEvent
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time)
    (event : A.PathEvent) :
    A.ContinuationPrefix (time + 1) :=
  IicProdIoc
    (X := fun _ => A.PathEvent)
    time (time + 1)
    (finitePrefix,
      (MeasurableEquiv.piSingleton
        (X := fun _ => A.PathEvent)
        time) event)

/-- Appending an event to a fixed finite prefix is measurable. -/
theorem measurable_appendContinuationEvent
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time) :
    Measurable
      (appendContinuationEvent time finitePrefix) := by
  exact
    measurable_IicProdIoc.comp
      (measurable_const.prodMk
        (MeasurableEquiv.piSingleton
          (X := fun _ => A.PathEvent)
          time).measurable)

/-- Finite splicing commutes with adjoining one new event. Although
`EventAt` carries a clock index, it is definitionally the same measurable
`PathEvent` type at every time, so no event-value transport is needed. -/
theorem spliceContinuationPrefix_IicProdIoc_piSingleton
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix offset)
    (event : A.PathEvent) :
    spliceContinuationPrefix
        start initialPrefix (offset + 1)
        (IicProdIoc
          (X := fun _ => A.PathEvent)
          offset (offset + 1)
          (freshPrefix,
            (MeasurableEquiv.piSingleton
              (X := fun _ => A.PathEvent)
              offset) event)) =
      IicProdIoc
        (X := fun _ => A.PathEvent)
        (start + offset) ((start + offset) + 1)
        (spliceContinuationPrefix
            start initialPrefix offset freshPrefix,
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.PathEvent)
            (start + offset)) event) := by
  funext time
  by_cases hstart : time.1 ≤ start
  · have habsolute : time.1 ≤ start + offset := by
      omega
    simp [
      spliceContinuationPrefix,
      IicProdIoc,
      hstart,
      habsolute]
  · by_cases habsolute : time.1 ≤ start + offset
    · have hfresh : time.1 - start ≤ offset := by
        omega
      simp [
        spliceContinuationPrefix,
        IicProdIoc,
        hstart,
        habsolute,
        hfresh]
    · have htime :
          time.1 = (start + offset) + 1 := by
        have hupper :
            time.1 ≤ (start + offset) + 1 :=
          Finset.mem_Iic.mp time.2
        omega
      simp [
        spliceContinuationPrefix,
        IicProdIoc,
        htime,
        MeasurableEquiv.piSingleton,
        Nat.add_comm]

/-- Conceptual form of
`spliceContinuationPrefix_IicProdIoc_piSingleton`: finite splicing commutes
with the one-event prefix extension map. -/
theorem spliceContinuationPrefix_appendContinuationEvent
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix offset)
    (event : A.PathEvent) :
    spliceContinuationPrefix
        start initialPrefix (offset + 1)
        (appendContinuationEvent
          offset freshPrefix event) =
      appendContinuationEvent
        (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)
        event :=
  spliceContinuationPrefix_IicProdIoc_piSingleton
    start initialPrefix offset freshPrefix event

/-- The newest event of a positive-horizon finite splice is exactly the
newest event of the fresh prefix. -/
@[simp]
theorem latestEvent_spliceContinuationPrefix_add_succ
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix (offset + 1)) :
    latestEvent ((start + offset) + 1)
        (spliceContinuationPrefix
          start initialPrefix (offset + 1)
          freshPrefix) =
      latestEvent (offset + 1) freshPrefix := by
  simp [
    latestEvent,
    spliceContinuationPrefix]
  apply congrArg freshPrefix
  apply Subtype.ext
  simp [Nat.add_assoc]

/-- A finite splice and its canonically rooted fresh prefix have the same
latest state. The rooted premise is needed only at offset zero; at positive
offsets the newest spliced event is already a fresh event. -/
theorem latestEventState_spliceContinuationPrefix_eq_of_rooted
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix offset)
    (hrooted :
      IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix) :
    latestEventState (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix) =
      latestEventState offset freshPrefix := by
  cases offset with
  | zero =>
      change
        latestEventState start
            (spliceContinuationPrefix
              start initialPrefix 0 freshPrefix) =
          latestEventState 0 freshPrefix
      rw [spliceContinuationPrefix_zero]
      unfold IsInitialEventRootedPrefix at hrooted
      have hlatest :=
        congrArg (latestEventState 0) hrooted
      simpa [
        latestEventState,
        latestEvent,
        setInitialPrefix] using hlatest
  | succ offset =>
      change
        (latestEvent ((start + offset) + 1)
          (spliceContinuationPrefix
            start initialPrefix (offset + 1)
            freshPrefix)).state =
          (latestEvent (offset + 1) freshPrefix).state
      exact
        congrArg PathEvent.state
          (latestEvent_spliceContinuationPrefix_add_succ
            start initialPrefix offset freshPrefix)

/-- Tail-shifting a splice and normalizing its coordinate-zero occurrence is
exactly fixed-root initial-event replacement on the fresh path. -/
theorem freshenInitialEvent_tailEventPath_spliceContinuationPath
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (freshPath : ℕ → A.PathEvent) :
    freshenInitialEvent
        (EventHistoryActionPolicy.tailEventPath start
          (spliceContinuationPath
            start initialPrefix freshPath)) =
      setInitialEvent
        (latestEventState start initialPrefix)
        freshPath := by
  funext offset
  cases offset with
  | zero =>
      simp [
        freshenInitialEvent,
        setInitialEvent,
        EventHistoryActionPolicy.tailEventPath,
        spliceContinuationPath,
        latestEvent,
        latestEventState]
  | succ offset =>
      simp [
        freshenInitialEvent,
        setInitialEvent,
        EventHistoryActionPolicy.tailEventPath]

end MeasurableKernelArena
