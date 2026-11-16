/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Core

/-!
# Restart.Trajectory — spliced trajectory laws

This implementation module builds the raw policy-level spliced path law,
its finite marginals, and the exact one-step trajectory identities used by
restart certificates.  The declarations remain in
`MeasurableKernelArena.EventHistoryActionPolicy`.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

namespace EventHistoryActionPolicy

/-- A time-zero event path law is invariant under resetting coordinate zero
to its already-fixed initial event. -/
theorem pathMeasure_map_setInitialEvent
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    (policy.pathMeasure
        hterminal initialState).map
          (setInitialEvent initialState) =
      policy.pathMeasure
        hterminal initialState := by
  have hset :
      setInitialEvent (A := A) initialState =
        (fun path =>
          Function.updateFinset path (Finset.Iic 0)
            (fun _ => A.initialEvent initialState)) := by
    funext path time
    by_cases htime : time = 0
    · subst time
      simp [setInitialEvent, Function.updateFinset]
    · simp [
        setInitialEvent,
        Function.updateFinset,
        htime]
  rw [hset]
  unfold pathMeasure
  exact
    Kernel.traj_map_updateFinset
      (κ := policy.pathStepKernel hterminal)
      (fun _ => A.initialEvent initialState)

/-- Full absolute-coordinate law obtained by splicing a time-zero fresh path
after a retained complete prefix. -/
noncomputable def splicedFreshAbsolutePathMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Measure (ℕ → A.PathEvent) :=
  (policy.pathMeasure
    hterminal
    (latestEventState start initialPrefix)).map
      (spliceContinuationPath start initialPrefix)

/-- The spliced fresh law is a probability measure. -/
instance splicedFreshAbsolutePathMeasure_isProbability
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    IsProbabilityMeasure
      (policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix) := by
  unfold splicedFreshAbsolutePathMeasure
  exact
    Measure.isProbabilityMeasure_map
      (measurable_spliceContinuationPath
        start initialPrefix).aemeasurable

/-- The spliced law has exactly the supplied retained-prefix marginal. -/
theorem splicedFreshAbsolutePathMeasure_map_frestrictLe
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    (policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix).map
          (frestrictLe start) =
      Measure.dirac initialPrefix := by
  unfold splicedFreshAbsolutePathMeasure
  rw [
    Measure.map_map
      (measurable_frestrictLe start)
      (measurable_spliceContinuationPath
        start initialPrefix)]
  have hconstant :
      frestrictLe start ∘
          spliceContinuationPath start initialPrefix =
        (fun _path : ℕ → A.PathEvent =>
          initialPrefix) := by
    funext freshPath
    exact
      frestrictLe_spliceContinuationPath
        start initialPrefix freshPath
  rw [hconstant, Measure.map_const]
  simp

/-- After tail-shifting and normalizing the root occurrence, the spliced law
is exactly the original fresh-clock event-path law. -/
theorem splicedFreshAbsolutePathMeasure_map_tail_freshen
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    ((policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix).map
          (tailEventPath start)).map
            freshenInitialEvent =
      policy.pathMeasure hterminal
        (latestEventState start initialPrefix) := by
  unfold splicedFreshAbsolutePathMeasure
  rw [
    Measure.map_map
      measurable_freshenInitialEvent
      (measurable_tailEventPath (A := A) start),
    Measure.map_map
      (measurable_freshenInitialEvent.comp
        (measurable_tailEventPath (A := A) start))
      (measurable_spliceContinuationPath
        start initialPrefix)]
  have hcomposition :
      (freshenInitialEvent ∘
          tailEventPath start) ∘
          spliceContinuationPath start initialPrefix =
        setInitialEvent
          (latestEventState start initialPrefix) := by
    funext freshPath
    exact
      freshenInitialEvent_tailEventPath_spliceContinuationPath
        start initialPrefix freshPath
  rw [
    hcomposition,
    policy.pathMeasure_map_setInitialEvent]

/-- If the actual absolute trajectory is the spliced fresh trajectory, then
its normalized tail law is the fresh-clock event law. -/
theorem tailEventPathMeasureFromPrefix_map_freshen_eq_pathMeasure_of_eq_spliced
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (htrajectory :
      policy.absolutePathMeasureFromPrefix
          hterminal start initialPrefix =
        policy.splicedFreshAbsolutePathMeasure
          hterminal start initialPrefix) :
    (policy.tailEventPathMeasureFromPrefix
        hterminal start initialPrefix).map
          freshenInitialEvent =
      policy.pathMeasure hterminal
        (latestEventState start initialPrefix) := by
  unfold tailEventPathMeasureFromPrefix
  rw [
    htrajectory,
    policy.splicedFreshAbsolutePathMeasure_map_tail_freshen]

/-- Finite absolute-coordinate marginal of the actual absolute trajectory. -/
noncomputable def absoluteFinitePrefixMeasureFromPrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (horizon : ℕ) :
    Measure (A.ContinuationPrefix horizon) :=
  (policy.absolutePathMeasureFromPrefix
    hterminal start initialPrefix).map
      (frestrictLe horizon)

/-- Finite absolute-coordinate marginal of the spliced fresh trajectory. -/
noncomputable def splicedFreshFinitePrefixMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (horizon : ℕ) :
    Measure (A.ContinuationPrefix horizon) :=
  (policy.splicedFreshAbsolutePathMeasure
    hterminal start initialPrefix).map
      (frestrictLe horizon)

/-- Fresh-clock finite event-prefix law through `offset`, rooted at the
latest state of the retained absolute prefix. -/
noncomputable def freshRestartFinitePrefixMeasure
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    Measure (A.ContinuationPrefix offset) :=
  Kernel.partialTraj
    (policy.pathStepKernel hterminal)
    0 offset
    (fun _ =>
      A.initialEvent
        (latestEventState start initialPrefix))

/-- The named fresh finite-prefix law is the matching finite marginal of the
fresh infinite path law. -/
theorem freshRestartFinitePrefixMeasure_eq_pathMeasure_map_frestrictLe
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix offset =
      (policy.pathMeasure
        hterminal
        (latestEventState start initialPrefix)).map
          (frestrictLe offset) := by
  unfold
    freshRestartFinitePrefixMeasure
    pathMeasure
  exact
    (Kernel.traj_map_frestrictLe_apply
      (κ := policy.pathStepKernel hterminal)
      0 offset
      (fun _ =>
        A.initialEvent
          (latestEventState
            start initialPrefix))).symm

/-- The generated fresh finite-prefix law is invariant under resetting its
coordinate zero to the canonical initial event. This avoids any
measurable-singleton or measurable-diagonal premise. -/
theorem freshRestartFinitePrefixMeasure_map_setInitialPrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    (policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix offset).map
          (setInitialPrefix
            (latestEventState start initialPrefix)
            offset) =
      policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix offset := by
  rw [
    policy.freshRestartFinitePrefixMeasure_eq_pathMeasure_map_frestrictLe
      hterminal start initialPrefix offset,
    Measure.map_map
      (measurable_setInitialPrefix
        (latestEventState start initialPrefix)
        offset)
      (measurable_frestrictLe offset)]
  have hcomposition :
      setInitialPrefix
          (latestEventState start initialPrefix)
          offset ∘
        frestrictLe offset =
      frestrictLe offset ∘
        setInitialEvent
          (latestEventState start initialPrefix) := by
    funext path
    exact
      setInitialPrefix_frestrictLe_setInitialEvent
        (latestEventState start initialPrefix)
        offset path
  rw [
    hcomposition,
    ← Measure.map_map
      (measurable_frestrictLe offset)
      (measurable_setInitialEvent
        (latestEventState start initialPrefix)),
    policy.pathMeasure_map_setInitialEvent]

/-- If a measure is invariant under a measurable reset and two kernels agree
after that reset at every input, then their compositions with the invariant
measure agree. This lemma avoids converting a possibly nonmeasurable
fixed-point condition into an almost-everywhere proposition. -/
theorem measureComp_eq_of_map_eq_self_of_forall
    {X Y : Type*}
    [MeasurableSpace X]
    [MeasurableSpace Y]
    (μ : Measure X)
    (κ η : Kernel X Y)
    (reset : X → X)
    (hreset : Measurable reset)
    (hinvariant : μ.map reset = μ)
    (hkernel :
      ∀ x, κ (reset x) = η (reset x)) :
    κ ∘ₘ μ = η ∘ₘ μ := by
  calc
    κ ∘ₘ μ =
      κ ∘ₘ (μ.map reset) := by
        rw [hinvariant]
    _ =
      (κ.comap reset hreset) ∘ₘ μ := by
        rw [
          ← Measure.deterministic_comp_eq_map hreset,
          Measure.comp_assoc,
          Kernel.comp_deterministic_eq_comap]
    _ =
      (η.comap reset hreset) ∘ₘ μ := by
        apply Measure.comp_congr
        exact
          Filter.Eventually.of_forall
            (fun x => hkernel x)
    _ =
      η ∘ₘ (μ.map reset) := by
        rw [
          ← Measure.deterministic_comp_eq_map hreset,
          Measure.comp_assoc,
          Kernel.comp_deterministic_eq_comap]
    _ =
      η ∘ₘ μ := by
        rw [hinvariant]

/-- Fresh-clock finite-prefix laws satisfy their own one-step trajectory
recursion. -/
theorem freshRestartFinitePrefixMeasure_succ
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix (offset + 1) =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset := by
  unfold freshRestartFinitePrefixMeasure
  have hcompose :=
    congrArg
      (fun kernel =>
        kernel
          (fun _ =>
            A.initialEvent
              (latestEventState
                start initialPrefix)))
      (Kernel.partialTraj_comp_partialTraj
        (κ := policy.pathStepKernel hterminal)
        (a := 0)
        (b := offset)
        (c := offset + 1)
        (Nat.zero_le offset)
        (Nat.le_succ offset))
  exact hcompose.symm

/-- At horizon `start + offset`, the spliced full-path marginal is exactly
the fresh partial trajectory through `offset` mapped by the finite splice. -/
theorem splicedFreshFinitePrefixMeasure_add_eq_map_partialTraj
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix
        (start + offset) =
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        0 offset
        (fun _ =>
          A.initialEvent
            (latestEventState
              start initialPrefix))).map
        (spliceContinuationPrefix
          start initialPrefix offset) := by
  unfold
    splicedFreshFinitePrefixMeasure
    splicedFreshAbsolutePathMeasure
    pathMeasure
  rw [
    Measure.map_map
      (measurable_frestrictLe (start + offset))
      (measurable_spliceContinuationPath
        start initialPrefix)]
  have hcomposition :
      frestrictLe (start + offset) ∘
          spliceContinuationPath start initialPrefix =
        spliceContinuationPrefix
            start initialPrefix offset ∘
          frestrictLe offset := by
    funext freshPath
    exact
      (spliceContinuationPrefix_frestrictLe
        start initialPrefix offset freshPath).symm
  rw [hcomposition]
  rw [
    ← Measure.map_map
      (measurable_spliceContinuationPrefix
        start initialPrefix offset)
      (measurable_frestrictLe offset)]
  rw [Kernel.traj_map_frestrictLe_apply]

/-- Abbreviated finite-prefix representation of the spliced fresh law. -/
theorem splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix
        (start + offset) =
      (policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix offset).map
          (spliceContinuationPrefix
            start initialPrefix offset) := by
  exact
    policy.splicedFreshFinitePrefixMeasure_add_eq_map_partialTraj
      hterminal start initialPrefix offset

/-- The actual absolute finite marginals satisfy the expected one-step
`partialTraj` recursion after every offset from `start`. -/
theorem absoluteFinitePrefixMeasureFromPrefix_succ
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ) :
    policy.absoluteFinitePrefixMeasureFromPrefix
        hterminal start initialPrefix
        ((start + offset) + 1) =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        policy.absoluteFinitePrefixMeasureFromPrefix
          hterminal start initialPrefix
          (start + offset) := by
  unfold
    absoluteFinitePrefixMeasureFromPrefix
    absolutePathMeasureFromPrefix
  rw [
    Kernel.traj_map_frestrictLe_apply,
    Kernel.traj_map_frestrictLe_apply]
  have hcompose :=
    congrArg
      (fun kernel => kernel initialPrefix)
      (Kernel.partialTraj_comp_partialTraj
        (κ := policy.pathStepKernel hterminal)
        (a := start)
        (b := start + offset)
        (c := (start + offset) + 1)
        (Nat.le_add_right start offset)
        (Nat.le_succ (start + offset)))
  exact hcompose.symm

/-- A successor partial trajectory queried at a fixed prefix is just the
one-event step law mapped by deterministic prefix extension. -/
theorem partialTraj_succ_apply_eq_map_appendContinuationEvent
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (time : ℕ)
    (finitePrefix : A.ContinuationPrefix time) :
    Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        time (time + 1) finitePrefix =
      (policy.pathStepKernel hterminal time finitePrefix).map
        (appendContinuationEvent time finitePrefix) := by
  rw [
    Kernel.partialTraj_succ_self,
    Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.prod_apply,
    Kernel.id_apply,
    Measure.dirac_prod,
    Kernel.map_apply _
      (MeasurableEquiv.piSingleton
        (X := fun _ => A.PathEvent)
        time).measurable]
  rw [
    Measure.map_map
      measurable_prodMk_left
      (MeasurableEquiv.piSingleton
        (X := fun _ => A.PathEvent)
        time).measurable]
  simpa [
    appendContinuationEvent,
    Function.comp_def] using
    (Measure.map_map
      (μ := policy.pathStepKernel
        hterminal time finitePrefix)
      measurable_IicProdIoc
      (measurable_prodMk_left.comp
        (MeasurableEquiv.piSingleton
          (X := fun _ => A.PathEvent)
          time).measurable))

/-- Equality of the primitive next-event laws at matching fresh and absolute
prefixes implies equality of their one-step finite-prefix laws after
splicing. -/
theorem partialTraj_succ_splice_eq_of_pathStepKernel_apply_eq
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (offset : ℕ)
    (freshPrefix : A.ContinuationPrefix offset)
    (hkernel :
      policy.pathStepKernel hterminal
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        policy.pathStepKernel hterminal
          offset freshPrefix) :
    Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        (start + offset)
        ((start + offset) + 1)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix) =
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        offset (offset + 1)
        freshPrefix).map
          (spliceContinuationPrefix
            start initialPrefix (offset + 1)) := by
  rw [
    policy.partialTraj_succ_apply_eq_map_appendContinuationEvent
      hterminal (start + offset)
      (spliceContinuationPrefix
        start initialPrefix offset freshPrefix),
    policy.partialTraj_succ_apply_eq_map_appendContinuationEvent
      hterminal offset freshPrefix,
    Measure.map_map
      (measurable_spliceContinuationPrefix
        start initialPrefix (offset + 1))
      (measurable_appendContinuationEvent
        offset freshPrefix),
    hkernel]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun event =>
    (spliceContinuationPrefix_appendContinuationEvent
      start initialPrefix offset freshPrefix event).symm

end EventHistoryActionPolicy

end MeasurableKernelArena
