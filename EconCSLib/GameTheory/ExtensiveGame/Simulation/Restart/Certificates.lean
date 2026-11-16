/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Trajectory

/-!
# Restart.Certificates — raw compatibility certificates

This implementation module defines generated-law, pointwise, rooted,
primitive path-step, behavioral action-kernel, and distributional partial-step
certificates.  It proves only adjacent conversions and closes the raw
trajectory argument through finite-prefix/projective-limit equality.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

namespace EventHistoryActionPolicy

/-- Generated-law almost-everywhere one-step kernel compatibility.

For almost every fresh prefix through `offset`, extending it by one
fresh-clock step and then finite-splicing has the same law as first
finite-splicing it and then extending it by the actual absolute-clock step.
The almost-everywhere quantifier avoids imposing equality on prefixes ignored
by the generated fresh law.
-/
def IsFreshRestartStepKernelCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset,
    ∀ᵐ freshPrefix ∂
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset,
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
              start initialPrefix (offset + 1))

/-- Pointwise strengthening of generated-law almost-everywhere one-step
kernel compatibility. This version is convenient for structural policies,
but deliberately stronger than the reusable distributional condition. -/
def IsFreshRestartPointwiseStepKernelCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset freshPrefix,
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
          start initialPrefix (offset + 1))

/-- Canonically rooted compatibility stated directly on the behavioral
action-selection kernel.

At matching rooted fresh and absolute prefixes, this condition requires the
same probability measure on dependent action bundles. Terminal prefixes are
included: both measures are then forced to zero by the policy interface.
-/
def IsFreshRestartRootedActionKernelCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset freshPrefix,
    IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix →
      policy.kernel
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        policy.kernel offset freshPrefix

/-- Root-uniform rooted behavioral action-kernel rebasing.

This structural certificate requires the root-scoped action condition for
every retained absolute start and finite prefix. It is stronger than any
single-root condition and is not automatic for arbitrary history-dependent
policies.
-/
def IsFreshRestartRootedActionKernelCompatible
    (policy : A.EventHistoryActionPolicy) :
    Prop :=
  ∀ start initialPrefix,
    policy.IsFreshRestartRootedActionKernelCompatibleAt
      start initialPrefix

/-- A root-uniform behavioral certificate supplies the root-scoped
certificate at any retained prefix. -/
theorem IsFreshRestartRootedActionKernelCompatible.at
    {policy : A.EventHistoryActionPolicy}
    (hcompatible :
      policy.IsFreshRestartRootedActionKernelCompatible)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.IsFreshRestartRootedActionKernelCompatibleAt
      start initialPrefix :=
  hcompatible start initialPrefix

/-- Canonically rooted compatibility stated directly on the primitive
next-event `pathStepKernel`.

At every rooted fresh prefix, the absolute-clock and fresh-clock kernels
must assign the same law to the next state/action event. Terminal absorption,
policy randomization, and arena transition randomness are already included
in `pathStepKernel`; this condition does not compare only action policies.
-/
def IsFreshRestartRootedPathStepKernelCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset freshPrefix,
    IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix →
      policy.pathStepKernel hterminal
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        policy.pathStepKernel hterminal
          offset freshPrefix

/-- Canonically rooted pointwise one-step compatibility.

Unlike the global pointwise strengthening, this condition is required only
for fresh prefixes fixed by coordinate-zero initial-event replacement. The
generated fresh law is invariant under that replacement, so this weaker
structural condition still suffices after integration without assuming that
the rooted-prefix equality predicate is measurable.
-/
def IsFreshRestartRootedStepKernelCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset freshPrefix,
    IsInitialEventRootedPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix →
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
              start initialPrefix (offset + 1))

/-- Distributional local step compatibility: at every offset, the next
spliced-fresh finite prefix is obtained by applying the actual absolute
one-step trajectory kernel to the current spliced-fresh prefix law.

This formulation is intentionally distributional. It allows two step kernels
to differ away from prefixes generated by the fresh law, which is essential
for non-atomic and null-prefix models.
-/
def IsFreshRestartPartialStepCompatibleAt
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    Prop :=
  ∀ offset,
    policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix
        ((start + offset) + 1) =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        policy.splicedFreshFinitePrefixMeasure
          hterminal start initialPrefix
          (start + offset)

/-- Pointwise one-step compatibility implies the generated-law
almost-everywhere certificate. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.stepKernel
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartPointwiseStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartStepKernelCompatibleAt
      hterminal start initialPrefix := by
  intro offset
  exact
    Filter.Eventually.of_forall
      (hcompatible offset)

/-- Global pointwise one-step compatibility implies the weaker
canonical-rooted pointwise condition. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.rootedStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartPointwiseStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartRootedStepKernelCompatibleAt
      hterminal start initialPrefix := by
  intro offset freshPrefix _hrooted
  exact hcompatible offset freshPrefix

/-- Rooted equality of the behavioral action measures implies rooted
equality of the complete primitive next-event measures. Matching rooted
prefixes have the same latest state, so they take the same terminal branch;
on the nonterminal branch the equal action measures are bound through the
common recorded transition. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.rootedPathStep
    {policy : A.EventHistoryActionPolicy}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hterminal : MeasurableSet A.terminalSet)
    (hcompatible :
      policy.IsFreshRestartRootedActionKernelCompatibleAt
        start initialPrefix) :
    policy.IsFreshRestartRootedPathStepKernelCompatibleAt
      hterminal start initialPrefix := by
  intro offset freshPrefix hrooted
  have hstate :
      latestEventState (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        latestEventState offset freshPrefix :=
    latestEventState_spliceContinuationPrefix_eq_of_rooted
      start initialPrefix offset freshPrefix hrooted
  by_cases hfreshTerminal :
      IsEmpty
        (A.Action
          (latestEventState offset freshPrefix))
  · have habsoluteTerminal :
        IsEmpty
          (A.Action
            (latestEventState (start + offset)
              (spliceContinuationPrefix
                start initialPrefix offset freshPrefix))) := by
      rw [hstate]
      exact hfreshTerminal
    rw [
      policy.pathStepKernel_apply_terminal
        hterminal (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)
        habsoluteTerminal,
      policy.pathStepKernel_apply_terminal
        hterminal offset freshPrefix
        hfreshTerminal,
      hstate]
  · have habsoluteNonterminal :
        ¬ IsEmpty
          (A.Action
            (latestEventState (start + offset)
              (spliceContinuationPrefix
                start initialPrefix offset freshPrefix))) := by
      rw [hstate]
      exact hfreshTerminal
    rw [
      policy.pathStepKernel_apply_nonterminal
        hterminal (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)
        habsoluteNonterminal,
      policy.pathStepKernel_apply_nonterminal
        hterminal offset freshPrefix
        hfreshTerminal,
      hcompatible offset freshPrefix hrooted]

/-- Primitive rooted next-event compatibility implies rooted one-step
finite-prefix compatibility. This is the reusable naturality bridge from
`pathStepKernel` to Mathlib's successor `partialTraj`. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.rootedStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartRootedStepKernelCompatibleAt
      hterminal start initialPrefix := by
  intro offset freshPrefix hrooted
  exact
    policy.partialTraj_succ_splice_eq_of_pathStepKernel_apply_eq
      hterminal start initialPrefix offset freshPrefix
      (hcompatible offset freshPrefix hrooted)

/-- Rooted equality of complete primitive next-event measures recovers
rooted equality of the behavioral action measures.

On nonterminal prefixes, projecting the recorded event to its incoming
action gives the action measure mapped by `Sum.inr`; this map is injective
because `Sum.inr` is a measurable embedding. On terminal prefixes both
action measures are zero by the policy interface.
-/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.rootedAction
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartRootedActionKernelCompatibleAt
      start initialPrefix := by
  intro offset freshPrefix hrooted
  have hstate :
      latestEventState (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix) =
        latestEventState offset freshPrefix :=
    latestEventState_spliceContinuationPrefix_eq_of_rooted
      start initialPrefix offset freshPrefix hrooted
  by_cases hfreshTerminal :
      IsEmpty
        (A.Action
          (latestEventState offset freshPrefix))
  · have habsoluteTerminal :
        IsEmpty
          (A.Action
            (latestEventState (start + offset)
              (spliceContinuationPrefix
                start initialPrefix offset freshPrefix))) := by
      rw [hstate]
      exact hfreshTerminal
    rw [
      policy.terminal_zero
        (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)
        habsoluteTerminal,
      policy.terminal_zero
        offset freshPrefix hfreshTerminal]
  · have habsoluteNonterminal :
        ¬ IsEmpty
          (A.Action
            (latestEventState (start + offset)
              (spliceContinuationPrefix
                start initialPrefix offset freshPrefix))) := by
      rw [hstate]
      exact hfreshTerminal
    have hpath :=
      hcompatible offset freshPrefix hrooted
    rw [
      policy.pathStepKernel_apply_nonterminal
        hterminal (start + offset)
        (spliceContinuationPrefix
          start initialPrefix offset freshPrefix)
        habsoluteNonterminal,
      policy.pathStepKernel_apply_nonterminal
        hterminal offset freshPrefix
        hfreshTerminal]
        at hpath
    have haction :=
      congrArg
        (fun measure =>
          measure.map PathEvent.action)
        hpath
    dsimp only at haction
    change
      (policy.actionStepKernel
          (start + offset)
          (spliceContinuationPrefix
            start initialPrefix offset freshPrefix)).map
          PathEvent.action =
        (policy.actionStepKernel
          offset freshPrefix).map
            PathEvent.action
      at haction
    rw [
      ← Kernel.map_apply _
        PathEvent.measurable_action,
      policy.actionStepKernel_map_action,
      Kernel.map_apply _ measurable_inr,
      ← Kernel.map_apply _
        PathEvent.measurable_action,
      policy.actionStepKernel_map_action,
      Kernel.map_apply _ measurable_inr]
        at haction
    have hinr :
        MeasurableEmbedding
          (@Sum.inr Unit A.ActionBundle) :=
      { injective := Sum.inr_injective
        measurable := measurable_inr
        measurableSet_image' :=
          fun _ hs => hs.inr_image }
    exact hinr.map_injective haction

/-- Rooted action-kernel rebasing is exactly equivalent to rooted primitive
next-event rebasing. -/
theorem isFreshRestartRootedActionKernelCompatibleAt_iff_rootedPathStep
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.IsFreshRestartRootedActionKernelCompatibleAt
        start initialPrefix ↔
      policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        hterminal start initialPrefix :=
  ⟨fun hcompatible =>
      hcompatible.rootedPathStep hterminal,
    fun hcompatible =>
      hcompatible.rootedAction⟩

/-- Rooted action-kernel rebasing implies rooted successor-prefix rebasing.
-/
theorem IsFreshRestartRootedActionKernelCompatibleAt.rootedStep
    {policy : A.EventHistoryActionPolicy}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hterminal : MeasurableSet A.terminalSet)
    (hcompatible :
      policy.IsFreshRestartRootedActionKernelCompatibleAt
        start initialPrefix) :
    policy.IsFreshRestartRootedStepKernelCompatibleAt
      hterminal start initialPrefix :=
  (hcompatible.rootedPathStep hterminal).rootedStep

/-- Rooted one-step finite-prefix compatibility recovers primitive rooted
next-event compatibility by projecting both sides to their newest event.
Together with `rootedStep`, this shows that the lower-level certificate is
an exact reformulation, not an additional stationarity assumption. -/
theorem IsFreshRestartRootedStepKernelCompatibleAt.rootedPathStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartRootedStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartRootedPathStepKernelCompatibleAt
      hterminal start initialPrefix := by
  intro offset freshPrefix hrooted
  let absolutePrefix :
      A.ContinuationPrefix (start + offset) :=
    spliceContinuationPrefix
      start initialPrefix offset freshPrefix
  have hmeasure :=
    congrArg
      (fun measure =>
        measure.map
          (latestEvent ((start + offset) + 1)))
      (hcompatible offset freshPrefix hrooted)
  dsimp only at hmeasure
  rw [
    Measure.map_map
      (measurable_latestEvent ((start + offset) + 1))
      (measurable_spliceContinuationPrefix
        start initialPrefix (offset + 1))]
      at hmeasure
  have hlatestComposition :
      latestEvent ((start + offset) + 1) ∘
          spliceContinuationPrefix
            start initialPrefix (offset + 1) =
        latestEvent (offset + 1) := by
    funext finitePrefix
    exact
      latestEvent_spliceContinuationPrefix_add_succ
        start initialPrefix offset finitePrefix
  rw [hlatestComposition] at hmeasure
  have habsoluteKernel :
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        (start + offset)
        ((start + offset) + 1)).map
          (latestEvent ((start + offset) + 1)) =
        policy.pathStepKernel hterminal
          (start + offset) := by
    simpa only [latestEvent] using
      (@Kernel.map_partialTraj_succ_self
        (EventAt A) (fun _ => inferInstance)
        (policy.pathStepKernel hterminal)
        (fun _ => inferInstance)
        (start + offset))
  have hfreshKernel :
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        offset (offset + 1)).map
          (latestEvent (offset + 1)) =
        policy.pathStepKernel hterminal offset := by
    simpa only [latestEvent] using
      (@Kernel.map_partialTraj_succ_self
        (EventAt A) (fun _ => inferInstance)
        (policy.pathStepKernel hterminal)
        (fun _ => inferInstance)
        offset)
  have habsoluteApply :=
    congrArg
      (fun kernel => kernel absolutePrefix)
      habsoluteKernel
  dsimp only at habsoluteApply
  rw [
    Kernel.map_apply _
      (measurable_latestEvent
        ((start + offset) + 1))]
      at habsoluteApply
  have hfreshApply :=
    congrArg
      (fun kernel => kernel freshPrefix)
      hfreshKernel
  dsimp only at hfreshApply
  rw [
    Kernel.map_apply _
      (measurable_latestEvent (offset + 1))]
      at hfreshApply
  exact
    habsoluteApply.symm.trans
      (hmeasure.trans hfreshApply)

/-- Primitive rooted next-event compatibility is equivalent to rooted
one-step finite-prefix compatibility. -/
theorem isFreshRestartRootedPathStepKernelCompatibleAt_iff_rootedStep
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        hterminal start initialPrefix ↔
      policy.IsFreshRestartRootedStepKernelCompatibleAt
        hterminal start initialPrefix :=
  ⟨fun hcompatible => hcompatible.rootedStep,
    fun hcompatible => hcompatible.rootedPathStep⟩

/-- Rooted action-kernel rebasing is exactly equivalent to rooted
successor-prefix rebasing. -/
theorem isFreshRestartRootedActionKernelCompatibleAt_iff_rootedStep
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.IsFreshRestartRootedActionKernelCompatibleAt
        start initialPrefix ↔
      policy.IsFreshRestartRootedStepKernelCompatibleAt
        hterminal start initialPrefix :=
  ⟨fun hcompatible =>
      hcompatible.rootedStep hterminal,
    fun hcompatible =>
      hcompatible.rootedPathStep.rootedAction⟩

/-- Generated-law almost-everywhere one-step kernel compatibility implies
the exact distributional finite-prefix recurrence. -/
theorem IsFreshRestartStepKernelCompatibleAt.partialStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartPartialStepCompatibleAt
      hterminal start initialPrefix := by
  intro offset
  calc
    policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix
        ((start + offset) + 1) =
      (policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix
        (offset + 1)).map
          (spliceContinuationPrefix
            start initialPrefix (offset + 1)) := by
        simpa only [Nat.add_succ] using
          policy.splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
            hterminal start initialPrefix (offset + 1)
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)) := by
        rw [
          policy.freshRestartFinitePrefixMeasure_succ
            hterminal start initialPrefix offset]
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1)).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset := by
        rw [
          Measure.map_comp
            (policy.freshRestartFinitePrefixMeasure
              hterminal start initialPrefix offset)
            (Kernel.partialTraj
              (policy.pathStepKernel hterminal)
              offset (offset + 1))
            (measurable_spliceContinuationPrefix
              start initialPrefix (offset + 1))]
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1)).comap
            (spliceContinuationPrefix
              start initialPrefix offset)
            (measurable_spliceContinuationPrefix
              start initialPrefix offset) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset := by
        apply Measure.comp_congr
        filter_upwards [hcompatible offset] with
          freshPrefix hfreshPrefix
        rw [
          Kernel.map_apply
            _
            (measurable_spliceContinuationPrefix
              start initialPrefix (offset + 1)),
          Kernel.comap_apply]
        exact hfreshPrefix.symm
    _ =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        (policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset).map
            (spliceContinuationPrefix
              start initialPrefix offset) := by
        rw [
          ← Kernel.comp_deterministic_eq_comap,
          ← Measure.comp_assoc,
          Measure.deterministic_comp_eq_map]
    _ =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        policy.splicedFreshFinitePrefixMeasure
          hterminal start initialPrefix
          (start + offset) := by
        rw [
          policy.splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
            hterminal start initialPrefix offset]

/-- Canonically rooted pointwise one-step compatibility implies the exact
distributional recurrence. The proof integrates through fixed-root reset
invariance and does not assert that the rooted-prefix predicate is
measurable. -/
theorem IsFreshRestartRootedStepKernelCompatibleAt.partialStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartRootedStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartPartialStepCompatibleAt
      hterminal start initialPrefix := by
  intro offset
  have hkernelComposition :
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1)).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1)).comap
            (spliceContinuationPrefix
              start initialPrefix offset)
            (measurable_spliceContinuationPrefix
              start initialPrefix offset) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset := by
    apply
      measureComp_eq_of_map_eq_self_of_forall
        (policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset)
        ((Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1)).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)))
        ((Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1)).comap
            (spliceContinuationPrefix
              start initialPrefix offset)
            (measurable_spliceContinuationPrefix
              start initialPrefix offset))
        (setInitialPrefix
          (latestEventState start initialPrefix)
          offset)
        (measurable_setInitialPrefix
          (latestEventState start initialPrefix)
          offset)
        (policy.freshRestartFinitePrefixMeasure_map_setInitialPrefix
          hterminal start initialPrefix offset)
    intro freshPrefix
    have hrooted :
        IsInitialEventRootedPrefix
          (latestEventState start initialPrefix)
          offset
          (setInitialPrefix
            (latestEventState start initialPrefix)
            offset freshPrefix) :=
      isInitialEventRootedPrefix_setInitialPrefix
        (latestEventState start initialPrefix)
        offset freshPrefix
    have hpointwise :=
      hcompatible offset
        (setInitialPrefix
          (latestEventState start initialPrefix)
          offset freshPrefix)
        hrooted
    rw [
      Kernel.map_apply
        _
        (measurable_spliceContinuationPrefix
          start initialPrefix (offset + 1)),
      Kernel.comap_apply]
    exact hpointwise.symm
  calc
    policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix
        ((start + offset) + 1) =
      (policy.freshRestartFinitePrefixMeasure
        hterminal start initialPrefix
        (offset + 1)).map
          (spliceContinuationPrefix
            start initialPrefix (offset + 1)) := by
        simpa only [Nat.add_succ] using
          policy.splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
            hterminal start initialPrefix (offset + 1)
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)) := by
        rw [
          policy.freshRestartFinitePrefixMeasure_succ
            hterminal start initialPrefix offset]
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          offset (offset + 1)).map
            (spliceContinuationPrefix
              start initialPrefix (offset + 1)) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset := by
        rw [
          Measure.map_comp
            (policy.freshRestartFinitePrefixMeasure
              hterminal start initialPrefix offset)
            (Kernel.partialTraj
              (policy.pathStepKernel hterminal)
              offset (offset + 1))
            (measurable_spliceContinuationPrefix
              start initialPrefix (offset + 1))]
    _ =
      (Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1)).comap
            (spliceContinuationPrefix
              start initialPrefix offset)
            (measurable_spliceContinuationPrefix
              start initialPrefix offset) ∘ₘ
        policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset :=
      hkernelComposition
    _ =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        (policy.freshRestartFinitePrefixMeasure
          hterminal start initialPrefix offset).map
            (spliceContinuationPrefix
              start initialPrefix offset) := by
        rw [
          ← Kernel.comp_deterministic_eq_comap,
          ← Measure.comp_assoc,
          Measure.deterministic_comp_eq_map]
    _ =
      Kernel.partialTraj
          (policy.pathStepKernel hterminal)
          (start + offset)
          ((start + offset) + 1) ∘ₘ
        policy.splicedFreshFinitePrefixMeasure
          hterminal start initialPrefix
          (start + offset) := by
        rw [
          policy.splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
            hterminal start initialPrefix offset]

/-- Primitive rooted next-event compatibility implies the exact
distributional finite-prefix recurrence. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.partialStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartRootedPathStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartPartialStepCompatibleAt
      hterminal start initialPrefix :=
  hcompatible.rootedStep.partialStep

/-- Rooted behavioral action-kernel rebasing implies the exact
distributional finite-prefix recurrence. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.partialStep
    {policy : A.EventHistoryActionPolicy}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hterminal : MeasurableSet A.terminalSet)
    (hcompatible :
      policy.IsFreshRestartRootedActionKernelCompatibleAt
        start initialPrefix) :
    policy.IsFreshRestartPartialStepCompatibleAt
      hterminal start initialPrefix :=
  (hcompatible.rootedStep hterminal).partialStep

/-- Pointwise one-step compatibility implies the exact distributional
finite-prefix recurrence. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.partialStep
    {policy : A.EventHistoryActionPolicy}
    {hterminal : MeasurableSet A.terminalSet}
    {start : ℕ}
    {initialPrefix : A.ContinuationPrefix start}
    (hcompatible :
      policy.IsFreshRestartPointwiseStepKernelCompatibleAt
        hterminal start initialPrefix) :
    policy.IsFreshRestartPartialStepCompatibleAt
      hterminal start initialPrefix :=
  hcompatible.stepKernel.partialStep

/-- Distributional local step compatibility makes every post-root finite
spliced marginal equal the matching actual absolute marginal. -/
theorem splicedFreshFinitePrefixMeasure_eq_absolute_of_partialStepCompatible
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (hcompatible :
      policy.IsFreshRestartPartialStepCompatibleAt
        hterminal start initialPrefix) :
    ∀ offset,
      policy.splicedFreshFinitePrefixMeasure
          hterminal start initialPrefix
          (start + offset) =
        policy.absoluteFinitePrefixMeasureFromPrefix
          hterminal start initialPrefix
          (start + offset) := by
  intro offset
  induction offset with
  | zero =>
      simpa only [Nat.add_zero] using
        (policy.splicedFreshAbsolutePathMeasure_map_frestrictLe
          hterminal start initialPrefix).trans
            (policy.absolutePathMeasureFromPrefix_map_frestrictLe
              hterminal start initialPrefix).symm
  | succ offset ih =>
      rw [Nat.add_succ]
      calc
        policy.splicedFreshFinitePrefixMeasure
            hterminal start initialPrefix
            ((start + offset) + 1) =
          Kernel.partialTraj
              (policy.pathStepKernel hterminal)
              (start + offset)
              ((start + offset) + 1) ∘ₘ
            policy.splicedFreshFinitePrefixMeasure
              hterminal start initialPrefix
              (start + offset) :=
          hcompatible offset
        _ =
          Kernel.partialTraj
              (policy.pathStepKernel hterminal)
              (start + offset)
              ((start + offset) + 1) ∘ₘ
            policy.absoluteFinitePrefixMeasureFromPrefix
              hterminal start initialPrefix
              (start + offset) := by
            rw [ih]
        _ =
          policy.absoluteFinitePrefixMeasureFromPrefix
            hterminal start initialPrefix
            ((start + offset) + 1) :=
          (policy.absoluteFinitePrefixMeasureFromPrefix_succ
            hterminal start initialPrefix offset).symm

end EventHistoryActionPolicy

/-- Two probability laws on a countable product are equal exactly when all
their initial finite-prefix marginals are equal. -/
theorem probabilityMeasure_eq_iff_map_frestrictLe_eq
    {S : Type*}
    [MeasurableSpace S]
    (μ ν : Measure (ℕ → S))
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ = ν ↔
      ∀ horizon,
        μ.map (frestrictLe horizon) =
          ν.map (frestrictLe horizon) := by
  constructor
  · intro hmeasure horizon
    rw [hmeasure]
  · intro hmarginal
    let marginal :
        (horizon : ℕ) →
          Measure (Finset.Iic horizon → S) :=
      fun horizon =>
        μ.map (frestrictLe horizon)
    have hmarginal_probability :
        ∀ horizon,
          IsProbabilityMeasure (marginal horizon) := by
      intro horizon
      unfold marginal
      exact
        Measure.isProbabilityMeasure_map
          (measurable_frestrictLe horizon).aemeasurable
    letI (horizon : ℕ) :
        IsProbabilityMeasure (marginal horizon) :=
      hmarginal_probability horizon
    have hconsistent :
        ∀ a b : ℕ, ∀ hab : a ≤ b,
          (marginal b).map
              (frestrictLe₂
                (π := fun _ : ℕ => S) hab) =
            marginal a := by
      intro a b hab
      unfold marginal
      rw [
        Measure.map_map
          (measurable_frestrictLe₂
            (X := fun _ : ℕ => S) hab)
          (measurable_frestrictLe b)]
      congr 1
    have hprojective :=
      @isProjectiveMeasureFamily_inducedFamily
        (fun _ : ℕ => S) _ marginal hconsistent
    have hμ :
        IsProjectiveLimit μ
          (inducedFamily
            (X := fun _ : ℕ => S) marginal) := by
      rw [isProjectiveLimit_nat_iff hprojective]
      intro horizon
      rw [inducedFamily_Iic]
    have hν :
        IsProjectiveLimit ν
          (inducedFamily
            (X := fun _ : ℕ => S) marginal) := by
      rw [isProjectiveLimit_nat_iff hprojective]
      intro horizon
      rw [inducedFamily_Iic]
      exact (hmarginal horizon).symm
    letI (indices : Finset ℕ) :
        IsProbabilityMeasure
          (inducedFamily
            (X := fun _ : ℕ => S)
            marginal indices) := by
      unfold inducedFamily
      haveI :
          IsProbabilityMeasure
            (marginal (indices.sup id)) :=
        hmarginal_probability _
      exact
        Measure.isProbabilityMeasure_map
          (Finset.measurable_restrict₂ _).aemeasurable
    exact hμ.unique hν

namespace EventHistoryActionPolicy

/-- The actual absolute trajectory is the spliced fresh trajectory exactly
when all their complete initial finite-prefix marginals agree. -/
theorem absolutePathMeasureFromPrefix_eq_spliced_iff_finitePrefix
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix =
      policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix ↔
      ∀ horizon,
        (policy.absolutePathMeasureFromPrefix
          hterminal start initialPrefix).map
            (frestrictLe horizon) =
          (policy.splicedFreshAbsolutePathMeasure
            hterminal start initialPrefix).map
              (frestrictLe horizon) := by
  exact
    probabilityMeasure_eq_iff_map_frestrictLe_eq
      (policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix)
      (policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix)

/-- Restricting an actual absolute finite-prefix marginal to an earlier
horizon gives that earlier marginal. -/
theorem absoluteFinitePrefixMeasureFromPrefix_map_frestrictLe₂
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    {earlier later : ℕ}
    (horizonLe : earlier ≤ later) :
    (policy.absoluteFinitePrefixMeasureFromPrefix
      hterminal start initialPrefix later).map
        (frestrictLe₂ horizonLe) =
      policy.absoluteFinitePrefixMeasureFromPrefix
        hterminal start initialPrefix earlier := by
  unfold absoluteFinitePrefixMeasureFromPrefix
  rw [
    Measure.map_map
      (measurable_frestrictLe₂ horizonLe)
      (measurable_frestrictLe later)]
  congr 1

/-- Restricting a spliced-fresh finite-prefix marginal to an earlier horizon
gives that earlier marginal. -/
theorem splicedFreshFinitePrefixMeasure_map_frestrictLe₂
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    {earlier later : ℕ}
    (horizonLe : earlier ≤ later) :
    (policy.splicedFreshFinitePrefixMeasure
      hterminal start initialPrefix later).map
        (frestrictLe₂ horizonLe) =
      policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix earlier := by
  unfold splicedFreshFinitePrefixMeasure
  rw [
    Measure.map_map
      (measurable_frestrictLe₂ horizonLe)
      (measurable_frestrictLe later)]
  congr 1

/-- Distributional one-step compatibility at every offset implies equality
of the complete actual and spliced infinite trajectory laws. -/
theorem absolutePathMeasureFromPrefix_eq_spliced_of_partialStepCompatible
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start)
    (hcompatible :
      policy.IsFreshRestartPartialStepCompatibleAt
        hterminal start initialPrefix) :
    policy.absolutePathMeasureFromPrefix
        hterminal start initialPrefix =
      policy.splicedFreshAbsolutePathMeasure
        hterminal start initialPrefix := by
  rw [
    policy.absolutePathMeasureFromPrefix_eq_spliced_iff_finitePrefix
      hterminal start initialPrefix]
  intro horizon
  change
    policy.absoluteFinitePrefixMeasureFromPrefix
        hterminal start initialPrefix horizon =
      policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix horizon
  have hpost :=
    policy.splicedFreshFinitePrefixMeasure_eq_absolute_of_partialStepCompatible
      hterminal start initialPrefix hcompatible
  by_cases hstart : start ≤ horizon
  · have hoffset :=
      hpost (horizon - start)
    have hadd :
        start + (horizon - start) = horizon := by
      omega
    rw [hadd] at hoffset
    exact hoffset.symm
  · have hhorizon : horizon ≤ start :=
      Nat.le_of_not_ge hstart
    have hroot := hpost 0
    simp only [Nat.add_zero] at hroot
    have hrestricted :=
      congrArg
        (fun measure =>
          measure.map
            (frestrictLe₂ hhorizon))
        hroot
    change
      (policy.splicedFreshFinitePrefixMeasure
        hterminal start initialPrefix start).map
          (frestrictLe₂ hhorizon) =
        (policy.absoluteFinitePrefixMeasureFromPrefix
          hterminal start initialPrefix start).map
            (frestrictLe₂ hhorizon)
      at hrestricted
    rw [
      policy.splicedFreshFinitePrefixMeasure_map_frestrictLe₂
        hterminal start initialPrefix hhorizon,
      policy.absoluteFinitePrefixMeasureFromPrefix_map_frestrictLe₂
        hterminal start initialPrefix hhorizon]
        at hrestricted
    exact hrestricted.symm

/-- The distributional partial-step condition is an exact characterization
of actual/spliced trajectory equality. -/
theorem isFreshRestartPartialStepCompatibleAt_iff_eq_spliced
    (policy : A.EventHistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (start : ℕ)
    (initialPrefix : A.ContinuationPrefix start) :
    policy.IsFreshRestartPartialStepCompatibleAt
        hterminal start initialPrefix ↔
      policy.absolutePathMeasureFromPrefix
          hterminal start initialPrefix =
        policy.splicedFreshAbsolutePathMeasure
          hterminal start initialPrefix := by
  constructor
  · exact
      policy.absolutePathMeasureFromPrefix_eq_spliced_of_partialStepCompatible
        hterminal start initialPrefix
  · intro htrajectory offset
    unfold splicedFreshFinitePrefixMeasure
    rw [← htrajectory]
    exact
      policy.absoluteFinitePrefixMeasureFromPrefix_succ
        hterminal start initialPrefix offset

end EventHistoryActionPolicy

end MeasurableKernelArena
