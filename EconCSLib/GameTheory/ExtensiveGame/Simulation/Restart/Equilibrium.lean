/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Assembly

/-!
# Restart.Equilibrium — fresh-restart equilibrium transfer

This implementation module contains the single maintained semantic proof
route from state-law compatibility to expected-utility equality and
deviation-complete designated-continuation Nash equivalence, with explicit
subgame-perfection-on and complete standard-SPE specializations.
Certificate-specific proofs below are private route regressions: consumers
convert their certificate to state-law compatibility and use the six
canonical public theorems.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableHistoryModel.BoundedPathUtility

variable
  {model : MeasurableHistoryModel G}
  (evaluation : MeasurableHistoryModel.BoundedPathUtility model)

/-- Under state-law compatibility, fresh-restart and absolute-continuation
bounded expected utilities are identical. -/
theorem expectedUtility_eq_continuationExpectedUtility_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G)
    (hcompatible :
      profile.IsFreshRestartStateCompatibleAt root)
    (i : N) :
    evaluation.expectedUtility profile root i =
      evaluation.continuationExpectedUtility
        profile root i := by
  unfold
    MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt
    MeasurableKernelPresentation.KernelBehavioralProfile.freshRestartStatePathMeasure
      at hcompatible
  unfold
    expectedUtility
    PathUtility.expectedUtility
    continuationExpectedUtility
  rw [hcompatible]

/-- If the baseline and every admitted deviation have compatible state laws,
fresh-restart Nash and absolute-prefix continuation Nash are equivalent. -/
theorem isNashAt_iff_isNashAtContinuation_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile := by
  constructor
  · intro hnash who strategy
    rw [
      ← evaluation.expectedUtility_eq_continuationExpectedUtility_of_compatible
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root (hcompatible.2 who strategy) who,
      ← evaluation.expectedUtility_eq_continuationExpectedUtility_of_compatible
        (assembly.toKernelBehavioralProfile profile)
        root hcompatible.1 who]
    exact hnash who strategy
  · intro hnash who strategy
    rw [
      evaluation.expectedUtility_eq_continuationExpectedUtility_of_compatible
        (assembly.toKernelBehavioralProfile
          (MeasurableKernelPresentation.ProfileAssembly.PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root (hcompatible.2 who strategy) who,
      evaluation.expectedUtility_eq_continuationExpectedUtility_of_compatible
        (assembly.toKernelBehavioralProfile profile)
        root hcompatible.1 who]
    exact hnash who strategy

/-- Rootwise deviation compatibility transfers all selected-root Nash tests
between fresh and absolute continuation semantics. -/
theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile := by
  constructor <;>
    intro hnash root hroot
  · exact
      (evaluation.isNashAt_iff_isNashAtContinuation_of_compatible
        assembly root profile
        (hcompatible root hroot)).mp
          (hnash root hroot)
  · exact
      (evaluation.isNashAt_iff_isNashAtContinuation_of_compatible
        assembly root profile
        (hcompatible root hroot)).mpr
          (hnash root hroot)

/-- Under compatibility at every root of an explicit presentation and for
every unilateral deviation, fresh-restart Nash is exactly absolute-prefix
continuation Nash on that presentation. -/
theorem isNashOnFreshRestartPresentation_iff_isNashOnPresentation_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : G.RootPresentation)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationCompatibleOn
        roots.IsRoot profile) :
    evaluation.IsNashOnFreshRestartPresentation
        assembly roots profile ↔
      evaluation.IsNashOnPresentation assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_compatible
    assembly roots.IsRoot profile hcompatible

/-- Under compatibility on an explicit lawful subgame system, fresh-restart
subgame perfection on that system is exactly absolute-prefix subgame
perfection on the same system. -/
theorem isFreshRestartSubgamePerfectOn_iff_isSubgamePerfectOn_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.SubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationCompatibleOn
        system.IsRoot profile) :
    evaluation.IsFreshRestartSubgamePerfectOn
        assembly system profile ↔
      evaluation.IsSubgamePerfectOn
        assembly system profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_compatible
    assembly system.IsRoot profile hcompatible

/-- Under deviation-complete compatibility on every structurally lawful root,
fresh-restart standard SPE is exactly absolute-prefix standard SPE. -/
theorem isFreshRestartStandardSubgamePerfect_iff_isStandardSubgamePerfect_of_compatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (system : G.CompleteSubgameSystem)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationCompatibleOn
        system.toSubgameSystem.IsRoot profile) :
    evaluation.IsFreshRestartStandardSubgamePerfect
        assembly system profile ↔
      evaluation.IsStandardSubgamePerfect
        assembly system profile :=
  evaluation.isFreshRestartSubgamePerfectOn_iff_isSubgamePerfectOn_of_compatible
    assembly system.toSubgameSystem profile hcompatible

/-- Deviation-complete distributional local step compatibility suffices for
rootwise fresh/absolute Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationPartialStepCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_compatible
    assembly root profile hcompatible.state

/-- Distributional local step compatibility on all selected roots suffices
for selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_partialStepCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationPartialStepCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_compatible
    assembly roots profile hcompatible.state

/-- Generated-law almost-everywhere one-step kernel compatibility suffices
for rootwise fresh/absolute Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_stepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
    assembly root profile hcompatible.partialStep

/-- Generated-law almost-everywhere one-step compatibility on selected roots
suffices for selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_stepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_partialStepCompatible
    assembly roots profile hcompatible.partialStep

/-- Canonically rooted pointwise one-step compatibility suffices for
rootwise fresh/absolute Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_rootedStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
    assembly root profile hcompatible.partialStep

/-- Canonically rooted pointwise compatibility on selected roots suffices
for selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_rootedStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_partialStepCompatible
    assembly roots profile hcompatible.partialStep

/-- Primitive canonically rooted next-event compatibility suffices for
rootwise fresh/absolute Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_rootedPathStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
    assembly root profile hcompatible.partialStep

/-- Primitive canonically rooted next-event compatibility on selected roots
suffices for selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_rootedPathStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_partialStepCompatible
    assembly roots profile hcompatible.partialStep

/-- Rooted behavioral action-kernel rebasing suffices for rootwise
fresh-restart/absolute-continuation Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_rootedActionKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_partialStepCompatible
    assembly root profile hcompatible.partialStep

/-- Rooted behavioral action-kernel rebasing on selected roots suffices for
selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_rootedActionKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_partialStepCompatible
    assembly roots profile hcompatible.partialStep

/-- A deviation-complete root-uniform behavioral certificate suffices for
rootwise fresh-restart/absolute-continuation Nash equivalence at any root. -/
private theorem isNashAt_iff_isNashAtContinuation_of_rootUniformActionKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatible
        profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_rootedActionKernelCompatible
    assembly root profile (hcompatible.at root)

/-- A deviation-complete root-uniform behavioral certificate suffices for
selected-root Nash equivalence for any root predicate. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_rootUniformActionKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatible
        profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_rootedActionKernelCompatible
    assembly roots profile (hcompatible.on roots)

/-- Pointwise one-step kernel compatibility suffices for rootwise
fresh/absolute Nash equivalence. -/
private theorem isNashAt_iff_isNashAtContinuation_of_pointwiseStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
        root profile) :
    evaluation.IsNashAt assembly root profile ↔
      evaluation.IsNashAtContinuation
        assembly root profile :=
  evaluation.isNashAt_iff_isNashAtContinuation_of_stepKernelCompatible
    assembly root profile hcompatible.stepKernel

/-- Pointwise one-step compatibility on selected roots suffices for
selected-root Nash equivalence. -/
private theorem isNashOnFreshRestarts_iff_isNashOnContinuations_of_pointwiseStepKernelCompatible
    {presentation : G.MeasurableKernelPresentation model}
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile)
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleOn
        roots profile) :
    evaluation.IsNashOnFreshRestarts
        assembly roots profile ↔
      evaluation.IsNashOnContinuations
        assembly roots profile :=
  evaluation.isNashOnFreshRestarts_iff_isNashOnContinuations_of_stepKernelCompatible
    assembly roots profile hcompatible.stepKernel

end MeasurableHistoryModel.BoundedPathUtility

end ExtensiveGame.ObservedGame
