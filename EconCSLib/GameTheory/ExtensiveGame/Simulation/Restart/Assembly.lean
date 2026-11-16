/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Observed

/-!
# Restart.Assembly — deviation-complete compatibility

This implementation module packages state-law and certificate
compatibility for a baseline profile and every admitted unilateral deviation.
`FreshRestartDeviationCompatibleAt` and `FreshRestartDeviationCompatibleOn`
are the canonical assembly-level semantic targets.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableKernelPresentation.ProfileAssembly

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Compatibility at one root for the baseline profile and every certified
unilateral deviation compared by the Nash predicates. -/
def FreshRestartDeviationCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt
        (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStateCompatibleAt
          (assembly.toKernelBehavioralProfile
            (PlayerKernelProfile.deviate
              (assembly := assembly)
              profile who strategy))
          root

/-- Compatibility at every root selected by `roots`, including all admitted
unilateral deviations at each root. -/
def FreshRestartDeviationCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationCompatibleAt
      root profile

/-- Generated-law almost-everywhere one-step kernel compatibility at one
root for the baseline and every certified unilateral deviation. -/
def FreshRestartDeviationStepKernelCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStepKernelCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartStepKernelCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Generated-law almost-everywhere one-step kernel compatibility at every
selected root, for both the baseline and every admitted deviation. -/
def FreshRestartDeviationStepKernelCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationStepKernelCompatibleAt
      root profile

/-- Pointwise one-step kernel compatibility at one root for the baseline and
every certified unilateral deviation. -/
def FreshRestartDeviationPointwiseStepKernelCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartPointwiseStepKernelCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartPointwiseStepKernelCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Pointwise one-step kernel compatibility at every selected root, for the
baseline and every admitted deviation. -/
def FreshRestartDeviationPointwiseStepKernelCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
      root profile

/-- Canonically rooted pointwise one-step compatibility at one root for the
baseline and every certified unilateral deviation. -/
def FreshRestartDeviationRootedStepKernelCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedStepKernelCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedStepKernelCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Canonically rooted pointwise one-step compatibility at every selected
root for the baseline and every admitted deviation. -/
def FreshRestartDeviationRootedStepKernelCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
      root profile

/-- Primitive canonically rooted next-event compatibility at one root for
the baseline and every certified unilateral deviation. -/
def FreshRestartDeviationRootedPathStepKernelCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedPathStepKernelCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedPathStepKernelCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Primitive canonically rooted next-event compatibility at every selected
root for the baseline and every admitted deviation. -/
def FreshRestartDeviationRootedPathStepKernelCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
      root profile

/-- Rooted behavioral action-kernel rebasing at one root for the baseline
and every certified unilateral deviation. -/
def FreshRestartDeviationRootedActionKernelCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedActionKernelCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedActionKernelCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Rooted behavioral action-kernel rebasing at every selected root for the
baseline and every admitted deviation. -/
def FreshRestartDeviationRootedActionKernelCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
      root profile

/-- Root-uniform behavioral action-kernel rebasing for the baseline and
every certified unilateral deviation. -/
def FreshRestartDeviationRootedActionKernelCompatible
    (assembly : presentation.ProfileAssembly)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedActionKernelCompatible
      (assembly.toKernelBehavioralProfile profile) ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartRootedActionKernelCompatible
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))

/-- Distributional local step compatibility at one root for the baseline and
every certified unilateral deviation. -/
def FreshRestartDeviationPartialStepCompatibleAt
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartPartialStepCompatibleAt
      (assembly.toKernelBehavioralProfile profile) root ∧
    ∀ (who : N)
      (strategy : assembly.PlayerStrategy who),
      MeasurableKernelPresentation.KernelBehavioralProfile.IsFreshRestartPartialStepCompatibleAt
        (assembly.toKernelBehavioralProfile
          (PlayerKernelProfile.deviate
            (assembly := assembly)
            profile who strategy))
        root

/-- Distributional local step compatibility at every root selected by
`roots`, for both the baseline and all admitted deviations. -/
def FreshRestartDeviationPartialStepCompatibleOn
    (assembly : presentation.ProfileAssembly)
    (roots : CompleteHistory G → Prop)
    (profile : assembly.PlayerKernelProfile) :
    Prop :=
  ∀ root, roots root →
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile

/-- Pointwise deviation-complete one-step compatibility implies the
generated-law almost-everywhere condition. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleAt.stepKernel
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationStepKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.stepKernel,
    fun who strategy =>
      (hcompatible.2 who strategy).stepKernel⟩

/-- Selected-root pointwise compatibility implies selected-root
generated-law almost-everywhere compatibility. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleOn.stepKernel
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationStepKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).stepKernel

/-- Global pointwise deviation-complete compatibility implies the weaker
canonical-rooted condition. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleAt.rootedStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.rootedStep,
    fun who strategy =>
      (hcompatible.2 who strategy).rootedStep⟩

/-- Selected-root global pointwise compatibility implies selected-root
canonical-rooted compatibility. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleOn.rootedStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).rootedStep

/-- A deviation-complete root-uniform behavioral certificate supplies the
root-scoped certificate at every continuation root. -/
theorem FreshRestartDeviationRootedActionKernelCompatible.at
    {assembly : presentation.ProfileAssembly}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatible
        profile)
    (root : CompleteHistory G) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.at root,
    fun who strategy =>
      (hcompatible.2 who strategy).at root⟩

/-- A deviation-complete root-uniform behavioral certificate supplies the
selected-root certificate for any root predicate. -/
theorem FreshRestartDeviationRootedActionKernelCompatible.on
    {assembly : presentation.ProfileAssembly}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatible
        profile)
    (roots : CompleteHistory G → Prop) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
      roots profile :=
  fun root _hroot =>
    hcompatible.at root

/-- Rooted behavioral action-kernel rebasing for the baseline and all
admitted deviations implies primitive rooted next-event compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleAt.rootedPathStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.rootedPathStep,
    fun who strategy =>
      (hcompatible.2 who strategy).rootedPathStep⟩

/-- Selected-root behavioral action-kernel rebasing implies selected-root
primitive next-event compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleOn.rootedPathStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).rootedPathStep

/-- Primitive rooted next-event compatibility for the baseline and all
admitted deviations implies rooted one-step compatibility. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleAt.rootedStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.rootedStep,
    fun who strategy =>
      (hcompatible.2 who strategy).rootedStep⟩

/-- Selected-root primitive rooted next-event compatibility implies
selected-root rooted one-step compatibility. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleOn.rootedStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).rootedStep

/-- Primitive rooted next-event compatibility for the baseline and all
deviations recovers rooted behavioral action-kernel rebasing. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleAt.rootedAction
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.rootedAction,
    fun who strategy =>
      (hcompatible.2 who strategy).rootedAction⟩

/-- Selected-root primitive next-event compatibility recovers selected-root
behavioral action-kernel rebasing. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleOn.rootedAction
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).rootedAction

/-- Deviation-complete rooted behavioral action-kernel rebasing implies
rooted one-step compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleAt.rootedStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
      root profile :=
  hcompatible.rootedPathStep.rootedStep

/-- Selected-root behavioral action-kernel rebasing implies selected-root
rooted one-step compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleOn.rootedStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
      roots profile :=
  hcompatible.rootedPathStep.rootedStep

/-- Rooted one-step compatibility for the baseline and all deviations
recovers primitive rooted next-event compatibility. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleAt.rootedPathStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
      root profile :=
  ⟨hcompatible.1.rootedPathStep,
    fun who strategy =>
      (hcompatible.2 who strategy).rootedPathStep⟩

/-- Selected-root rooted one-step compatibility recovers selected-root
primitive rooted next-event compatibility. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleOn.rootedPathStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).rootedPathStep

/-- Deviation-complete primitive rooted next-event compatibility is
equivalent to deviation-complete rooted one-step compatibility at a root. -/
theorem freshRestartDeviationRootedPathStepKernelCompatibleAt_iff_rootedStep
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile ↔
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile :=
  ⟨fun hcompatible => hcompatible.rootedStep,
    fun hcompatible => hcompatible.rootedPathStep⟩

/-- Deviation-complete rooted behavioral action-kernel rebasing is
equivalent to primitive rooted next-event compatibility at a root. -/
theorem freshRestartDeviationRootedActionKernelCompatibleAt_iff_rootedPathStep
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile ↔
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile :=
  ⟨fun hcompatible => hcompatible.rootedPathStep,
    fun hcompatible => hcompatible.rootedAction⟩

/-- Deviation-complete rooted behavioral action-kernel rebasing is
equivalent to rooted one-step compatibility at a root. -/
theorem freshRestartDeviationRootedActionKernelCompatibleAt_iff_rootedStep
    (assembly : presentation.ProfileAssembly)
    (root : CompleteHistory G)
    (profile : assembly.PlayerKernelProfile) :
    assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile ↔
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile :=
  ⟨fun hcompatible => hcompatible.rootedStep,
    fun hcompatible =>
      hcompatible.rootedPathStep.rootedAction⟩

/-- Generated-law almost-everywhere deviation-complete one-step
compatibility implies the distributional recurrence. -/
theorem FreshRestartDeviationStepKernelCompatibleAt.partialStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile :=
  ⟨hcompatible.1.partialStep,
    fun who strategy =>
      (hcompatible.2 who strategy).partialStep⟩

/-- Selected-root generated-law almost-everywhere compatibility implies the
selected-root distributional recurrence. -/
theorem FreshRestartDeviationStepKernelCompatibleOn.partialStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).partialStep

/-- Canonically rooted deviation-complete one-step compatibility implies the
distributional recurrence. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleAt.partialStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile :=
  ⟨hcompatible.1.partialStep,
    fun who strategy =>
      (hcompatible.2 who strategy).partialStep⟩

/-- Selected-root canonical-rooted compatibility implies the selected-root
distributional recurrence. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleOn.partialStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).partialStep

/-- Primitive rooted next-event compatibility for the baseline and every
deviation implies the distributional recurrence. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleAt.partialStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile :=
  hcompatible.rootedStep.partialStep

/-- Selected-root primitive rooted next-event compatibility implies the
selected-root distributional recurrence. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleOn.partialStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleOn
      roots profile :=
  hcompatible.rootedStep.partialStep

/-- Rooted behavioral action-kernel rebasing for the baseline and every
deviation implies the distributional recurrence. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleAt.partialStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile :=
  hcompatible.rootedStep.partialStep

/-- Selected-root behavioral action-kernel rebasing implies the
selected-root distributional recurrence. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleOn.partialStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleOn
      roots profile :=
  hcompatible.rootedStep.partialStep

/-- Pointwise deviation-complete one-step compatibility implies the
distributional recurrence. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleAt.partialStep
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleAt
      root profile :=
  hcompatible.stepKernel.partialStep

/-- Selected-root pointwise compatibility implies the selected-root
distributional recurrence. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleOn.partialStep
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationPartialStepCompatibleOn
      roots profile :=
  hcompatible.stepKernel.partialStep

/-- Deviation-complete local step compatibility implies the semantic
state-law compatibility used by the equilibrium transfer theorems. -/
theorem FreshRestartDeviationPartialStepCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPartialStepCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  ⟨hcompatible.1.state,
    fun who strategy =>
      (hcompatible.2 who strategy).state⟩

/-- Rootwise local step compatibility implies rootwise semantic state-law
compatibility for the baseline and all deviations. -/
theorem FreshRestartDeviationPartialStepCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPartialStepCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  fun root hroot =>
    (hcompatible root hroot).state

/-- Generated-law almost-everywhere deviation-complete one-step
compatibility implies semantic state-law compatibility. -/
theorem FreshRestartDeviationStepKernelCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  hcompatible.partialStep.state

/-- Selected-root generated-law almost-everywhere compatibility implies
selected-root semantic state-law compatibility. -/
theorem FreshRestartDeviationStepKernelCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  hcompatible.partialStep.state

/-- Canonically rooted deviation-complete one-step compatibility implies
semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  hcompatible.partialStep.state

/-- Selected-root canonical-rooted compatibility implies selected-root
semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedStepKernelCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  hcompatible.partialStep.state

/-- Primitive rooted next-event compatibility for the baseline and every
deviation implies semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  hcompatible.partialStep.state

/-- Selected-root primitive rooted next-event compatibility implies
selected-root semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedPathStepKernelCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedPathStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  hcompatible.partialStep.state

/-- Rooted behavioral action-kernel rebasing for the baseline and every
deviation implies semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  hcompatible.partialStep.state

/-- Selected-root behavioral action-kernel rebasing implies selected-root
semantic state-law compatibility. -/
theorem FreshRestartDeviationRootedActionKernelCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationRootedActionKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  hcompatible.partialStep.state

/-- Pointwise deviation-complete one-step compatibility implies semantic
state-law compatibility. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleAt.state
    {assembly : presentation.ProfileAssembly}
    {root : CompleteHistory G}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleAt
        root profile) :
    assembly.FreshRestartDeviationCompatibleAt
      root profile :=
  hcompatible.stepKernel.state

/-- Selected-root pointwise compatibility implies selected-root semantic
state-law compatibility. -/
theorem FreshRestartDeviationPointwiseStepKernelCompatibleOn.state
    {assembly : presentation.ProfileAssembly}
    {roots : CompleteHistory G → Prop}
    {profile : assembly.PlayerKernelProfile}
    (hcompatible :
      assembly.FreshRestartDeviationPointwiseStepKernelCompatibleOn
        roots profile) :
    assembly.FreshRestartDeviationCompatibleOn
      roots profile :=
  hcompatible.stepKernel.state

end MeasurableKernelPresentation.ProfileAssembly

end ExtensiveGame.ObservedGame
