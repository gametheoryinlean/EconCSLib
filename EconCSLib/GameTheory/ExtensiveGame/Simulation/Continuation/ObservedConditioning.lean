/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Conditioning
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed

/-!
# Continuation.ObservedConditioning — observed conditional compatibility

This module lifts the raw positive-prefix conditional compatibility theorem
to canonical observed-game histories.

For a profile started from `initialHistory`, certified data supplies:

* the marginal mass of another complete history's canonical event prefix;
* the regular conditional shifted event-path law at that prefix;
* its state-path projection;
* bounded expected utility under that conditional state law.

When the canonical prefix has nonzero marginal mass, these laws and expected
utilities agree exactly with constructive absolute-prefix continuation.
The conditional data projections require an explicit nonzero-mass witness;
there is no conditional-law value at a null history. `Nonempty` theorems
establish analytic existence without installing runtime instances.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableKernelPresentation.KernelBehavioralProfile

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Supplied masses and conditional laws at canonical histories.

Conditioning is partial: event and state laws can be projected only with a
certificate that the conditioning prefix has nonzero mass. Null prefixes
receive no default posterior. -/
class ConditionalContinuation (profile : presentation.KernelBehavioralProfile) where
  /-- Supplied marginal mass of each canonical prefix. -/
  prefixMass : CompleteHistory G → CompleteHistory G → ℝ≥0∞
  /-- The supplied masses agree exactly with the execution prefix laws. -/
  prefixMass_eq : ∀ initialHistory root,
    prefixMass initialHistory root =
      profile.compiledPolicy.prefixMeasure model.toArena_terminalSet_measurable
        initialHistory (MeasurableHistoryModel.canonicalContinuationStart root)
        {model.canonicalContinuationPrefix root}
  /-- Supplied conditional event law on the positive-mass domain. -/
  eventLaw : [StandardBorelSpace (ℕ → model.toArena.PathEvent)] →
    [Nonempty (ℕ → model.toArena.PathEvent)] →
    (initialHistory root : CompleteHistory G) →
    prefixMass initialHistory root ≠ 0 → Measure (ℕ → model.toArena.PathEvent)
  /-- Agreement with the regular conditional kernel on the admitted domain. -/
  eventLaw_eq : ∀ [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)] initialHistory root hpositive,
    eventLaw initialHistory root hpositive =
      profile.compiledPolicy.conditionalTailKernel model.toArena_terminalSet_measurable
        initialHistory (MeasurableHistoryModel.canonicalContinuationStart root)
        (model.canonicalContinuationPrefix root)
  /-- Supplied conditional state law on the same positive-mass domain. -/
  stateLaw : [StandardBorelSpace (ℕ → model.toArena.PathEvent)] →
    [Nonempty (ℕ → model.toArena.PathEvent)] →
    (initialHistory root : CompleteHistory G) →
    prefixMass initialHistory root ≠ 0 → Measure (ℕ → model.toArena.State)
  /-- Exact state projection of the supplied conditional event law. -/
  stateLaw_eq : ∀ [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)] initialHistory root hpositive,
    stateLaw initialHistory root hpositive =
      (eventLaw initialHistory root hpositive).map MeasurableKernelArena.eventPathStates

/-- Conditional laws exist as mathematical data; this proof does not install
an executable or default conditional-law instance. -/
theorem ConditionalContinuation.nonempty
    (profile : presentation.KernelBehavioralProfile) :
    Nonempty (ConditionalContinuation profile) := by
  let mass := fun initialHistory root =>
    profile.compiledPolicy.prefixMeasure model.toArena_terminalSet_measurable
      initialHistory (MeasurableHistoryModel.canonicalContinuationStart root)
      {model.canonicalContinuationPrefix root}
  refine ⟨{
    prefixMass := mass
    prefixMass_eq := fun _ _ => rfl
    eventLaw := by
      intro _ _ initialHistory root _
      exact profile.compiledPolicy.conditionalTailKernel model.toArena_terminalSet_measurable
        initialHistory (MeasurableHistoryModel.canonicalContinuationStart root)
        (model.canonicalContinuationPrefix root)
    eventLaw_eq := by intros; rfl
    stateLaw := by
      intro _ _ initialHistory root _
      exact (profile.compiledPolicy.conditionalTailKernel model.toArena_terminalSet_measurable
        initialHistory (MeasurableHistoryModel.canonicalContinuationStart root)
        (model.canonicalContinuationPrefix root)).map MeasurableKernelArena.eventPathStates
    stateLaw_eq := by intros; rfl }⟩

/-- Supplied marginal probability of the canonical prefix of `root`. -/
def canonicalContinuationPrefixMass
    (profile : presentation.KernelBehavioralProfile)
    [laws : ConditionalContinuation profile]
    (initialHistory root : CompleteHistory G) : ℝ≥0∞ :=
  laws.prefixMass initialHistory root

/-- Supplied conditional event law, defined only at a positive-mass prefix. -/
def conditionalContinuationEventPathMeasure
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    [laws : ConditionalContinuation profile]
    (initialHistory root : CompleteHistory G)
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0) :
    Measure (ℕ → model.toArena.PathEvent) :=
  laws.eventLaw initialHistory root hpositive

/-- Positive-prefix conditioning equals absolute-prefix continuation. -/
theorem conditionalContinuationEventPathMeasure_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    [laws : ConditionalContinuation profile]
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0) :
    profile.conditionalContinuationEventPathMeasure initialHistory root hpositive =
      profile.continuationEventPathMeasure root := by
  change laws.eventLaw initialHistory root hpositive = _
  rw [laws.eventLaw_eq]
  apply profile.compiledPolicy.conditionalTailKernel_apply_eq_tailEventPathMeasureFromPrefix
    model.toArena_terminalSet_measurable initialHistory
    (MeasurableHistoryModel.canonicalContinuationStart root)
    (model.canonicalContinuationPrefix root)
  have hmass := laws.prefixMass_eq initialHistory root
  exact hmass ▸ hpositive

/-- Supplied conditional state law on the positive-mass domain. -/
def conditionalContinuationStatePathMeasure
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    [laws : ConditionalContinuation profile]
    (initialHistory root : CompleteHistory G)
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0) :
    Measure (ℕ → model.toArena.State) :=
  laws.stateLaw initialHistory root hpositive

/-- Conditional state laws retain the exact continuation state projection. -/
theorem conditionalContinuationStatePathMeasure_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    (profile : presentation.KernelBehavioralProfile)
    [laws : ConditionalContinuation profile]
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0) :
    profile.conditionalContinuationStatePathMeasure initialHistory root hpositive =
      profile.continuationStatePathMeasure root := by
  change laws.stateLaw initialHistory root hpositive = _
  rw [laws.stateLaw_eq]
  change (profile.conditionalContinuationEventPathMeasure
    initialHistory root hpositive).map MeasurableKernelArena.eventPathStates = _
  rw [profile.conditionalContinuationEventPathMeasure_eq_continuation
    initialHistory root hpositive]
  rfl

end MeasurableKernelPresentation.KernelBehavioralProfile

namespace MeasurableHistoryModel.BoundedPathUtility

open MeasurableKernelPresentation.KernelBehavioralProfile

variable
  {model : MeasurableHistoryModel G}
  (evaluation : MeasurableHistoryModel.BoundedPathUtility model)

/-- Supplied exact conditional expectations; integration is a certificate,
not a data-producing algorithm. -/
class ConditionalEvaluation
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    [ConditionalContinuation profile] where
  /-- Expected utility for each player at an admitted conditional root. -/
  value : [StandardBorelSpace (ℕ → model.toArena.PathEvent)] →
    [Nonempty (ℕ → model.toArena.PathEvent)] →
    (initialHistory root : CompleteHistory G) →
    profile.canonicalContinuationPrefixMass initialHistory root ≠ 0 → N → ℝ
  /-- The supplied utility is exactly the integral under the supplied state law. -/
  value_eq : ∀ [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)] initialHistory root hpositive i,
    value initialHistory root hpositive i =
      ∫ path, evaluation.utility i path
        ∂profile.conditionalContinuationStatePathMeasure initialHistory root hpositive

/-- Conditional integrals exist without a runtime selection of their values. -/
theorem ConditionalEvaluation.nonempty
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    [ConditionalContinuation profile] :
    Nonempty (ConditionalEvaluation evaluation profile) := by
  exact ⟨{
    value := by
      intro _ _ initialHistory root hpositive i
      exact ∫ path, evaluation.utility i path
        ∂profile.conditionalContinuationStatePathMeasure initialHistory root hpositive
    value_eq := by intros; rfl }⟩

/-- Supplied expected utility under positive-prefix conditioning. -/
def conditionalContinuationExpectedUtility
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    [ConditionalContinuation profile]
    [values : ConditionalEvaluation evaluation profile]
    (initialHistory root : CompleteHistory G)
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0)
    (i : N) : ℝ :=
  values.value initialHistory root hpositive i

/-- Positive-prefix conditional expected utility equals continuation utility. -/
theorem conditionalContinuationExpectedUtility_eq_continuation
    [StandardBorelSpace (ℕ → model.toArena.PathEvent)]
    [Nonempty (ℕ → model.toArena.PathEvent)]
    {presentation : G.MeasurableKernelPresentation model}
    (profile : presentation.KernelBehavioralProfile)
    [ConditionalContinuation profile]
    [values : ConditionalEvaluation evaluation profile]
    (initialHistory root : CompleteHistory G)
    [MeasurableSingletonClass
      (model.toArena.ContinuationPrefix
        (MeasurableHistoryModel.canonicalContinuationStart root))]
    (hpositive : profile.canonicalContinuationPrefixMass initialHistory root ≠ 0)
    (i : N) :
    evaluation.conditionalContinuationExpectedUtility
        profile initialHistory root hpositive i =
      evaluation.continuationExpectedUtility profile root i := by
  change values.value initialHistory root hpositive i = _
  rw [values.value_eq]
  unfold continuationExpectedUtility
  rw [profile.conditionalContinuationStatePathMeasure_eq_continuation
    initialHistory root hpositive]

end MeasurableHistoryModel.BoundedPathUtility

end ExtensiveGame.ObservedGame
