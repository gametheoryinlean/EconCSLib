/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.EffectiveBehavioralProfile

/-!
# Restart.Observed — observed-profile compatibility

This implementation module lifts raw restart certificates to observed
kernel behavioral profiles.  Its canonical semantic endpoint is
`KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`; event,
trajectory, and certificate-specific predicates remain expert proof tools.
It also connects A20 effective execution to every finite marginal of the
absolute-clock continuation event/state laws, the time-zero fresh-restart
state law, and the normalized continuation event law.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace ExtensiveGame.ObservedGame

universe uN

variable {N : Type uN}
variable {G : ObservedGame N ℝ}

namespace MeasurableKernelPresentation.KernelBehavioralProfile

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

variable
  {model : MeasurableHistoryModel G}
  {presentation : G.MeasurableKernelPresentation model}

/-- Full event-path law obtained by restarting a profile at time zero from
`root`. -/
noncomputable def freshRestartEventPathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  profile.compiledPolicy.pathMeasure
    model.toArena_terminalSet_measurable root

/-- Absolute-prefix continuation event law with only tail coordinate zero's
incoming-action occurrence replaced by the fresh initial marker. -/
noncomputable def normalizedContinuationEventPathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  (profile.continuationEventPathMeasure root).map
    MeasurableKernelArena.freshenInitialEvent

/-- A20 effective execution from the complete canonical prefix gives exactly
every finite-prefix marginal of the original high-level absolute-clock
continuation event law.

The finite executor keeps the complete action-recording prefix and calls the
policy at the original absolute time.  Only the returned finite continuation
is reindexed from zero.  The theorem identifies each finite marginal and does
not replace the original infinite-path measure by executable data. -/
theorem effective_measure_tailPrefixLawFrom_eq_continuationEventPathMeasure_map_frestrictLe
    {effectivePresentation :
      (finiteKernelHistoryArena G).EffectiveKernelPresentation}
    {effectiveProfile :
      KernelArena.EffectiveKernelBehavioralProfile effectivePresentation}
    {analyticPresentation :
      MeasurableKernelPresentation G (MeasurableHistoryModel.discrete G)}
    {analyticProfile : analyticPresentation.KernelBehavioralProfile}
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (root : CompleteHistory G)
    (horizon : ℕ) :
    letI (state : (finiteKernelHistoryArena G).State) :
        Decidable
          (IsEmpty ((finiteKernelHistoryArena G).Action state)) :=
      effectivePresentation.terminalDecision state
    let start := MeasurableHistoryModel.canonicalContinuationStart root
    let initialPrefix :
        (finiteKernelHistoryArena G).EventPrefix start :=
      KernelArena.EventPrefix.ofAnalytic
        ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
    μ[((effectiveProfile.compiledPolicy.tailPrefixLawFrom
        start initialPrefix horizon).map fun history =>
          KernelArena.EventPrefix.toAnalytic history).atoms] =
      (analyticProfile.continuationEventPathMeasure root).map
        (Preorder.frestrictLe horizon) := by
  let A := finiteKernelHistoryArena G
  let start := MeasurableHistoryModel.canonicalContinuationStart root
  let initialPrefix : A.EventPrefix start :=
    KernelArena.EventPrefix.ofAnalytic
      ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    effectivePresentation.terminalDecision state
  have realizes :=
    effective_compiledPolicy_analyticallyRealizedBy representation
  have htail :=
    effectiveProfile.compiledPolicy
      |>.measure_tailPrefixLawFrom_eq_tailEventPathMeasureFromPrefix_map_frestrictLe
        analyticProfile.compiledPolicy realizes start initialPrefix horizon
  unfold continuationEventPathMeasure
  simpa only [initialPrefix, start,
    KernelArena.EventPrefix.toAnalytic_ofAnalytic] using htail

/-- Projecting the A20 effective continuation execution to states gives
exactly every finite-prefix marginal of the original high-level
absolute-clock continuation state law.

Actions are retained while future decisions are generated and are forgotten
only in the final projection.  Thus history-dependent strategies still see
the complete canonical prefix. -/
theorem effective_measure_tailPrefixLawFrom_map_states_eq_continuationStatePathMeasure_map_frestrictLe
    {effectivePresentation :
      (finiteKernelHistoryArena G).EffectiveKernelPresentation}
    {effectiveProfile :
      KernelArena.EffectiveKernelBehavioralProfile effectivePresentation}
    {analyticPresentation :
      MeasurableKernelPresentation G (MeasurableHistoryModel.discrete G)}
    {analyticProfile : analyticPresentation.KernelBehavioralProfile}
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (root : CompleteHistory G)
    (horizon : ℕ) :
    letI (state : (finiteKernelHistoryArena G).State) :
        Decidable
          (IsEmpty ((finiteKernelHistoryArena G).Action state)) :=
      effectivePresentation.terminalDecision state
    let start := MeasurableHistoryModel.canonicalContinuationStart root
    let initialPrefix :
        (finiteKernelHistoryArena G).EventPrefix start :=
      KernelArena.EventPrefix.ofAnalytic
        ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
    μ[((effectiveProfile.compiledPolicy.tailPrefixLawFrom
        start initialPrefix horizon).map fun history =>
          history.states.toAnalytic).atoms] =
      (analyticProfile.continuationStatePathMeasure root).map
        (Preorder.frestrictLe horizon) := by
  let A := finiteKernelHistoryArena G
  let start := MeasurableHistoryModel.canonicalContinuationStart root
  let initialPrefix : A.EventPrefix start :=
    KernelArena.EventPrefix.ofAnalytic
      ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    effectivePresentation.terminalDecision state
  have realizes :=
    effective_compiledPolicy_analyticallyRealizedBy representation
  have htail :=
    effectiveProfile.compiledPolicy
      |>.measure_tailPrefixLawFrom_map_states_eq_tailStatePathMeasureFromPrefix_map_frestrictLe
        analyticProfile.compiledPolicy realizes start initialPrefix horizon
  unfold continuationStatePathMeasure
  simpa only [initialPrefix, start,
    KernelArena.EventPrefix.toAnalytic_ofAnalytic] using htail

/-- Starting the A20 effective profile from `root` at time zero and projecting
to states gives exactly every finite-prefix marginal of the original
high-level fresh-restart state law.

This computation deliberately uses the time-zero profile components.  It is
not identified with the absolute-clock continuation law without an additional
restart-compatibility hypothesis. -/
theorem effective_measure_finitePrefixLawFrom_map_states_eq_freshRestartStatePathMeasure_map_frestrictLe
    {effectivePresentation :
      (finiteKernelHistoryArena G).EffectiveKernelPresentation}
    {effectiveProfile :
      KernelArena.EffectiveKernelBehavioralProfile effectivePresentation}
    {analyticPresentation :
      MeasurableKernelPresentation G (MeasurableHistoryModel.discrete G)}
    {analyticProfile : analyticPresentation.KernelBehavioralProfile}
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (root : CompleteHistory G)
    (horizon : ℕ) :
    letI : MeasurableSpace (finiteKernelHistoryArena G).State :=
      (finiteKernelHistoryArena G).toMeasurable.stateMeasurable
    μ[((effectiveProfile.finitePrefixLawFrom
        0 (KernelArena.EventPrefix.initial root) horizon).map
          fun history (index : Finset.Iic horizon) =>
            history.states ⟨index.1, by
              have hindex := Finset.mem_Iic.mp index.2
              omega⟩).atoms] =
      (analyticProfile.freshRestartStatePathMeasure root).map
        (Preorder.frestrictLe horizon) := by
  simpa only [freshRestartStatePathMeasure] using
    effective_measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe
      representation root horizon

/-- A20 effective absolute-clock execution, tail reindexing, and finite
coordinate-zero normalization give exactly every finite-prefix marginal of
the original high-level `normalizedContinuationEventPathMeasure`.

Execution retains the complete canonical event prefix and its absolute clock.
Only after execution is the tail reindexed, and only its coordinate-zero
incoming-action occurrence is replaced by the initial marker at the same
state.  This theorem identifies each finite marginal; it does not identify an
executable object with the entire infinite-path measure. -/
theorem effective_measure_normalizedTailPrefixLawFrom_eq_normalizedContinuationEventPathMeasure_map_frestrictLe
    {effectivePresentation :
      (finiteKernelHistoryArena G).EffectiveKernelPresentation}
    {effectiveProfile :
      KernelArena.EffectiveKernelBehavioralProfile effectivePresentation}
    {analyticPresentation :
      MeasurableKernelPresentation G (MeasurableHistoryModel.discrete G)}
    {analyticProfile : analyticPresentation.KernelBehavioralProfile}
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (root : CompleteHistory G)
    (horizon : ℕ) :
    letI (state : (finiteKernelHistoryArena G).State) :
        Decidable
          (IsEmpty ((finiteKernelHistoryArena G).Action state)) :=
      effectivePresentation.terminalDecision state
    let start := MeasurableHistoryModel.canonicalContinuationStart root
    let initialPrefix :
        (finiteKernelHistoryArena G).EventPrefix start :=
      KernelArena.EventPrefix.ofAnalytic
        ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
    μ[(((effectiveProfile.compiledPolicy.tailPrefixLawFrom
        start initialPrefix horizon).map fun history index =>
          if index.1 = 0 then
            KernelArena.PathEvent.initial (history index).state
          else
            history index).map fun history =>
              KernelArena.EventPrefix.toAnalytic history).atoms] =
      (analyticProfile.normalizedContinuationEventPathMeasure root).map
        (Preorder.frestrictLe horizon) := by
  let A := finiteKernelHistoryArena G
  let start := MeasurableHistoryModel.canonicalContinuationStart root
  let initialPrefix : A.EventPrefix start :=
    KernelArena.EventPrefix.ofAnalytic
      ((MeasurableHistoryModel.discrete G).canonicalContinuationPrefix root)
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    effectivePresentation.terminalDecision state
  let normalizeFinite : A.EventPrefix horizon → A.EventPrefix horizon :=
    fun history index =>
      if index.1 = 0 then
        KernelArena.PathEvent.initial (history index).state
      else
        history index
  let normalizePrefix :
      ((MeasurableHistoryModel.discrete G).toArena.ContinuationPrefix horizon) →
        ((MeasurableHistoryModel.discrete G).toArena.ContinuationPrefix horizon) :=
    fun history index =>
      if index.1 = 0 then
        (MeasurableHistoryModel.discrete G).toArena.initialEvent
          (history index).state
      else
        history index
  have hnormalizePrefix_measurable : Measurable normalizePrefix := by
    apply measurable_pi_lambda
    intro index
    by_cases hindex : index.1 = 0
    · simp only [normalizePrefix, hindex, if_true]
      exact
        (MeasurableHistoryModel.discrete G).toArena.measurable_initialEvent.comp
          (MeasurableKernelArena.PathEvent.measurable_state.comp
            (measurable_pi_apply index))
    · simpa only [normalizePrefix, hindex, if_false] using
        (measurable_pi_apply index :
          Measurable fun history :
              (MeasurableHistoryModel.discrete G).toArena.ContinuationPrefix
                horizon =>
            history index)
  have hlaw :
      ((effectiveProfile.compiledPolicy.tailPrefixLawFrom
          start initialPrefix horizon).map normalizeFinite).map
            (fun history => history.toAnalytic) =
        ((effectiveProfile.compiledPolicy.tailPrefixLawFrom
          start initialPrefix horizon).map
            (fun history => history.toAnalytic)).map normalizePrefix := by
    simp only [FiniteLaw.map_comp]
    congr 1
  have realizes :=
    effective_compiledPolicy_analyticallyRealizedBy representation
  have htail :=
    effectiveProfile.compiledPolicy
      |>.measure_tailPrefixLawFrom_eq_tailEventPathMeasureFromPrefix_map_frestrictLe
        analyticProfile.compiledPolicy realizes start initialPrefix horizon
  have hcontinuation :
      μ[((effectiveProfile.compiledPolicy.tailPrefixLawFrom
          start initialPrefix horizon).map
            fun history => history.toAnalytic).atoms] =
        (analyticProfile.continuationEventPathMeasure root).map
          (Preorder.frestrictLe horizon) := by
    unfold continuationEventPathMeasure
    simpa only [initialPrefix, start,
      KernelArena.EventPrefix.toAnalytic_ofAnalytic] using htail
  change
    μ[(((effectiveProfile.compiledPolicy.tailPrefixLawFrom
        start initialPrefix horizon).map normalizeFinite).map
          fun history => history.toAnalytic).atoms] = _
  rw [hlaw]
  refine (FiniteLaw.measure_map
    ((effectiveProfile.compiledPolicy.tailPrefixLawFrom
      start initialPrefix horizon).map
        fun history => history.toAnalytic)
    normalizePrefix hnormalizePrefix_measurable).symm.trans ?_
  refine (congrArg (Measure.map normalizePrefix) hcontinuation).trans ?_
  unfold normalizedContinuationEventPathMeasure
  rw [Measure.map_map hnormalizePrefix_measurable
    (Preorder.measurable_frestrictLe horizon)]
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe horizon)
    MeasurableKernelArena.measurable_freshenInitialEvent]
  congr 1
  funext path index
  by_cases hindex : index.1 = 0
  · simp [normalizePrefix,
      MeasurableKernelArena.freshenInitialEvent, hindex]
    rw [hindex]
  · simp [normalizePrefix,
      MeasurableKernelArena.freshenInitialEvent, hindex]

/-- Event-level compatibility of fresh restart with absolute continuation at
one root, after normalizing the unavoidable coordinate-zero occurrence
marker. -/
def IsFreshRestartEventCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  profile.freshRestartEventPathMeasure root =
    profile.normalizedContinuationEventPathMeasure root

/-- The actual absolute full path law is exactly the law obtained by
retaining the canonical root prefix and splicing a fresh-clock future after
it. This trajectory-level predicate is a proof target for local step-kernel
compatibility criteria. -/
def IsFreshRestartSplicedTrajectoryAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  profile.compiledPolicy.absolutePathMeasureFromPrefix
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root) =
    profile.compiledPolicy.splicedFreshAbsolutePathMeasure
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Generated-law almost-everywhere one-step kernel compatibility of an
observed profile at one canonical continuation root. -/
def IsFreshRestartStepKernelCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartStepKernelCompatibleAt
      profile.compiledPolicy
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Pointwise one-step kernel compatibility of an observed profile at one
canonical continuation root. -/
def IsFreshRestartPointwiseStepKernelCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartPointwiseStepKernelCompatibleAt
      profile.compiledPolicy
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Canonically rooted pointwise one-step kernel compatibility of an
observed profile at one continuation root. -/
def IsFreshRestartRootedStepKernelCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartRootedStepKernelCompatibleAt
      profile.compiledPolicy
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Primitive canonically rooted next-event compatibility of an observed
profile at one continuation root. -/
def IsFreshRestartRootedPathStepKernelCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartRootedPathStepKernelCompatibleAt
      profile.compiledPolicy
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Canonically rooted behavioral action-kernel rebasing of an observed
profile at one continuation root. -/
def IsFreshRestartRootedActionKernelCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatibleAt
      profile.compiledPolicy
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Root-uniform rooted behavioral action-kernel rebasing of an observed
profile's compiled policy. -/
def IsFreshRestartRootedActionKernelCompatible
    (profile : presentation.KernelBehavioralProfile) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartRootedActionKernelCompatible
    profile.compiledPolicy

/-- Distributional local one-step compatibility of an observed profile at one
canonical continuation root. -/
def IsFreshRestartPartialStepCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  MeasurableKernelArena.EventHistoryActionPolicy.IsFreshRestartPartialStepCompatibleAt
      profile.compiledPolicy
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Pointwise one-step compatibility implies generated-law
almost-everywhere one-step compatibility for an observed profile. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.stepKernel
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPointwiseStepKernelCompatibleAt root) :
    profile.IsFreshRestartStepKernelCompatibleAt root := by
  unfold
    IsFreshRestartPointwiseStepKernelCompatibleAt
    IsFreshRestartStepKernelCompatibleAt
      at *
  exact hcompatible.stepKernel

/-- Global pointwise compatibility implies the weaker canonical-rooted
condition for an observed profile. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.rootedStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPointwiseStepKernelCompatibleAt root) :
    profile.IsFreshRestartRootedStepKernelCompatibleAt root := by
  unfold
    IsFreshRestartPointwiseStepKernelCompatibleAt
    IsFreshRestartRootedStepKernelCompatibleAt
      at *
  exact hcompatible.rootedStep

/-- A root-uniform behavioral certificate supplies the root-scoped
certificate at every observed continuation root. -/
theorem IsFreshRestartRootedActionKernelCompatible.at
    {profile : presentation.KernelBehavioralProfile}
    (hcompatible :
      profile.IsFreshRestartRootedActionKernelCompatible)
    (root : CompleteHistory G) :
    profile.IsFreshRestartRootedActionKernelCompatibleAt root := by
  unfold
    IsFreshRestartRootedActionKernelCompatible
    IsFreshRestartRootedActionKernelCompatibleAt
      at *
  exact
    hcompatible.at
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Rooted behavioral action-kernel rebasing implies primitive rooted
next-event compatibility for an observed profile. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.rootedPathStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedActionKernelCompatibleAt root) :
    profile.IsFreshRestartRootedPathStepKernelCompatibleAt root := by
  unfold
    IsFreshRestartRootedActionKernelCompatibleAt
    IsFreshRestartRootedPathStepKernelCompatibleAt
      at *
  exact
    hcompatible.rootedPathStep
      model.toArena_terminalSet_measurable

/-- Primitive rooted next-event compatibility implies rooted one-step
compatibility for an observed profile. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.rootedStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedPathStepKernelCompatibleAt root) :
    profile.IsFreshRestartRootedStepKernelCompatibleAt root := by
  unfold
    IsFreshRestartRootedPathStepKernelCompatibleAt
    IsFreshRestartRootedStepKernelCompatibleAt
      at *
  exact hcompatible.rootedStep

/-- Primitive rooted next-event compatibility recovers rooted behavioral
action-kernel rebasing for an observed profile. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.rootedAction
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedPathStepKernelCompatibleAt root) :
    profile.IsFreshRestartRootedActionKernelCompatibleAt root := by
  unfold
    IsFreshRestartRootedPathStepKernelCompatibleAt
    IsFreshRestartRootedActionKernelCompatibleAt
      at *
  exact hcompatible.rootedAction

/-- Rooted behavioral action-kernel rebasing implies rooted one-step
compatibility for an observed profile. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.rootedStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedActionKernelCompatibleAt root) :
    profile.IsFreshRestartRootedStepKernelCompatibleAt root :=
  hcompatible.rootedPathStep.rootedStep

/-- Rooted one-step compatibility recovers primitive rooted next-event
compatibility for an observed profile. -/
theorem IsFreshRestartRootedStepKernelCompatibleAt.rootedPathStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedStepKernelCompatibleAt root) :
    profile.IsFreshRestartRootedPathStepKernelCompatibleAt root := by
  unfold
    IsFreshRestartRootedStepKernelCompatibleAt
    IsFreshRestartRootedPathStepKernelCompatibleAt
      at *
  exact hcompatible.rootedPathStep

/-- For observed profiles, primitive rooted next-event compatibility and
rooted one-step compatibility are equivalent. -/
theorem isFreshRestartRootedPathStepKernelCompatibleAt_iff_rootedStep
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    profile.IsFreshRestartRootedPathStepKernelCompatibleAt root ↔
      profile.IsFreshRestartRootedStepKernelCompatibleAt root :=
  ⟨fun hcompatible => hcompatible.rootedStep,
    fun hcompatible => hcompatible.rootedPathStep⟩

/-- For observed profiles, rooted behavioral action-kernel rebasing and
primitive rooted next-event compatibility are equivalent. -/
theorem isFreshRestartRootedActionKernelCompatibleAt_iff_rootedPathStep
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    profile.IsFreshRestartRootedActionKernelCompatibleAt root ↔
      profile.IsFreshRestartRootedPathStepKernelCompatibleAt root :=
  ⟨fun hcompatible => hcompatible.rootedPathStep,
    fun hcompatible => hcompatible.rootedAction⟩

/-- For observed profiles, rooted behavioral action-kernel rebasing and
rooted one-step compatibility are equivalent. -/
theorem isFreshRestartRootedActionKernelCompatibleAt_iff_rootedStep
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    profile.IsFreshRestartRootedActionKernelCompatibleAt root ↔
      profile.IsFreshRestartRootedStepKernelCompatibleAt root :=
  ⟨fun hcompatible => hcompatible.rootedStep,
    fun hcompatible =>
      hcompatible.rootedPathStep.rootedAction⟩

/-- Generated-law almost-everywhere one-step compatibility implies the exact
distributional recurrence for an observed profile. -/
theorem IsFreshRestartStepKernelCompatibleAt.partialStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartStepKernelCompatibleAt root) :
    profile.IsFreshRestartPartialStepCompatibleAt root := by
  unfold
    IsFreshRestartStepKernelCompatibleAt
    IsFreshRestartPartialStepCompatibleAt
      at *
  exact hcompatible.partialStep

/-- Canonically rooted pointwise compatibility implies the exact
distributional recurrence for an observed profile. -/
theorem IsFreshRestartRootedStepKernelCompatibleAt.partialStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedStepKernelCompatibleAt root) :
    profile.IsFreshRestartPartialStepCompatibleAt root := by
  unfold
    IsFreshRestartRootedStepKernelCompatibleAt
    IsFreshRestartPartialStepCompatibleAt
      at *
  exact hcompatible.partialStep

/-- Primitive rooted next-event compatibility implies the exact
distributional recurrence for an observed profile. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.partialStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedPathStepKernelCompatibleAt root) :
    profile.IsFreshRestartPartialStepCompatibleAt root :=
  hcompatible.rootedStep.partialStep

/-- Rooted behavioral action-kernel rebasing implies the exact
distributional recurrence for an observed profile. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.partialStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedActionKernelCompatibleAt root) :
    profile.IsFreshRestartPartialStepCompatibleAt root :=
  hcompatible.rootedStep.partialStep

/-- Pointwise one-step compatibility implies the exact distributional
recurrence for an observed profile. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.partialStep
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPointwiseStepKernelCompatibleAt root) :
    profile.IsFreshRestartPartialStepCompatibleAt root :=
  hcompatible.stepKernel.partialStep

/-- Local distributional step compatibility implies exact equality of the
actual and spliced absolute trajectories. -/
theorem IsFreshRestartPartialStepCompatibleAt.splicedTrajectory
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPartialStepCompatibleAt root) :
    profile.IsFreshRestartSplicedTrajectoryAt root := by
  unfold
    IsFreshRestartPartialStepCompatibleAt
    IsFreshRestartSplicedTrajectoryAt
      at *
  exact
    profile.compiledPolicy.absolutePathMeasureFromPrefix_eq_spliced_of_partialStepCompatible
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)
      hcompatible

/-- Spliced-trajectory compatibility is equivalent to equality of every
complete initial finite-prefix marginal in absolute coordinates. -/
theorem isFreshRestartSplicedTrajectoryAt_iff_finitePrefix
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    profile.IsFreshRestartSplicedTrajectoryAt root ↔
      ∀ horizon,
        (profile.compiledPolicy.absolutePathMeasureFromPrefix
          model.toArena_terminalSet_measurable
          (MeasurableHistoryModel.canonicalContinuationStart root)
          (model.canonicalContinuationPrefix root)).map
            (frestrictLe horizon) =
          (profile.compiledPolicy.splicedFreshAbsolutePathMeasure
            model.toArena_terminalSet_measurable
            (MeasurableHistoryModel.canonicalContinuationStart root)
            (model.canonicalContinuationPrefix root)).map
              (frestrictLe horizon) := by
  unfold IsFreshRestartSplicedTrajectoryAt
  exact
    profile.compiledPolicy.absolutePathMeasureFromPrefix_eq_spliced_iff_finitePrefix
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)

/-- Exact spliced-trajectory compatibility implies normalized full-event
compatibility. -/
theorem IsFreshRestartSplicedTrajectoryAt.event
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (htrajectory :
      profile.IsFreshRestartSplicedTrajectoryAt root) :
    profile.IsFreshRestartEventCompatibleAt root := by
  unfold IsFreshRestartSplicedTrajectoryAt at htrajectory
  unfold
    IsFreshRestartEventCompatibleAt
    freshRestartEventPathMeasure
    normalizedContinuationEventPathMeasure
    continuationEventPathMeasure
  symm
  have hevent :=
    profile.compiledPolicy.tailEventPathMeasureFromPrefix_map_freshen_eq_pathMeasure_of_eq_spliced
      model.toArena_terminalSet_measurable
      (MeasurableHistoryModel.canonicalContinuationStart root)
      (model.canonicalContinuationPrefix root)
      htrajectory
  simpa only [
    model.latestEventState_canonicalContinuationPrefix] using
      hevent

/-- Local distributional step compatibility implies normalized full-event
compatibility. -/
theorem IsFreshRestartPartialStepCompatibleAt.event
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPartialStepCompatibleAt root) :
    profile.IsFreshRestartEventCompatibleAt root :=
  hcompatible.splicedTrajectory.event

/-- State-law compatibility of fresh restart with absolute-prefix
continuation at one root. -/
def IsFreshRestartStateCompatibleAt
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    Prop :=
  profile.freshRestartStatePathMeasure root =
    profile.continuationStatePathMeasure root

/-- Complete normalized event compatibility implies state compatibility. -/
theorem IsFreshRestartEventCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartEventCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root := by
  change
    (profile.compiledPolicy.pathMeasure
      model.toArena_terminalSet_measurable root).map
        MeasurableKernelArena.eventPathStates =
      (profile.continuationEventPathMeasure root).map
        MeasurableKernelArena.eventPathStates
  change
    profile.compiledPolicy.pathMeasure
        model.toArena_terminalSet_measurable root =
      (profile.continuationEventPathMeasure root).map
        MeasurableKernelArena.freshenInitialEvent
    at hcompatible
  rw [hcompatible]
  rw [
    Measure.map_map
      MeasurableKernelArena.measurable_eventPathStates
      MeasurableKernelArena.measurable_freshenInitialEvent]
  congr 1
  funext path
  exact
    MeasurableKernelArena.eventPathStates_freshenInitialEvent
      path

/-- Local distributional step compatibility implies exact state-path
compatibility. -/
theorem IsFreshRestartPartialStepCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPartialStepCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.event.state

/-- Generated-law almost-everywhere one-step compatibility implies exact
state-path compatibility. -/
theorem IsFreshRestartStepKernelCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartStepKernelCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.partialStep.state

/-- Canonically rooted pointwise one-step compatibility implies exact
state-path compatibility. -/
theorem IsFreshRestartRootedStepKernelCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedStepKernelCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.partialStep.state

/-- Primitive rooted next-event compatibility implies exact state-path
compatibility. -/
theorem IsFreshRestartRootedPathStepKernelCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedPathStepKernelCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.partialStep.state

/-- Rooted behavioral action-kernel rebasing implies exact state-path
compatibility. -/
theorem IsFreshRestartRootedActionKernelCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartRootedActionKernelCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.partialStep.state

/-- Pointwise one-step compatibility implies exact state-path
compatibility. -/
theorem IsFreshRestartPointwiseStepKernelCompatibleAt.state
    {profile : presentation.KernelBehavioralProfile}
    {root : CompleteHistory G}
    (hcompatible :
      profile.IsFreshRestartPointwiseStepKernelCompatibleAt root) :
    profile.IsFreshRestartStateCompatibleAt root :=
  hcompatible.stepKernel.state

/-- State compatibility is equivalent to equality of every initial finite
state-path marginal. -/
theorem isFreshRestartStateCompatibleAt_iff_finitePrefix
    (profile : presentation.KernelBehavioralProfile)
    (root : CompleteHistory G) :
    profile.IsFreshRestartStateCompatibleAt root ↔
      ∀ horizon,
        (profile.freshRestartStatePathMeasure root).map
            (frestrictLe horizon) =
          (profile.continuationStatePathMeasure root).map
            (frestrictLe horizon) := by
  unfold IsFreshRestartStateCompatibleAt
  letI :
      IsProbabilityMeasure
        (profile.freshRestartStatePathMeasure root) := by
    unfold freshRestartStatePathMeasure
    infer_instance
  exact
    MeasurableKernelArena.probabilityMeasure_eq_iff_map_frestrictLe_eq
      (profile.freshRestartStatePathMeasure root)
      (profile.continuationStatePathMeasure root)

end MeasurableKernelPresentation.KernelBehavioralProfile

end ExtensiveGame.ObservedGame
