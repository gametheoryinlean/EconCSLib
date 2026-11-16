/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectiveKernelBehavioralProfile
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteRealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core

/-!
# Analytic representation of effective kernel behavioral profiles

This semantic leaf connects the executable finite-law profile adapter to the
existing analytic realized-information and observed-game presentations.

The bridge deliberately requires local representation data.  A measurable
equivalence identifies the finite and analytic abstract-action carriers; the
analytic abstract kernel is required to be the weighted-Dirac interpretation
of the finite abstract law at every represented nonterminal prefix; and every
analytic realization kernel is required to be the weighted-Dirac
interpretation of its prefix-dependent finite realization law.  Pointwise
finite support alone would not prove measurable dependence on a general
information or history carrier.

Under those certificates, the A06 compiler proves exact equality with the
existing analytic `compiledPolicy`.  The established finite-execution bridge
then gives exact equality of every finite event-prefix marginal.  This module
does not manufacture a general infinite path measure from finite data.

## Main results

* `AnalyticRepresentation` — the two local weighted-Dirac representation
  certificates;
* `compiledPolicy_analyticallyRealizedBy` — exact raw-policy correspondence;
* `measure_finitePrefixLawFrom_eq_partialTraj` — exact finite path marginals;
* `ObservedGame.KernelBehavioralProfile.effective_compiledPolicy_analyticallyRealizedBy`
  — specialization to the existing high-level profile over the discrete
  complete-history compatibility model;
* `ObservedGame.KernelBehavioralProfile.effective_measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe`
  — exact complete finite state-prefix marginals of the original high-level
  state-path law.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena.EffectiveKernelBehavioralProfile

universe uI uC uJ uD

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

set_option quotPrecheck false in
local notation "μᵇ[" arena "|" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      @Measure.dirac (KernelArena.toMeasurable arena).ActionBundle
        (KernelArena.toMeasurable arena).actionBundleMeasurable
        (Prod.fst atom) + rest)
    0 atoms

variable
  {A : KernelArena}
  {presentation : A.EffectiveKernelPresentation}

/-- Local analytic representation certificates for one effective profile.

The target analytic information, realization, and policy are explicit
semantic inputs.  They are not used to compute the finite policy. -/
structure AnalyticRepresentation
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (presentation.realization.AbstractAction time)]
    (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)
    (analyticInformation : A.toMeasurable.EventInformation)
    (analyticRealization :
      MeasurableKernelArena.EventInformation.ActionRealization
        analyticInformation)
    (analyticPolicy :
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        analyticRealization) where
  /-- Measurable identification of executable and analytic abstract actions.
  -/
  abstractActionEquiv :
    ∀ time,
      presentation.realization.AbstractAction time ≃ᵐ
        analyticRealization.AbstractAction time
  /-- At each represented nonterminal prefix, the analytic abstract kernel is
  exactly the pushed-forward finite weighted-Dirac law. -/
  abstractKernel_eq :
    ∀ time
      (history : A.toMeasurable.EventPrefix time)
      (hnonterminal :
        ¬ IsEmpty
          (A.Action
            (MeasurableKernelArena.latestEventState time history))),
      analyticPolicy.abstractKernel time
          (analyticInformation.informationAt time history) =
        Measure.map (abstractActionEquiv time)
          μ[(profile.abstractLawAt time
            (EventPrefix.ofAnalytic history)
            (by simpa using hnonterminal)).atoms]
  /-- At each prefix and finite abstract action, the analytic realization
  kernel is exactly the finite concrete law interpreted as weighted Diracs. -/
  realizationKernel_eq :
    ∀ time
      (history : A.toMeasurable.EventPrefix time)
      (abstractAction :
        presentation.realization.AbstractAction time),
      analyticRealization.kernel time
          (history, abstractActionEquiv time abstractAction) =
        μᵇ[A|((presentation.realization.realizationLaw time
            (EventPrefix.ofAnalytic history) abstractAction).map
              fun action =>
                ⟨(EventPrefix.ofAnalytic history).latestState,
                  action⟩).atoms]

/-- The effective profile's raw finite event policy is represented exactly by
the supplied analytic realized-action policy. -/
theorem compiledPolicy_analyticallyRealizedBy
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (presentation.realization.AbstractAction time)]
    (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)
    {analyticInformation : A.toMeasurable.EventInformation}
    {analyticRealization :
      MeasurableKernelArena.EventInformation.ActionRealization
        analyticInformation}
    {analyticPolicy :
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        analyticRealization}
    (representation :
      AnalyticRepresentation profile analyticInformation
        analyticRealization analyticPolicy) :
    letI (state : A.State) :
        Decidable (IsEmpty (A.Action state)) :=
      presentation.terminalDecision state
    profile.compiledPolicy.AnalyticallyRealizedBy
      analyticPolicy.toEventHistoryActionPolicy := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  exact
    profile.toRealizedActionPolicy.toEventHistoryPolicy_analyticallyRealizedBy
      analyticPolicy representation.abstractActionEquiv
        representation.abstractKernel_eq
        representation.realizationKernel_eq

/-- Every bounded event-prefix computation of an effective profile equals the
corresponding analytic partial-trajectory marginal. -/
theorem measure_finitePrefixLawFrom_eq_partialTraj
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (presentation.realization.AbstractAction time)]
    (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)
    {analyticInformation : A.toMeasurable.EventInformation}
    {analyticRealization :
      MeasurableKernelArena.EventInformation.ActionRealization
        analyticInformation}
    {analyticPolicy :
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        analyticRealization}
    (representation :
      AnalyticRepresentation profile analyticInformation
        analyticRealization analyticPolicy)
    (start : ℕ) (initialPrefix : A.EventPrefix start)
    (steps : ℕ) :
    μ[((profile.finitePrefixLawFrom start initialPrefix steps).map
        fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analyticPolicy.toEventHistoryActionPolicy.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  change
    μ[((profile.compiledPolicy.prefixLawFrom
        start initialPrefix steps).map
          fun history => history.toAnalytic).atoms] = _
  exact
    profile.compiledPolicy.measure_prefixLawFrom_eq_partialTraj
      analyticPolicy.toEventHistoryActionPolicy
      (profile.compiledPolicy_analyticallyRealizedBy representation)
      start initialPrefix steps

end KernelArena.EffectiveKernelBehavioralProfile

namespace ExtensiveGame.ObservedGame

universe uN uU

variable {N : Type uN} {U : Type uU}

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

set_option quotPrecheck false in
local notation "μᵇ[" arena "|" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      @Measure.dirac (KernelArena.toMeasurable arena).ActionBundle
        (KernelArena.toMeasurable arena).actionBundleMeasurable
        (Prod.fst atom) + rest)
    0 atoms

/-- The finite deterministic complete-history arena underlying the discrete
compatibility model of an observed game. -/
abbrev finiteKernelHistoryArena (G : ObservedGame N U) : KernelArena :=
  G.base.toArena.historyKernelArena G.base.init

namespace MeasurableKernelPresentation.KernelBehavioralProfile

variable
  {G : ObservedGame N U}
  {effectivePresentation :
    (finiteKernelHistoryArena G).EffectiveKernelPresentation}
  {effectiveProfile :
    KernelArena.EffectiveKernelBehavioralProfile effectivePresentation}
  {analyticPresentation :
    MeasurableKernelPresentation G (MeasurableHistoryModel.discrete G)}
  {analyticProfile : analyticPresentation.KernelBehavioralProfile}

/-- A locally represented effective profile compiles exactly to the existing
high-level `KernelBehavioralProfile.compiledPolicy` over the discrete
complete-history compatibility model. -/
theorem effective_compiledPolicy_analyticallyRealizedBy
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy) :
    letI (state : (finiteKernelHistoryArena G).State) :
        Decidable
          (IsEmpty ((finiteKernelHistoryArena G).Action state)) :=
      effectivePresentation.terminalDecision state
    effectiveProfile.compiledPolicy.AnalyticallyRealizedBy
      analyticProfile.compiledPolicy := by
  letI (state : (finiteKernelHistoryArena G).State) :
      Decidable
        (IsEmpty ((finiteKernelHistoryArena G).Action state)) :=
    effectivePresentation.terminalDecision state
  exact
    effectiveProfile.compiledPolicy_analyticallyRealizedBy representation

/-- At a genuine chance prefix recognized by the executable classifier, the
original presentation's fixed analytic chance kernel is exactly the
weighted-Dirac interpretation of the executable concrete chance law. -/
theorem effective_chanceKernel_eq_measure_chanceLaw
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (time : ℕ)
    (history : (finiteKernelHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty
        ((finiteKernelHistoryArena G).Action history.latestState))
    (hchance :
      effectivePresentation.isChance time history = true)
    (hmover : G.base.mover history.latestState.1 = none) :
    let A := finiteKernelHistoryArena G
    analyticPresentation.chanceKernel time history.toAnalytic =
      μᵇ[A|((effectivePresentation.chanceLaw
        time history hnonterminal).map fun action =>
          ⟨history.latestState, action⟩).atoms] := by
  let A := finiteKernelHistoryArena G
  have hnonterminalAnalytic :
      ¬ IsEmpty
        (A.Action
          (MeasurableKernelArena.latestEventState
            time history.toAnalytic)) := by
    simpa only [KernelArena.EventPrefix.latestEventState_toAnalytic] using
      hnonterminal
  have hgameNonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState
          time history.toAnalytic).1 := by
    simpa only [A, finiteKernelHistoryArena,
      KernelArena.EventPrefix.latestEventState_toAnalytic] using hnonterminal
  have hmoverAnalytic :
      G.base.mover
          (MeasurableKernelArena.latestEventState
            time history.toAnalytic).1 = none := by
    simpa only [KernelArena.EventPrefix.latestEventState_toAnalytic] using
      hmover
  have hlocal :=
    effectiveProfile.toRealizedActionPolicy
      |>.realizedKernel_eq_measure_realizedBundleLaw
        analyticProfile.policy representation.abstractActionEquiv
          representation.abstractKernel_eq
          representation.realizationKernel_eq
          time history.toAnalytic hnonterminalAnalytic
  have hbundle :
      effectiveProfile.toRealizedActionPolicy.realizedBundleLaw
          time history hnonterminal =
        (effectivePresentation.chanceLaw
          time history hnonterminal).map fun action =>
            ⟨history.latestState, action⟩ := by
    change
      (effectiveProfile.compiledPolicy
          time history hnonterminal).map
            (fun action =>
              (⟨history.latestState, action⟩ : A.ActionBundle)) = _
    rw [effectiveProfile.compiledPolicy_of_chance
      time history hnonterminal hchance]
  calc
    analyticPresentation.chanceKernel time history.toAnalytic =
        analyticProfile.policy.realizedKernel
          time history.toAnalytic :=
      (analyticProfile.chance_eq
        time history.toAnalytic hgameNonterminal hmoverAnalytic).symm
    _ = μᵇ[A|(effectiveProfile.toRealizedActionPolicy.realizedBundleLaw
          time history hnonterminal).atoms] := by
      simpa only [A] using hlocal
    _ = μᵇ[A|((effectivePresentation.chanceLaw
          time history hnonterminal).map fun action =>
            ⟨history.latestState, action⟩).atoms] := by
      rw [hbundle]
      rfl

/-- Every effective finite event-prefix law equals the corresponding finite
marginal of the original high-level profile's compiled analytic executor. -/
theorem effective_measure_finitePrefixLawFrom_eq_partialTraj
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (start : ℕ)
    (initialPrefix :
      (finiteKernelHistoryArena G).EventPrefix start)
    (steps : ℕ) :
    let A := finiteKernelHistoryArena G
    μ[((effectiveProfile.finitePrefixLawFrom
        start initialPrefix steps).map
          fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analyticProfile.compiledPolicy.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  exact
    effectiveProfile.measure_finitePrefixLawFrom_eq_partialTraj
      representation start initialPrefix steps

/-- Starting from a complete history, A20 effective finite execution followed
by state projection is exactly the matching finite-prefix marginal of the
original high-level `KernelBehavioralProfile.statePathMeasure` over the
discrete complete-history model.

The effective executor retains the complete event history, including selected
actions, until after it has generated the requested prefix.  This identifies
every finite horizon separately and does not assert equality with the entire
infinite state-path measure. -/
theorem effective_measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe
    [abstractActionMeasurable :
      ∀ time,
        MeasurableSpace
          (effectivePresentation.realization.AbstractAction time)]
    (representation :
      KernelArena.EffectiveKernelBehavioralProfile.AnalyticRepresentation
        effectiveProfile analyticPresentation.information
          analyticPresentation.realization analyticProfile.policy)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ) :
    letI : MeasurableSpace (finiteKernelHistoryArena G).State :=
      (finiteKernelHistoryArena G).toMeasurable.stateMeasurable
    μ[((effectiveProfile.finitePrefixLawFrom
        0 (KernelArena.EventPrefix.initial initialHistory) horizon).map
          fun history (index : Finset.Iic horizon) =>
            history.states ⟨index.1, by
              have hindex := Finset.mem_Iic.mp index.2
              omega⟩).atoms] =
      (analyticProfile.statePathMeasure initialHistory).map
        (Preorder.frestrictLe horizon) := by
  letI : MeasurableSpace (finiteKernelHistoryArena G).State :=
    (finiteKernelHistoryArena G).toMeasurable.stateMeasurable
  let initialPrefix : (finiteKernelHistoryArena G).EventPrefix 0 :=
    KernelArena.EventPrefix.initial initialHistory
  let finitePrefixStates :
      (finiteKernelHistoryArena G).EventPrefix (0 + horizon) →
        (Π _index : Finset.Iic horizon,
          (MeasurableHistoryModel.discrete G).toArena.State) :=
    fun history index =>
      history.states ⟨index.1, by
        have hindex := Finset.mem_Iic.mp index.2
        omega⟩
  let prefixStates :
      (Π _index : Finset.Iic (0 + horizon),
          (MeasurableHistoryModel.discrete G).toArena.PathEvent) →
        (Π _index : Finset.Iic horizon,
          (MeasurableHistoryModel.discrete G).toArena.State) :=
    fun history index =>
      (history ⟨index.1, Finset.mem_Iic.mpr (by
        have hindex := Finset.mem_Iic.mp index.2
        omega)⟩).state
  have hprefixStates_measurable : Measurable prefixStates := by
    exact measurable_pi_lambda _ fun index =>
      MeasurableKernelArena.PathEvent.measurable_state.comp
        (measurable_pi_apply
          (⟨index.1, Finset.mem_Iic.mpr (by
            have hindex := Finset.mem_Iic.mp index.2
            omega)⟩ : Finset.Iic (0 + horizon)))
  have hlaw :
      (effectiveProfile.finitePrefixLawFrom
          0 initialPrefix horizon).map finitePrefixStates =
        ((effectiveProfile.finitePrefixLawFrom
          0 initialPrefix horizon).map
            (fun history => history.toAnalytic)).map prefixStates := by
    simp only [FiniteLaw.map_comp]
    congr 1
  change
    μ[((effectiveProfile.finitePrefixLawFrom
        0 initialPrefix horizon).map finitePrefixStates).atoms] = _
  rw [hlaw]
  rw [← FiniteLaw.measure_map _ _ hprefixStates_measurable]
  have hevent :=
    effective_measure_finitePrefixLawFrom_eq_partialTraj
      representation 0 initialPrefix horizon
  refine (congrArg (Measure.map prefixStates) hevent).trans ?_
  unfold
    MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe horizon)
    MeasurableKernelArena.measurable_eventPathStates]
  unfold MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure
  rw [← Kernel.traj_map_frestrictLe_apply
    (κ := analyticProfile.compiledPolicy.pathStepKernel
      (finiteKernelHistoryArena G).toMeasurable_measurableSet_terminalSet)
    0 (0 + horizon) initialPrefix.toAnalytic]
  rw [Measure.map_map hprefixStates_measurable
    (Preorder.measurable_frestrictLe (0 + horizon))]
  congr 1

end MeasurableKernelPresentation.KernelBehavioralProfile

end ExtensiveGame.ObservedGame
