/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution

/-!
# Analytic semantics of effective path laws

This semantic leaf relates each finite horizon of an executable coherent path
law to the existing analytic `Kernel.partialTraj` construction.  It also
identifies the executable reindexed event and state tails with every finite
marginal of the existing analytic continuation-tail laws.  It does not turn
the running interface into a measure-valued API, construct an infinite path
measure, or claim decidability for arbitrary measurable path events.

The proofs reuse the finite-execution correspondence.  Thus the only analytic
assumption is an analytic policy that realizes the supplied exact finite
history policy.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena

universe uS uA

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

namespace StateHistoryPolicy

variable {A : KernelArena}

/-- Every horizon of a coherent effective state path law is exactly the
corresponding analytic partial-trajectory marginal. -/
theorem measure_effectivePathLawFrom_prefixLaw_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    μ[(((policy.effectivePathLawFrom start initialPrefix).prefixLaw steps).map
        fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  exact policy.measure_prefixLawFrom_eq_partialTraj
    analytic realizes start initialPrefix steps

/-- The same finite-marginal correspondence for a time-zero rooted state
path law. -/
theorem measure_effectivePathLaw_prefixLaw_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (root : A.State) (steps : ℕ) :
    μ[((policy.effectivePathLaw root).prefixLaw steps |>.map
        fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        0 (0 + steps) (StatePrefix.initial root).toAnalytic := by
  exact policy.measure_effectivePathLawFrom_prefixLaw_eq_partialTraj
    analytic realizes 0 (StatePrefix.initial root) steps

end StateHistoryPolicy

namespace EventHistoryPolicy

variable {A : KernelArena}

/-- The executable reindexed event-tail law through any finite horizon is
exactly the matching finite marginal of the original analytic
`tailEventPathMeasureFromPrefix` law.

The policy still executes at the original absolute clock and sees the whole
supplied event prefix.  This theorem identifies every requested finite tail
prefix; it does not identify an executable object with the complete
infinite-path measure. -/
theorem measure_tailPrefixLawFrom_eq_tailEventPathMeasureFromPrefix_map_frestrictLe
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[((policy.tailPrefixLawFrom start initialPrefix steps).map
        fun history => history.toAnalytic).atoms] =
      (analytic.tailEventPathMeasureFromPrefix
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic).map
          (Preorder.frestrictLe steps) := by
  let tailPrefix :
      (Π _index : Finset.Iic (start + steps),
          A.toMeasurable.PathEvent) →
        (Π _index : Finset.Iic steps,
          A.toMeasurable.PathEvent) :=
    fun history index =>
      history ⟨start + index.1, Finset.mem_Iic.mpr (by
        have hindex := Finset.mem_Iic.mp index.2
        omega)⟩
  have htailPrefix_measurable : Measurable tailPrefix := by
    exact measurable_pi_lambda _ fun index =>
      measurable_pi_apply
        (⟨start + index.1, Finset.mem_Iic.mpr (by
          have hindex := Finset.mem_Iic.mp index.2
          omega)⟩ : Finset.Iic (start + steps))
  have hlaw :
      (policy.tailPrefixLawFrom start initialPrefix steps).map
          (fun history => history.toAnalytic) =
        ((policy.prefixLawFrom start initialPrefix steps).map
          fun history => history.toAnalytic).map tailPrefix := by
    simp only [tailPrefixLawFrom, FiniteLaw.map_comp]
    congr 1
  rw [hlaw]
  rw [← FiniteLaw.measure_map _ _ htailPrefix_measurable]
  rw [policy.measure_prefixLawFrom_eq_partialTraj
    analytic realizes start initialPrefix steps]
  unfold
    MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix
    MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe steps)
    (MeasurableKernelArena.EventHistoryActionPolicy.measurable_tailEventPath
      (A := A.toMeasurable) start)]
  rw [← Kernel.traj_map_frestrictLe_apply
    (κ := analytic.pathStepKernel
      A.toMeasurable_measurableSet_terminalSet)
    start (start + steps) initialPrefix.toAnalytic]
  rw [Measure.map_map htailPrefix_measurable
    (Preorder.measurable_frestrictLe (start + steps))]
  congr 1

/-- Projecting the executable reindexed event tail to states gives exactly
the matching finite marginal of the original analytic
`tailStatePathMeasureFromPrefix` law.

Actions remain available while the executable policy generates the event
history and are forgotten only after execution.  The conclusion covers each
finite state-prefix horizon separately; it is not an equality with the
complete infinite state-path measure. -/
theorem measure_tailPrefixLawFrom_map_states_eq_tailStatePathMeasureFromPrefix_map_frestrictLe
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[((policy.tailPrefixLawFrom start initialPrefix steps).map
        fun history => history.states.toAnalytic).atoms] =
      (analytic.tailStatePathMeasureFromPrefix
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic).map
          (Preorder.frestrictLe steps) := by
  let prefixStates :
      (Π _index : Finset.Iic steps,
          A.toMeasurable.PathEvent) →
        (Π _index : Finset.Iic steps,
          A.toMeasurable.State) :=
    fun history index => (history index).state
  have hprefixStates_measurable : Measurable prefixStates := by
    exact measurable_pi_lambda _ fun index =>
      MeasurableKernelArena.PathEvent.measurable_state.comp
        (measurable_pi_apply index)
  have hlaw :
      (policy.tailPrefixLawFrom start initialPrefix steps).map
          (fun history => history.states.toAnalytic) =
        ((policy.tailPrefixLawFrom start initialPrefix steps).map
          fun history => history.toAnalytic).map prefixStates := by
    simp only [FiniteLaw.map_comp]
    congr 1
  rw [hlaw]
  rw [← FiniteLaw.measure_map _ _ hprefixStates_measurable]
  rw [policy.measure_tailPrefixLawFrom_eq_tailEventPathMeasureFromPrefix_map_frestrictLe
    analytic realizes start initialPrefix steps]
  unfold
    MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix
  rw [Measure.map_map hprefixStates_measurable
    (Preorder.measurable_frestrictLe steps)]
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe steps)
    MeasurableKernelArena.measurable_eventPathStates]
  congr 1

/-- Every horizon of a coherent effective event path law is exactly the
corresponding analytic action-recording partial-trajectory marginal. -/
theorem measure_effectivePathLawFrom_prefixLaw_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[(((policy.effectivePathLawFrom start initialPrefix).prefixLaw steps).map
        fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  exact policy.measure_prefixLawFrom_eq_partialTraj
    analytic realizes start initialPrefix steps

/-- The same finite-marginal correspondence for a time-zero rooted event path
law. -/
theorem measure_effectivePathLaw_prefixLaw_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (root : A.State) (steps : ℕ) :
    μ[((policy.effectivePathLaw root).prefixLaw steps |>.map
        fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        0 (0 + steps) (EventPrefix.initial root).toAnalytic := by
  exact policy.measure_effectivePathLawFrom_prefixLaw_eq_partialTraj
    analytic realizes 0 (EventPrefix.initial root) steps

end EventHistoryPolicy

end KernelArena
