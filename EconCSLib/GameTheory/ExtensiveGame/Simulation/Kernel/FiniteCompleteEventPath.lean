/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteCompleteEventPath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution
import EconCSLib.Math.Probability.FiniteLaw.Measure

/-!
# Analytic finite marginals of bounded complete event paths

This compatibility leaf interprets the executable complete-event-path law as a
finite weighted sum of Dirac measures.  If the supplied analytic policy locally
realizes the executable event policy and the selected finite support is
terminal, every post-start finite prefix and coordinate agrees exactly with the
existing analytic partial trajectory.

The theorems introduce no measure-valued data owner.  The analytic policy and
its local realization certificate remain explicit inputs, and the executable
owner stays measure-free.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena
namespace FiniteCompleteEventPath

universe u

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

variable {A : KernelArena}

/-- The weighted-Dirac interpretation of the complete-path law has exactly the
analytic partial-trajectory marginal at every requested post-start horizon. -/
theorem measure_law_prefix_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) :
    letI : MeasurableSpace A.PathEvent :=
      show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
    μ[(law policy start initialPrefix steps).atoms].map
        (fun path =>
          (pathPrefix path (start + querySteps)).toAnalytic) =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + querySteps) initialPrefix.toAnalytic := by
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  let completeLaw := law policy start initialPrefix steps
  let finitePrefix :=
    fun path : ℕ → A.PathEvent =>
      (pathPrefix path (start + querySteps)).toAnalytic
  have hfinitePrefix : Measurable finitePrefix := by
    dsimp only [finitePrefix, pathPrefix, EventPrefix.toAnalytic]
    rw [measurable_pi_iff]
    intro index
    exact measurable_pi_apply index.1
  calc
    μ[completeLaw.atoms].map finitePrefix =
        μ[(completeLaw.map finitePrefix).atoms] :=
      FiniteLaw.measure_map completeLaw finitePrefix hfinitePrefix
    _ = μ[((policy.prefixLawFrom start initialPrefix querySteps).map
          fun history => history.toAnalytic).atoms] := by
      apply FiniteLaw.measure_eq_of_equivalent
      have h :=
        (law_prefix_all policy start initialPrefix steps terminated
          querySteps).map
            (fun history => history.toAnalytic)
      rw [FiniteLaw.map_comp] at h
      simpa only [completeLaw, finitePrefix, Function.comp_apply] using h
    _ = Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + querySteps) initialPrefix.toAnalytic :=
      policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start initialPrefix querySteps

/-- Every event coordinate of the weighted-Dirac complete-path law agrees with
the matching analytic partial-trajectory coordinate. -/
theorem measure_law_eventCoordinate_eq_partialTraj_map
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) (coordinate : Fin (start + querySteps + 1)) :
    letI : MeasurableSpace A.PathEvent :=
      show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
    μ[(law policy start initialPrefix steps).atoms].map
        (fun path => path coordinate.1) =
      (Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + querySteps) initialPrefix.toAnalytic).map
          (fun history => history
            ⟨coordinate.1,
              Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩) := by
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  let completeLaw := law policy start initialPrefix steps
  let coordinateMap := fun path : ℕ → A.PathEvent => path coordinate.1
  calc
    μ[completeLaw.atoms].map coordinateMap =
        μ[(completeLaw.map coordinateMap).atoms] :=
      FiniteLaw.measure_map completeLaw coordinateMap (by
        simpa only [coordinateMap] using
          (measurable_pi_apply coordinate.1 :
            Measurable fun path : ℕ → A.PathEvent => path coordinate.1))
    _ = μ[(policy.eventCoordinateLawFrom start initialPrefix querySteps
          coordinate).atoms] := by
      apply FiniteLaw.measure_eq_of_equivalent
      simpa only [completeLaw, coordinateMap,
        EventHistoryPolicy.eventCoordinateLawFrom] using
          law_eventCoordinate_all policy start initialPrefix steps terminated
            querySteps coordinate
    _ = (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + querySteps) initialPrefix.toAnalytic).map
            (fun history => history
              ⟨coordinate.1,
                Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩) :=
      policy.measure_eventCoordinateLawFrom_eq_partialTraj_map
        analytic realizes start initialPrefix querySteps coordinate

/-- State projection of every complete-path coordinate agrees with the
matching projected analytic partial-trajectory coordinate. -/
theorem measure_law_stateCoordinate_eq_partialTraj_map
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) (coordinate : Fin (start + querySteps + 1)) :
    letI : MeasurableSpace A.PathEvent :=
      show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
    letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
    μ[(law policy start initialPrefix steps).atoms].map
        (fun path => (path coordinate.1).state) =
      (Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + querySteps) initialPrefix.toAnalytic).map
          (fun history =>
            (history
              ⟨coordinate.1,
                Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩).state) := by
  letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  let completeLaw := law policy start initialPrefix steps
  let coordinateMap :=
    fun path : ℕ → A.PathEvent => (path coordinate.1).state
  calc
    μ[completeLaw.atoms].map coordinateMap =
        μ[(completeLaw.map coordinateMap).atoms] :=
      FiniteLaw.measure_map completeLaw coordinateMap (by
        simpa only [coordinateMap] using
          (@MeasurableKernelArena.PathEvent.measurable_state A.toMeasurable).comp
            ((measurable_pi_apply coordinate.1) :
              Measurable fun path : ℕ → A.toMeasurable.PathEvent =>
                path coordinate.1))
    _ = μ[(policy.stateCoordinateLawFrom start initialPrefix querySteps
          coordinate).atoms] := by
      apply FiniteLaw.measure_eq_of_equivalent
      simpa only [completeLaw, coordinateMap,
        EventHistoryPolicy.stateCoordinateLawFrom,
        EventHistoryPolicy.eventCoordinateLawFrom,
        FiniteLaw.map_comp, Function.comp_apply] using
          law_stateCoordinate_all policy start initialPrefix steps terminated
            querySteps coordinate
    _ = (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + querySteps) initialPrefix.toAnalytic).map
            (fun history =>
              (history
                ⟨coordinate.1,
                  Finset.mem_Iic.mpr
                    (Nat.lt_succ_iff.mp coordinate.2)⟩).state) :=
      policy.measure_stateCoordinateLawFrom_eq_partialTraj_map
        analytic realizes start initialPrefix querySteps coordinate

end FiniteCompleteEventPath
end KernelArena
