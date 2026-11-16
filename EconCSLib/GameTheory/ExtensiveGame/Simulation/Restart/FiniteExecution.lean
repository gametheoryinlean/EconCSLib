/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates

/-!
# Exact finite execution semantics for fresh restart

This module identifies the executable finite event-prefix restart laws with
the corresponding analytic restart-prefix measures. It keeps the two clocks
separate: absolute continuations retain the supplied prefix clock, while a
fresh restart uses only its latest state and executes from time zero.
It is the restart branch of the semantic compatibility layer.

The executable definitions remain in
`Execution.Discrete.FiniteObservation`. This analytic leaf adds only semantic
equalities and imports no examples.

## Main results

- `measure_freshPrefixLaw_eq_freshRestartFinitePrefixMeasure` identifies the
  direct time-zero executor with the existing fresh-restart prefix measure.
- `measure_absolutePrefixLawFrom_eq_absoluteFinitePrefixMeasureFromPrefix`
  covers every absolute horizon, including deterministic truncation inside
  the retained prefix.
- `measure_splicedFreshAbsolutePrefixLawFrom_eq_splicedFreshFinitePrefixMeasure`
  gives the corresponding all-horizon equality for a fresh continuation
  spliced after the retained prefix.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena

universe uS uA

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

namespace EventPrefix

variable {A : KernelArena} {start offset : ℕ}

/-- Truncating an executable prefix and then reindexing is the analytic
finite-prefix restriction map. -/
theorem toAnalytic_truncate (initial : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    (truncate initial horizon horizon_le).toAnalytic =
      Preorder.frestrictLe₂ horizon_le initial.toAnalytic := by
  funext index
  rfl

/-- Executable finite-prefix splicing is the same coordinate operation as the
analytic restart layer's finite splice after reindexing. -/
theorem toAnalytic_spliceFresh (initial : A.EventPrefix start)
    (fresh : A.EventPrefix offset) :
    (spliceFresh initial fresh).toAnalytic =
      MeasurableKernelArena.spliceContinuationPrefix
        start initial.toAnalytic offset fresh.toAnalytic := by
  funext index
  by_cases hindex : index.1 ≤ start
  · let oldIndex : Fin (start + 1) :=
      ⟨index.1, by omega⟩
    have hsplice := EventPrefix.spliceFresh_oldIndex
      initial fresh oldIndex
    simp only [MeasurableKernelArena.spliceContinuationPrefix,
      EventPrefix.toAnalytic, hindex, dite_true]
    convert hsplice using 1
  · let tailIndex : Fin offset :=
      ⟨index.1 - start - 1, by
        have habsolute := Finset.mem_Iic.mp index.2
        omega⟩
    have hsplice := EventPrefix.spliceFresh_freshIndex
      initial fresh tailIndex
    simp only [MeasurableKernelArena.spliceContinuationPrefix,
      EventPrefix.toAnalytic, hindex, dite_false]
    convert hsplice using 1
    · congr 1
      apply Fin.ext
      simp [EventPrefix.freshIndex, tailIndex]
      omega
    · congr 1
      apply Fin.ext
      simp [tailIndex]
      omega

end EventPrefix

namespace EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

variable (policy : A.EventHistoryPolicy)
variable (analytic : A.toMeasurable.EventHistoryActionPolicy)

/-- The exact fresh-clock executor denotes the analytic partial trajectory
from the matching time-zero event. -/
theorem measure_freshPrefixLaw_eq_partialTraj

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (state : A.State) (steps : ℕ) :
    μ[((policy.freshPrefixLaw state steps).map
      fun history => history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        0 steps (EventPrefix.initial state).toAnalytic := by
  induction steps with
  | zero =>
      rw [freshPrefixLaw_zero, FiniteLaw.pure_map,
        FiniteLaw.measure_pure]
      have hself := congrArg
        (fun kernel => kernel (EventPrefix.initial state).toAnalytic)
        (Kernel.partialTraj_self
          (κ := analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet) 0)
      simpa only [Kernel.id_apply] using hself.symm
  | succ steps ih =>
      let previousLaw : FiniteLaw (A.EventPrefix steps) :=
        policy.freshPrefixLaw state steps
      let nextLaw :
          (Π index : Finset.Iic steps,
              MeasurableKernelArena.EventAt A.toMeasurable index) →
            FiniteLaw (Π index : Finset.Iic (steps + 1),
              MeasurableKernelArena.EventAt A.toMeasurable index) :=
        fun history =>
          (policy.stoppedStepLaw steps
            (EventPrefix.ofAnalytic history)).map fun event =>
              ((EventPrefix.ofAnalytic history).snoc event).toAnalytic
      have hfinite :
          (policy.freshPrefixLaw state (steps + 1)).map
              (fun history => history.toAnalytic) =
            (previousLaw.map fun history => history.toAnalytic).bind nextLaw := by
        rw [freshPrefixLaw_succ, FiniteLaw.map_bind,
          FiniteLaw.bind_map]
        simp only [previousLaw, nextLaw]
        congr
        funext history
        rw [FiniteLaw.map_comp]
        rfl
      rw [hfinite]
      have hnext (history :
          Π index : Finset.Iic steps,
            MeasurableKernelArena.EventAt A.toMeasurable index) :
          μ[(nextLaw history).atoms] =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              steps (steps + 1) history := by
        simpa only [nextLaw, EventPrefix.toAnalytic_ofAnalytic] using
          measure_stoppedStepLaw_map_snoc_eq_partialTraj
            policy analytic realizes steps (EventPrefix.ofAnalytic history)
      have hnextFunction :
          (fun history : Π index : Finset.Iic steps,
              MeasurableKernelArena.EventAt A.toMeasurable index =>
                μ[(nextLaw history).atoms]) =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              steps (steps + 1) := by
        funext history
        exact hnext history
      have hnextMeasurable :
          Measurable fun history : Π index : Finset.Iic steps,
              MeasurableKernelArena.EventAt A.toMeasurable index =>
                μ[(nextLaw history).atoms] := by
        rw [hnextFunction]
        exact Kernel.measurable _
      calc
        μ[((previousLaw.map fun history => history.toAnalytic).bind
              nextLaw).atoms] =
            Measure.bind
              μ[(previousLaw.map fun history => history.toAnalytic).atoms]
              (fun history => μ[(nextLaw history).atoms]) :=
          (FiniteLaw.measure_bind
            (previousLaw.map fun history => history.toAnalytic)
            nextLaw hnextMeasurable).symm
        _ = Measure.bind
              μ[(previousLaw.map fun history => history.toAnalytic).atoms]
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                steps (steps + 1)) := by rw [hnextFunction]
        _ = Measure.bind
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                0 steps (EventPrefix.initial state).toAnalytic)
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                steps (steps + 1)) := by
          simpa only [previousLaw] using congrArg
            (fun measure => Measure.bind measure
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                steps (steps + 1))) ih
        _ = Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              0 (steps + 1) (EventPrefix.initial state).toAnalytic := by
          rw [← Kernel.comp_apply]
          rw [Kernel.partialTraj_comp_partialTraj]
          · exact Nat.zero_le steps
          · exact Nat.le_succ steps

/-- The exact finite fresh-clock law has the analytic
`freshRestartFinitePrefixMeasure` as its Dirac interpretation. -/
theorem measure_freshPrefixLaw_eq_freshRestartFinitePrefixMeasure

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (offset : ℕ) :
    μ[((policy.freshPrefixLaw initialPrefix.latestState offset).map
      fun history => history.toAnalytic).atoms] =
      analytic.freshRestartFinitePrefixMeasure
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic offset := by
  have hinitial :
      (EventPrefix.initial initialPrefix.latestState).toAnalytic =
        (fun _ => A.toMeasurable.initialEvent
          (MeasurableKernelArena.latestEventState
            start initialPrefix.toAnalytic)) := by
    funext index
    rfl
  unfold
    MeasurableKernelArena.EventHistoryActionPolicy.freshRestartFinitePrefixMeasure
  rw [← hinitial]
  exact policy.measure_freshPrefixLaw_eq_partialTraj
    analytic realizes initialPrefix.latestState offset

/-- Mapping the exact fresh-spliced law into the analytic prefix space gives
the existing spliced fresh finite-prefix measure at `start + offset`. -/
theorem measure_freshSplicedPrefixLawFrom_eq_splicedFreshFinitePrefixMeasure

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (offset : ℕ) :
    μ[((policy.freshSplicedPrefixLawFrom start initialPrefix offset).map
      fun history => history.toAnalytic).atoms] =
      analytic.splicedFreshFinitePrefixMeasure
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic (start + offset) := by
  let freshLaw := policy.freshPrefixLaw initialPrefix.latestState offset
  let analyticSplice :=
    MeasurableKernelArena.spliceContinuationPrefix
      start initialPrefix.toAnalytic offset
  have hfinite :
      (policy.freshSplicedPrefixLawFrom start initialPrefix offset).map
          (fun history => history.toAnalytic) =
        (freshLaw.map fun history => history.toAnalytic).map
          analyticSplice := by
    calc
      _ = freshLaw.map
          (fun fresh =>
            (EventPrefix.spliceFresh initialPrefix fresh).toAnalytic) := by
        rw [freshSplicedPrefixLawFrom, FiniteLaw.map_comp]
        rfl
      _ = freshLaw.map
          (fun fresh => analyticSplice fresh.toAnalytic) := by
        congr 2
        funext fresh
        exact EventPrefix.toAnalytic_spliceFresh initialPrefix fresh
      _ = _ := by
        rw [FiniteLaw.map_comp]
        rfl
  rw [hfinite]
  calc
    μ[((freshLaw.map fun history => history.toAnalytic).map
        analyticSplice).atoms] =
        μ[(freshLaw.map fun history => history.toAnalytic).atoms].map
          analyticSplice :=
      (FiniteLaw.measure_map _ _
        (MeasurableKernelArena.measurable_spliceContinuationPrefix
          start initialPrefix.toAnalytic offset)).symm
    _ = (analytic.freshRestartFinitePrefixMeasure
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic offset).map analyticSplice := by
      rw [show freshLaw =
          policy.freshPrefixLaw initialPrefix.latestState offset by rfl]
      rw [policy.measure_freshPrefixLaw_eq_freshRestartFinitePrefixMeasure
        analytic realizes start initialPrefix offset]
    _ = analytic.splicedFreshFinitePrefixMeasure
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic (start + offset) :=
      (analytic.splicedFreshFinitePrefixMeasure_add_eq_map_freshRestart
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic offset).symm

/-- The executable absolute-clock prefix query at `start + steps` denotes the
existing absolute continuation's finite-prefix measure. -/
theorem measure_absolutePrefixLawFrom_add_eq_absoluteFinitePrefixMeasureFromPrefix

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[((policy.absolutePrefixLawFrom
      start initialPrefix (start + steps)).map
        fun history => history.toAnalytic).atoms] =
      analytic.absoluteFinitePrefixMeasureFromPrefix
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic (start + steps) := by
  cases steps with
  | zero =>
      rw [Nat.add_zero]
      rw [absolutePrefixLawFrom_of_le policy start initialPrefix start le_rfl]
      rw [FiniteLaw.pure_map, FiniteLaw.measure_pure]
      unfold
        MeasurableKernelArena.EventHistoryActionPolicy.absoluteFinitePrefixMeasureFromPrefix
      convert (analytic.absolutePathMeasureFromPrefix_map_frestrictLe
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic).symm using 1
  | succ steps =>
      have hnot : ¬ start + (steps + 1) ≤ start := by omega
      have hfinite :
          policy.absolutePrefixLawFrom
              start initialPrefix (start + (steps + 1)) =
            policy.prefixLawFrom start initialPrefix (steps + 1) := by
        have htransport (sourceSteps targetSteps : ℕ)
            (hsteps : sourceSteps = targetSteps) :
            (policy.prefixLawFrom start initialPrefix sourceSteps).map
                (fun history index =>
                  history (Fin.cast (by omega) index)) =
              policy.prefixLawFrom start initialPrefix targetSteps := by
          subst targetSteps
          have hmap :
              (fun history : A.EventPrefix (start + sourceSteps) =>
                (fun index => history (Fin.cast (by omega) index) :
                  A.EventPrefix (start + sourceSteps))) = id := by
            funext history index
            rfl
          rw [hmap, FiniteLaw.map_id]
        rw [absolutePrefixLawFrom]
        simp only [hnot, dite_false]
        have hsteps : start + (steps + 1) - start = steps + 1 := by omega
        exact htransport _ _ hsteps
      rw [hfinite]
      unfold
        MeasurableKernelArena.EventHistoryActionPolicy.absoluteFinitePrefixMeasureFromPrefix
        MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix
      rw [Kernel.traj_map_frestrictLe_apply]
      exact policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start initialPrefix (steps + 1)

/-- Before the continuation point, the executable absolute-prefix query and
the analytic absolute continuation both reduce to the same retained-prefix
restriction. -/
theorem measure_absolutePrefixLawFrom_of_le_eq_absoluteFinitePrefixMeasureFromPrefix

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    μ[((policy.absolutePrefixLawFrom start initialPrefix horizon).map
      fun history => history.toAnalytic).atoms] =
      analytic.absoluteFinitePrefixMeasureFromPrefix
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon := by
  have hstart :
      Measure.dirac initialPrefix.toAnalytic =
        analytic.absoluteFinitePrefixMeasureFromPrefix
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic start := by
    have hquery :=
      policy.measure_absolutePrefixLawFrom_add_eq_absoluteFinitePrefixMeasureFromPrefix
        analytic realizes start initialPrefix 0
    rw [Nat.add_zero] at hquery
    rw [absolutePrefixLawFrom_of_le policy start initialPrefix start le_rfl,
      EventPrefix.truncate_self, FiniteLaw.pure_map,
      FiniteLaw.measure_pure] at hquery
    exact hquery
  rw [absolutePrefixLawFrom_of_le policy start initialPrefix horizon horizon_le]
  rw [FiniteLaw.pure_map, FiniteLaw.measure_pure]
  calc
    Measure.dirac
        (EventPrefix.truncate initialPrefix horizon horizon_le).toAnalytic =
        Measure.dirac
          (Preorder.frestrictLe₂ horizon_le initialPrefix.toAnalytic) := by
      rw [EventPrefix.toAnalytic_truncate]
    _ = (Measure.dirac initialPrefix.toAnalytic).map
          (Preorder.frestrictLe₂ horizon_le) :=
      (Measure.map_dirac'
        (Preorder.measurable_frestrictLe₂ horizon_le)
        initialPrefix.toAnalytic).symm
    _ = (analytic.absoluteFinitePrefixMeasureFromPrefix
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic start).map
            (Preorder.frestrictLe₂ horizon_le) := by rw [hstart]
    _ = analytic.absoluteFinitePrefixMeasureFromPrefix
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic horizon :=
      analytic.absoluteFinitePrefixMeasureFromPrefix_map_frestrictLe₂
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon_le

/-- Before the splice point, the executable and analytic fresh-spliced laws
are both exactly the retained-prefix restriction. -/
theorem measure_splicedFreshAbsolutePrefixLawFrom_of_le_eq_splicedFreshFinitePrefixMeasure

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    μ[((policy.splicedFreshAbsolutePrefixLawFrom
      start initialPrefix horizon).map
        fun history => history.toAnalytic).atoms] =
      analytic.splicedFreshFinitePrefixMeasure
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon := by
  have hstart :
      Measure.dirac initialPrefix.toAnalytic =
        analytic.splicedFreshFinitePrefixMeasure
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic start := by
    have hquery :=
      policy.measure_freshSplicedPrefixLawFrom_eq_splicedFreshFinitePrefixMeasure
        analytic realizes start initialPrefix 0
    rw [freshSplicedPrefixLawFrom_zero, FiniteLaw.pure_map,
      FiniteLaw.measure_pure] at hquery
    simpa only [Nat.add_zero] using hquery
  rw [splicedFreshAbsolutePrefixLawFrom_of_le
    policy start initialPrefix horizon horizon_le]
  rw [FiniteLaw.pure_map, FiniteLaw.measure_pure]
  calc
    Measure.dirac
        (EventPrefix.truncate initialPrefix horizon horizon_le).toAnalytic =
        Measure.dirac
          (Preorder.frestrictLe₂ horizon_le initialPrefix.toAnalytic) := by
      rw [EventPrefix.toAnalytic_truncate]
    _ = (Measure.dirac initialPrefix.toAnalytic).map
          (Preorder.frestrictLe₂ horizon_le) :=
      (Measure.map_dirac'
        (Preorder.measurable_frestrictLe₂ horizon_le)
        initialPrefix.toAnalytic).symm
    _ = (analytic.splicedFreshFinitePrefixMeasure
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic start).map
            (Preorder.frestrictLe₂ horizon_le) := by rw [hstart]
    _ = analytic.splicedFreshFinitePrefixMeasure
          A.toMeasurable_measurableSet_terminalSet
          start initialPrefix.toAnalytic horizon :=
      analytic.splicedFreshFinitePrefixMeasure_map_frestrictLe₂
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon_le

/-- At every later horizon `start + steps`, the arbitrary-horizon executable
fresh-splice query denotes the existing analytic spliced finite marginal. -/
theorem measure_splicedFreshAbsolutePrefixLawFrom_add_eq_splicedFreshFinitePrefixMeasure

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[((policy.splicedFreshAbsolutePrefixLawFrom
      start initialPrefix (start + steps)).map
        fun history => history.toAnalytic).atoms] =
      analytic.splicedFreshFinitePrefixMeasure
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic (start + steps) := by
  cases steps with
  | zero =>
      simpa only [Nat.add_zero] using
        policy.measure_splicedFreshAbsolutePrefixLawFrom_of_le_eq_splicedFreshFinitePrefixMeasure
          analytic realizes start initialPrefix start le_rfl
  | succ steps =>
      have hnot : ¬ start + (steps + 1) ≤ start := by omega
      have hfinite :
          policy.splicedFreshAbsolutePrefixLawFrom
              start initialPrefix (start + (steps + 1)) =
            policy.freshSplicedPrefixLawFrom
              start initialPrefix (steps + 1) := by
        have htransport (sourceSteps targetSteps : ℕ)
            (hsteps : sourceSteps = targetSteps) :
            (policy.freshSplicedPrefixLawFrom
              start initialPrefix sourceSteps).map
                (fun history index =>
                  history (Fin.cast (by omega) index)) =
              policy.freshSplicedPrefixLawFrom
                start initialPrefix targetSteps := by
          subst targetSteps
          have hmap :
              (fun history : A.EventPrefix (start + sourceSteps) =>
                (fun index => history (Fin.cast (by omega) index) :
                  A.EventPrefix (start + sourceSteps))) = id := by
            funext history index
            rfl
          rw [hmap, FiniteLaw.map_id]
        rw [splicedFreshAbsolutePrefixLawFrom]
        simp only [hnot, dite_false]
        have hsteps : start + (steps + 1) - start = steps + 1 := by omega
        exact htransport _ _ hsteps
      rw [hfinite]
      exact
        policy.measure_freshSplicedPrefixLawFrom_eq_splicedFreshFinitePrefixMeasure
          analytic realizes start initialPrefix (steps + 1)

/-- The executable absolute-clock query denotes the analytic absolute finite
marginal at every horizon. -/
theorem measure_absolutePrefixLawFrom_eq_absoluteFinitePrefixMeasureFromPrefix

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    μ[((policy.absolutePrefixLawFrom start initialPrefix horizon).map
      fun history => history.toAnalytic).atoms] =
      analytic.absoluteFinitePrefixMeasureFromPrefix
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon := by
  by_cases horizon_le : horizon ≤ start
  · exact
      policy.measure_absolutePrefixLawFrom_of_le_eq_absoluteFinitePrefixMeasureFromPrefix
        analytic realizes start initialPrefix horizon horizon_le
  · have start_le : start ≤ horizon := by omega
    have horizon_eq : start + (horizon - start) = horizon :=
      Nat.add_sub_of_le start_le
    rw [← horizon_eq]
    exact
      policy.measure_absolutePrefixLawFrom_add_eq_absoluteFinitePrefixMeasureFromPrefix
        analytic realizes start initialPrefix (horizon - start)

/-- The arbitrary-horizon executable fresh splice denotes the analytic
spliced fresh finite marginal at every horizon. -/
theorem measure_splicedFreshAbsolutePrefixLawFrom_eq_splicedFreshFinitePrefixMeasure

    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    μ[((policy.splicedFreshAbsolutePrefixLawFrom
      start initialPrefix horizon).map
        fun history => history.toAnalytic).atoms] =
      analytic.splicedFreshFinitePrefixMeasure
        A.toMeasurable_measurableSet_terminalSet
        start initialPrefix.toAnalytic horizon := by
  by_cases horizon_le : horizon ≤ start
  · exact
      policy.measure_splicedFreshAbsolutePrefixLawFrom_of_le_eq_splicedFreshFinitePrefixMeasure
        analytic realizes start initialPrefix horizon horizon_le
  · have start_le : start ≤ horizon := by omega
    have horizon_eq : start + (horizon - start) = horizon :=
      Nat.add_sub_of_le start_le
    rw [← horizon_eq]
    exact
      policy.measure_splicedFreshAbsolutePrefixLawFrom_add_eq_splicedFreshFinitePrefixMeasure
        analytic realizes start initialPrefix (horizon - start)

end EventHistoryPolicy

end KernelArena
