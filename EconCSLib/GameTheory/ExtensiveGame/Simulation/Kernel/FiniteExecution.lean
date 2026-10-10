/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath
import EconCSLib.Math.Probability.FiniteLaw.Measure

/-!
# Finite execution and analytic kernel semantics

This module relates executable history-dependent `FiniteLaw` execution to the
existing Mathlib kernel semantics. It is a semantic compatibility bridge: the finite
executor remains in `Execution.Discrete.HistoryKernel` and does not import
`Measure`, `Kernel`, or infinite paths.

The analytic prefix API uses `Finset.Iic time`, while the executable API uses
`Fin (time + 1)`.  The conversions below are inverse reindexings and preserve
the latest state exactly.  A realization predicate then asks an analytic
policy kernel to denote the finite policy's bundled action law at every
prefix.  This is a genuine local representation condition; no target step or
trajectory equality is supplied by the caller.

An arbitrary function from histories to finite laws need not be measurable
when the state carrier is uncountable.  For that reason this module does not
manufacture an analytic policy from every executable policy. Given a
measurable realization, the theorems derive the state and action-recording
step equalities, including killed action mass and terminal absorption, then
iterate them to arbitrary finite prefix horizons from any supplied prefix.

## Main results

* inverse state/event prefix reindexings between finite and analytic APIs;
* `StateHistoryPolicy.AnalyticallyRealizedBy` and
  `EventHistoryPolicy.AnalyticallyRealizedBy`;
* exact one-step and arbitrary finite-prefix measure equalities for state and
  event execution, including requested state/event coordinate marginals;
* exact finite transition interpretation for recorded action occurrences.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena

universe uS uA

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

namespace StatePrefix

variable {A : KernelArena} {time : ℕ}

/-- Reindex an executable state prefix by the analytic `Finset.Iic` carrier. -/
def toAnalytic (history : A.StatePrefix time) :
    Π _index : Finset.Iic time, A.toMeasurable.State :=
  fun index =>
    history ⟨index.1,
      Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp index.2)⟩

/-- Reindex an analytic state prefix by the executable `Fin` carrier. -/
def ofAnalytic
    (history : Π _index : Finset.Iic time, A.toMeasurable.State) :
    A.StatePrefix time :=
  fun index =>
    history ⟨index.1,
      Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp index.2)⟩

@[simp]
theorem ofAnalytic_toAnalytic (history : A.StatePrefix time) :
    ofAnalytic (history.toAnalytic) = history := by
  funext index
  rfl

@[simp]
theorem toAnalytic_ofAnalytic
    (history : Π _index : Finset.Iic time, A.toMeasurable.State) :
    (ofAnalytic history).toAnalytic = history := by
  funext index
  rfl

@[simp]
theorem latest_ofAnalytic
    (history : Π _index : Finset.Iic time, A.toMeasurable.State) :
    (ofAnalytic history).latest =
      MeasurableKernelArena.latestState time history := by
  rfl

@[simp]
theorem latestState_toAnalytic (history : A.StatePrefix time) :
    MeasurableKernelArena.latestState time history.toAnalytic =
      history.latest := by
  rfl

/-- Executable prefix extension is the same reindexing used by Mathlib's
one-coordinate partial-trajectory extension. -/
theorem toAnalytic_snoc (history : A.StatePrefix time) (state : A.State) :
    (history.snoc state).toAnalytic =
      IicProdIoc (X := fun _ => A.toMeasurable.State) time (time + 1)
        (history.toAnalytic,
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.State) time) state) := by
  funext index
  by_cases h : index.1 ≤ time
  · simp [StatePrefix.toAnalytic, StatePrefix.snoc, IicProdIoc, h, Fin.snoc]
  · have hle : index.1 ≤ time + 1 := Finset.mem_Iic.mp index.2
    have hi : index.1 = time + 1 := by omega
    have hindex : index = ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      exact Subtype.ext hi
    rw [hindex]
    simp [StatePrefix.toAnalytic, StatePrefix.snoc, IicProdIoc,
      MeasurableEquiv.piSingleton, Fin.snoc]

end StatePrefix

namespace EventPrefix

variable {A : KernelArena} {time : ℕ}

/-- Reindex an executable event prefix by the analytic `Finset.Iic` carrier. -/
def toAnalytic (history : A.EventPrefix time) :
    Π _index : Finset.Iic time,
      MeasurableKernelArena.EventAt A.toMeasurable _index :=
  fun index =>
    history ⟨index.1,
      Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp index.2)⟩

/-- Reindex an analytic event prefix by the executable `Fin` carrier. -/
def ofAnalytic
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.EventAt A.toMeasurable index) :
    A.EventPrefix time :=
  fun index =>
    history ⟨index.1,
      Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp index.2)⟩

@[simp]
theorem ofAnalytic_toAnalytic (history : A.EventPrefix time) :
    ofAnalytic (history.toAnalytic) = history := by
  funext index
  rfl

@[simp]
theorem toAnalytic_ofAnalytic
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.EventAt A.toMeasurable index) :
    (ofAnalytic history).toAnalytic = history := by
  funext index
  rfl

@[simp]
theorem latestState_ofAnalytic
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.EventAt A.toMeasurable index) :
    (ofAnalytic history).latestState =
      MeasurableKernelArena.latestEventState time history := by
  rfl

@[simp]
theorem latestEventState_toAnalytic (history : A.EventPrefix time) :
    MeasurableKernelArena.latestEventState time history.toAnalytic =
      history.latestState := by
  rfl

/-- Executable event-prefix extension is the same reindexing used by
Mathlib's one-coordinate partial-trajectory extension. -/
theorem toAnalytic_snoc (history : A.EventPrefix time)
    (event : A.PathEvent) :
    (history.snoc event).toAnalytic =
      IicProdIoc (X := fun _ => A.toMeasurable.PathEvent) time (time + 1)
        (history.toAnalytic,
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.PathEvent) time) event) := by
  funext index
  by_cases h : index.1 ≤ time
  · simp [EventPrefix.toAnalytic, EventPrefix.snoc, IicProdIoc, h, Fin.snoc]
  · have hle : index.1 ≤ time + 1 := Finset.mem_Iic.mp index.2
    have hi : index.1 = time + 1 := by omega
    have hindex : index = ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩ := by
      exact Subtype.ext hi
    rw [hindex]
    simp [EventPrefix.toAnalytic, EventPrefix.snoc, IicProdIoc,
      MeasurableEquiv.piSingleton, Fin.snoc]

end EventPrefix

namespace StateHistoryPolicy

variable {A : KernelArena}

/-- An analytic history policy represents an executable finite history policy
when its action kernel is exactly the finite bundled-action Dirac measure at
every nonterminal prefix and is zero at every terminal prefix. -/
def AnalyticallyRealizedBy
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy) : Prop :=
  ∀ time history,
    analytic.kernel time history =
      match policy.actionLaw? time (StatePrefix.ofAnalytic history) with
      | none => 0
      | some law =>
          law.atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac A.toMeasurable.ActionBundle
                  A.toMeasurable.actionBundleMeasurable atom.1 + rest)
            0

/-- A realized analytic state-history step denotes exactly the executable
terminal-absorbing successor-state law. -/
theorem measure_stoppedStepLaw_eq_pathStepKernel
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (time : ℕ)
    (history : Π _index : Finset.Iic time, A.toMeasurable.State) :
    (policy.stoppedStepLaw time
        (StatePrefix.ofAnalytic history)).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) •
          @Measure.dirac A.toMeasurable.State
            A.toMeasurable.stateMeasurable atom.1 + rest)
      0 =
      analytic.pathStepKernel
        A.toMeasurable_measurableSet_terminalSet time history := by
  let finiteHistory := StatePrefix.ofAnalytic history
  by_cases hterminal : IsEmpty (A.Action finiteHistory.latest)
  · rw [policy.stoppedStepLaw_of_terminal _ _ hterminal]
    have hterminal' :
        IsEmpty (A.Action (MeasurableKernelArena.latestState time history)) := by
      simpa only [finiteHistory, StatePrefix.latest_ofAnalytic] using hterminal
    rw [MeasurableKernelArena.HistoryActionPolicy.pathStepKernel_apply_terminal
      _ _ _ _ hterminal']
    simp only [FiniteLaw.pure_atoms, List.foldr_cons, List.foldr_nil]
    rw [show ((1 : ℚ≥0) : ENNReal) = 1 by
      change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
      norm_num, one_smul, add_zero]
    congr 1
  · rw [policy.stoppedStepLaw_of_nonterminal _ _ hterminal]
    have hnonterminal' :
        ¬ IsEmpty (A.Action (MeasurableKernelArena.latestState time history)) := by
      simpa only [finiteHistory, StatePrefix.latest_ofAnalytic] using hterminal
    rw [MeasurableKernelArena.HistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ _ _ _ hnonterminal']
    · rw [realizes time history]
      rw [policy.actionLaw?_of_nonterminal _ _ hterminal]
      change
        (policy.stepLaw time finiteHistory hterminal).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac A.toMeasurable.State
                  A.toMeasurable.stateMeasurable atom.1 + rest)
            0 =
          (((policy time finiteHistory hterminal).map
              (fun action =>
                (⟨finiteHistory.latest, action⟩ : A.ActionBundle))).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac A.toMeasurable.ActionBundle
                  A.toMeasurable.actionBundleMeasurable atom.1 + rest)
            0).bind
              (fun bundle =>
                (A.next bundle.1 bundle.2).atoms.foldr
                  (fun atom rest =>
                    (atom.2 : ENNReal) •
                      @Measure.dirac A.toMeasurable.State
                        A.toMeasurable.stateMeasurable atom.1 + rest)
                  0)
      let actionBundles : FiniteLaw A.ActionBundle :=
        (policy time finiteHistory hterminal).map fun action =>
          ⟨finiteHistory.latest, action⟩
      let successors : A.ActionBundle → FiniteLaw A.State :=
        fun bundle => A.next bundle.1 bundle.2
      have hstep :
          policy.stepLaw time finiteHistory hterminal =
            actionBundles.bind successors := by
        rw [FiniteLaw.bind_map]
        rfl
      rw [hstep]
      letI : MeasurableSpace A.ActionBundle :=
        A.toMeasurable.actionBundleMeasurable
      letI : MeasurableSpace A.State :=
        A.toMeasurable.stateMeasurable
      exact (FiniteLaw.measure_bind actionBundles successors
        A.toMeasurable.transition.measurable).symm

/-- Extending one executable state prefix and interpreting its finite law as
a measure gives exactly Mathlib's one-step partial trajectory. -/
theorem measure_stoppedStepLaw_map_snoc_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (time : ℕ) (history : A.StatePrefix time) :
    μ[((policy.stoppedStepLaw time history).map fun state =>
        (history.snoc state).toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        time (time + 1) history.toAnalytic := by
  letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (by fun_prop)]
  let stepMeasure : Measure A.toMeasurable.State :=
    (policy.stoppedStepLaw time history).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) •
          @Measure.dirac A.toMeasurable.State
            A.toMeasurable.stateMeasurable atom.1 + rest)
      0
  have hstep :
      analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet time history.toAnalytic =
        stepMeasure := by
    dsimp only [stepMeasure]
    exact (policy.measure_stoppedStepLaw_eq_pathStepKernel
      analytic realizes time history.toAnalytic).symm
  rw [hstep]
  letI : IsProbabilityMeasure stepMeasure := by
    dsimp only [stepMeasure]
    exact FiniteLaw.measure_isProbability _
  letI : IsFiniteMeasure stepMeasure := inferInstance
  letI : SigmaFinite stepMeasure := inferInstance
  letI : SFinite stepMeasure := inferInstance
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hfunction :
      (IicProdIoc (X := fun _ => A.toMeasurable.State) time (time + 1) ∘
          Prod.mk history.toAnalytic) ∘
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.State) time) =
        (fun state => (history.snoc state).toAnalytic) := by
    funext state
    exact (StatePrefix.toAnalytic_snoc history state).symm
  rw [hfunction]
  have hmeasurable :
      Measurable (fun state => (history.snoc state).toAnalytic) := by
    rw [← hfunction]
    exact (measurable_IicProdIoc
      (X := fun _ => A.toMeasurable.State)).comp
        (measurable_const.prodMk
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.State) time).measurable)
  exact (FiniteLaw.measure_map _ _ hmeasurable).symm

/-- For every supplied initial prefix and every finite number of transitions,
the executable state-prefix law is exactly the corresponding analytic
partial-trajectory measure.  The analytic executor keeps the same absolute
clock and the same complete incoming history. -/
theorem measure_prefixLawFrom_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    μ[((policy.prefixLawFrom start initialPrefix steps).map fun history =>
        history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  induction steps with
  | zero =>
      rw [policy.prefixLawFrom_zero, FiniteLaw.pure_map,
        FiniteLaw.measure_pure]
      have hself := congrArg
        (fun kernel => kernel initialPrefix.toAnalytic)
        (Kernel.partialTraj_self
          (κ := analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet) start)
      simpa only [Nat.add_zero, Kernel.id_apply] using hself.symm
  | succ steps ih =>
      let time := start + steps
      let previousLaw : FiniteLaw (A.StatePrefix time) :=
        policy.prefixLawFrom start initialPrefix steps
      let nextLaw :
          (Π _index : Finset.Iic time, A.toMeasurable.State) →
            FiniteLaw (Π _index : Finset.Iic (time + 1),
              A.toMeasurable.State) :=
        fun history =>
          (policy.stoppedStepLaw time
            (StatePrefix.ofAnalytic history)).map fun state =>
              ((StatePrefix.ofAnalytic history).snoc state).toAnalytic
      have hfinite :
          (policy.prefixLawFrom start initialPrefix (steps + 1)).map
              (fun history => history.toAnalytic) =
            (previousLaw.map fun history => history.toAnalytic).bind nextLaw := by
        rw [policy.prefixLawFrom_succ, FiniteLaw.map_bind,
          FiniteLaw.bind_map]
        simp only [previousLaw, nextLaw, time]
        congr
        funext history
        rw [FiniteLaw.map_comp]
        rfl
      rw [hfinite]
      have hnext (history :
          Π _index : Finset.Iic time, A.toMeasurable.State) :
          μ[(nextLaw history).atoms] =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              time (time + 1) history := by
        simpa only [nextLaw, StatePrefix.toAnalytic_ofAnalytic] using
          measure_stoppedStepLaw_map_snoc_eq_partialTraj
            policy analytic realizes time (StatePrefix.ofAnalytic history)
      have hnextFunction :
          (fun history : Π _index : Finset.Iic time,
              A.toMeasurable.State => μ[(nextLaw history).atoms]) =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              time (time + 1) := by
        funext history
        exact hnext history
      have hnextMeasurable :
          Measurable fun history : Π _index : Finset.Iic time,
              A.toMeasurable.State => μ[(nextLaw history).atoms] := by
        rw [hnextFunction]
        exact Kernel.measurable _
      have ih' :
          μ[(previousLaw.map fun history => history.toAnalytic).atoms] =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start time initialPrefix.toAnalytic := by
        simpa only [previousLaw, time] using ih
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
                time (time + 1)) := by rw [hnextFunction]
        _ = Measure.bind
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                start time initialPrefix.toAnalytic)
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                time (time + 1)) := by rw [ih']
        _ = Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start (time + 1) initialPrefix.toAnalytic := by
          rw [← Kernel.comp_apply]
          rw [Kernel.partialTraj_comp_partialTraj]
          · exact Nat.le_add_right start steps
          · exact Nat.le_succ time
        _ = Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start (start + (steps + 1)) initialPrefix.toAnalytic := by
          simp only [time, Nat.add_succ]

/-- A requested executable state coordinate has exactly the corresponding
analytic partial-trajectory marginal. -/
theorem measure_coordinateLawFrom_eq_partialTraj_map
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) :
    letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
    μ[(policy.coordinateLawFrom start initialPrefix steps coordinate).atoms] =
      (Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic).map
          (fun history => history
            ⟨coordinate.1,
              Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩) := by
  letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
  let analyticCoordinate : Finset.Iic (start + steps) :=
    ⟨coordinate.1,
      Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩
  let prefixLaw := policy.prefixLawFrom start initialPrefix steps
  calc
    μ[(policy.coordinateLawFrom start initialPrefix steps coordinate).atoms] =
        μ[((prefixLaw.map fun history => history.toAnalytic).map
          fun history => history analyticCoordinate).atoms] := by
      congr 1
      simp only [StateHistoryPolicy.coordinateLawFrom, prefixLaw,
        FiniteLaw.map_comp]
      congr 2
    _ = μ[(prefixLaw.map fun history => history.toAnalytic).atoms].map
          (fun history => history analyticCoordinate) :=
      (FiniteLaw.measure_map
        (prefixLaw.map fun history => history.toAnalytic)
        (fun history => history analyticCoordinate)
        (measurable_pi_apply analyticCoordinate)).symm
    _ = (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic).map
            (fun history => history analyticCoordinate) := by
      rw [policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start initialPrefix steps]

end StateHistoryPolicy

/-- The analytic recorded transition of an embedded finite arena is exactly
the finite successor law with its selected source action retained. -/
theorem toMeasurable_recordedTransition_apply
    (A : KernelArena) (bundle : A.ActionBundle) :
    A.toMeasurable.recordedTransition bundle =
      ((A.next bundle.1 bundle.2).map
          (fun target =>
            (PathEvent.after bundle.1 bundle.2 target : A.PathEvent))).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac A.toMeasurable.PathEvent inferInstance atom.1 + rest)
        0 := by
  letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
  letI : MeasurableSpace A.ActionBundle :=
    A.toMeasurable.actionBundleMeasurable
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  rw [MeasurableKernelArena.recordedTransition,
    Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply]
  change
    Measure.map
        (fun actionNext : A.ActionBundle × A.State =>
          (actionNext.2, Sum.inr actionNext.1))
        ((Measure.dirac bundle).prod
          (A.toMeasurable.nextMeasure bundle.1 bundle.2)) = _
  let nextMeasure : Measure A.State :=
    (A.next bundle.1 bundle.2).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0
  have hnext :
      A.toMeasurable.nextMeasure bundle.1 bundle.2 = nextMeasure := by
    exact A.toMeasurable_nextMeasure bundle.1 bundle.2
  rw [hnext]
  letI : IsProbabilityMeasure nextMeasure := by
    dsimp only [nextMeasure]
    exact FiniteLaw.measure_isProbability _
  letI : IsFiniteMeasure nextMeasure := inferInstance
  letI : SigmaFinite nextMeasure := inferInstance
  letI : SFinite nextMeasure := inferInstance
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  have hfunction :
      (fun actionNext : A.ActionBundle × A.State =>
        (actionNext.2, Sum.inr actionNext.1)) ∘ Prod.mk bundle =
        (fun target =>
          (PathEvent.after bundle.1 bundle.2 target : A.PathEvent)) := by
    funext target
    rfl
  rw [hfunction]
  exact FiniteLaw.measure_map _ _
    (measurable_id.prodMk measurable_const)

namespace EventHistoryPolicy

variable {A : KernelArena}

/-- Analytic realization of an executable action-recording event-history
policy, including zero action mass at terminal prefixes. -/
def AnalyticallyRealizedBy
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy) : Prop :=
  ∀ time history,
    analytic.kernel time history =
      match policy.actionLaw? time (EventPrefix.ofAnalytic history) with
      | none => 0
      | some law =>
          law.atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac A.toMeasurable.ActionBundle
                  A.toMeasurable.actionBundleMeasurable atom.1 + rest)
            0

/-- A realized analytic event-history step denotes exactly the executable
terminal-absorbing next-event law, including its selected action occurrence. -/
theorem measure_stoppedStepLaw_eq_pathStepKernel
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (time : ℕ)
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.EventAt A.toMeasurable index) :
    (policy.stoppedStepLaw time
        (EventPrefix.ofAnalytic history)).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) •
          @Measure.dirac A.toMeasurable.PathEvent inferInstance atom.1 + rest)
      0 =
      analytic.pathStepKernel
        A.toMeasurable_measurableSet_terminalSet time history := by
  let finiteHistory := EventPrefix.ofAnalytic history
  by_cases hterminal : IsEmpty (A.Action finiteHistory.latestState)
  · rw [policy.stoppedStepLaw_of_terminal _ _ hterminal]
    have hterminal' :
        IsEmpty (A.Action
          (MeasurableKernelArena.latestEventState time history)) := by
      simpa only [finiteHistory, EventPrefix.latestState_ofAnalytic] using hterminal
    rw [MeasurableKernelArena.EventHistoryActionPolicy.pathStepKernel_apply_terminal
      _ _ _ _ hterminal']
    simp only [FiniteLaw.pure_atoms, List.foldr_cons, List.foldr_nil]
    rw [show ((1 : ℚ≥0) : ENNReal) = 1 by
      change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
      norm_num, one_smul, add_zero]
    congr 1
  · rw [policy.stoppedStepLaw_of_nonterminal _ _ hterminal]
    have hnonterminal' :
        ¬ IsEmpty (A.Action
          (MeasurableKernelArena.latestEventState time history)) := by
      simpa only [finiteHistory, EventPrefix.latestState_ofAnalytic] using hterminal
    rw [MeasurableKernelArena.EventHistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ _ _ _ hnonterminal']
    · rw [realizes time history]
      rw [policy.actionLaw?_of_nonterminal _ _ hterminal]
      let actionBundles : FiniteLaw A.ActionBundle :=
        (policy time finiteHistory hterminal).map fun action =>
          ⟨finiteHistory.latestState, action⟩
      let nextEvents : A.ActionBundle → FiniteLaw A.PathEvent :=
        fun bundle =>
          (A.next bundle.1 bundle.2).map fun target =>
            PathEvent.after bundle.1 bundle.2 target
      have hrecordedEq (bundle : A.ActionBundle) :
          A.toMeasurable.recordedTransition bundle =
            (nextEvents bundle).atoms.foldr
              (fun atom rest =>
                (atom.2 : ENNReal) •
                  @Measure.dirac A.toMeasurable.PathEvent inferInstance
                    atom.1 + rest)
              0 := by
        exact A.toMeasurable_recordedTransition_apply bundle
      have hrecordedFunction :
          (fun bundle : A.ActionBundle =>
            A.toMeasurable.recordedTransition bundle) =
          (fun bundle : A.ActionBundle =>
            (nextEvents bundle).atoms.foldr
              (fun atom rest =>
                (atom.2 : ENNReal) •
                  @Measure.dirac A.toMeasurable.PathEvent inferInstance
                    atom.1 + rest)
              0) := by
        funext bundle
        exact hrecordedEq bundle
      change _ = Measure.bind _
        (fun bundle : A.ActionBundle =>
          A.toMeasurable.recordedTransition bundle)
      rw [hrecordedFunction]
      have hstep :
          policy.stepLaw time finiteHistory hterminal =
            actionBundles.bind nextEvents := by
        rw [FiniteLaw.bind_map]
        rfl
      letI : MeasurableSpace A.State :=
        A.toMeasurable.stateMeasurable
      letI : MeasurableSpace A.ActionBundle :=
        A.toMeasurable.actionBundleMeasurable
      letI : MeasurableSpace A.PathEvent :=
        show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
      have hrecorded :
          Measurable fun bundle : A.ActionBundle =>
            nextEvents bundle |>.atoms.foldr
              (fun atom rest =>
                (atom.2 : ENNReal) •
                  @Measure.dirac A.toMeasurable.PathEvent inferInstance
                    atom.1 + rest)
              0 := by
        simpa only [nextEvents, ← A.toMeasurable_recordedTransition_apply] using
          A.toMeasurable.recordedTransition.measurable
      rw [hstep]
      exact (FiniteLaw.measure_bind actionBundles nextEvents hrecorded).symm

/-- Extending one executable event prefix and interpreting its finite law as
a measure gives exactly Mathlib's one-step event partial trajectory. -/
theorem measure_stoppedStepLaw_map_snoc_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (time : ℕ) (history : A.EventPrefix time) :
    μ[((policy.stoppedStepLaw time history).map fun event =>
        (history.snoc event).toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        time (time + 1) history.toAnalytic := by
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (by fun_prop)]
  let stepMeasure : Measure A.toMeasurable.PathEvent :=
    (policy.stoppedStepLaw time history).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) •
          @Measure.dirac A.toMeasurable.PathEvent inferInstance atom.1 + rest)
      0
  have hstep :
      analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet time history.toAnalytic =
        stepMeasure := by
    dsimp only [stepMeasure]
    exact (policy.measure_stoppedStepLaw_eq_pathStepKernel
      analytic realizes time history.toAnalytic).symm
  rw [hstep]
  letI : IsProbabilityMeasure stepMeasure := by
    dsimp only [stepMeasure]
    exact FiniteLaw.measure_isProbability _
  letI : IsFiniteMeasure stepMeasure := inferInstance
  letI : SigmaFinite stepMeasure := inferInstance
  letI : SFinite stepMeasure := inferInstance
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hfunction :
      (IicProdIoc (X := fun _ => A.toMeasurable.PathEvent) time (time + 1) ∘
          Prod.mk history.toAnalytic) ∘
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.PathEvent) time) =
        (fun event => (history.snoc event).toAnalytic) := by
    funext event
    exact (EventPrefix.toAnalytic_snoc history event).symm
  rw [hfunction]
  have hmeasurable :
      Measurable (fun event => (history.snoc event).toAnalytic) := by
    rw [← hfunction]
    exact (measurable_IicProdIoc
      (X := fun _ => A.toMeasurable.PathEvent)).comp
        (measurable_const.prodMk
          (MeasurableEquiv.piSingleton
            (X := fun _ => A.toMeasurable.PathEvent) time).measurable)
  exact (FiniteLaw.measure_map _ _ hmeasurable).symm

/-- For every supplied initial event prefix and every finite number of
transitions, the executable action-recording prefix law is exactly the
corresponding analytic partial-trajectory measure. -/
theorem measure_prefixLawFrom_eq_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    μ[((policy.prefixLawFrom start initialPrefix steps).map fun history =>
        history.toAnalytic).atoms] =
      Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic := by
  induction steps with
  | zero =>
      rw [policy.prefixLawFrom_zero, FiniteLaw.pure_map,
        FiniteLaw.measure_pure]
      have hself := congrArg
        (fun kernel => kernel initialPrefix.toAnalytic)
        (Kernel.partialTraj_self
          (κ := analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet) start)
      simpa only [Nat.add_zero, Kernel.id_apply] using hself.symm
  | succ steps ih =>
      let time := start + steps
      let previousLaw : FiniteLaw (A.EventPrefix time) :=
        policy.prefixLawFrom start initialPrefix steps
      let nextLaw :
          (Π index : Finset.Iic time,
              MeasurableKernelArena.EventAt A.toMeasurable index) →
            FiniteLaw (Π index : Finset.Iic (time + 1),
              MeasurableKernelArena.EventAt A.toMeasurable index) :=
        fun history =>
          (policy.stoppedStepLaw time
            (EventPrefix.ofAnalytic history)).map fun event =>
              ((EventPrefix.ofAnalytic history).snoc event).toAnalytic
      have hfinite :
          (policy.prefixLawFrom start initialPrefix (steps + 1)).map
              (fun history => history.toAnalytic) =
            (previousLaw.map fun history => history.toAnalytic).bind nextLaw := by
        rw [policy.prefixLawFrom_succ, FiniteLaw.map_bind,
          FiniteLaw.bind_map]
        simp only [previousLaw, nextLaw, time]
        congr
        funext history
        rw [FiniteLaw.map_comp]
        rfl
      rw [hfinite]
      have hnext (history :
          Π index : Finset.Iic time,
            MeasurableKernelArena.EventAt A.toMeasurable index) :
          μ[(nextLaw history).atoms] =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              time (time + 1) history := by
        simpa only [nextLaw, EventPrefix.toAnalytic_ofAnalytic] using
          measure_stoppedStepLaw_map_snoc_eq_partialTraj
            policy analytic realizes time (EventPrefix.ofAnalytic history)
      have hnextFunction :
          (fun history : Π index : Finset.Iic time,
              MeasurableKernelArena.EventAt A.toMeasurable index =>
                μ[(nextLaw history).atoms]) =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              time (time + 1) := by
        funext history
        exact hnext history
      have hnextMeasurable :
          Measurable fun history : Π index : Finset.Iic time,
              MeasurableKernelArena.EventAt A.toMeasurable index =>
                μ[(nextLaw history).atoms] := by
        rw [hnextFunction]
        exact Kernel.measurable _
      have ih' :
          μ[(previousLaw.map fun history => history.toAnalytic).atoms] =
            Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start time initialPrefix.toAnalytic := by
        simpa only [previousLaw, time] using ih
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
                time (time + 1)) := by rw [hnextFunction]
        _ = Measure.bind
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                start time initialPrefix.toAnalytic)
              (Kernel.partialTraj
                (analytic.pathStepKernel
                  A.toMeasurable_measurableSet_terminalSet)
                time (time + 1)) := by rw [ih']
        _ = Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start (time + 1) initialPrefix.toAnalytic := by
          rw [← Kernel.comp_apply]
          rw [Kernel.partialTraj_comp_partialTraj]
          · exact Nat.le_add_right start steps
          · exact Nat.le_succ time
        _ = Kernel.partialTraj
              (analytic.pathStepKernel
                A.toMeasurable_measurableSet_terminalSet)
              start (start + (steps + 1)) initialPrefix.toAnalytic := by
          simp only [time, Nat.add_succ]

/-- A requested executable event coordinate has exactly the corresponding
analytic event partial-trajectory marginal. -/
theorem measure_eventCoordinateLawFrom_eq_partialTraj_map
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) :
    letI : MeasurableSpace A.PathEvent :=
      show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
    μ[(policy.eventCoordinateLawFrom
      start initialPrefix steps coordinate).atoms] =
      (Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic).map
          (fun history => history
            ⟨coordinate.1,
              Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩) := by
  letI : MeasurableSpace A.PathEvent :=
    show MeasurableSpace A.toMeasurable.PathEvent from inferInstance
  let analyticCoordinate : Finset.Iic (start + steps) :=
    ⟨coordinate.1,
      Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩
  let prefixLaw := policy.prefixLawFrom start initialPrefix steps
  calc
    μ[(policy.eventCoordinateLawFrom
        start initialPrefix steps coordinate).atoms] =
        μ[((prefixLaw.map fun history => history.toAnalytic).map
          fun history => history analyticCoordinate).atoms] := by
      congr 1
      simp only [EventHistoryPolicy.eventCoordinateLawFrom, prefixLaw,
        FiniteLaw.map_comp]
      congr 2
    _ = μ[(prefixLaw.map fun history => history.toAnalytic).atoms].map
          (fun history => history analyticCoordinate) :=
      (FiniteLaw.measure_map
        (prefixLaw.map fun history => history.toAnalytic)
        (fun history => history analyticCoordinate)
        (measurable_pi_apply analyticCoordinate)).symm
    _ = (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic).map
            (fun history => history analyticCoordinate) := by
      rw [policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start initialPrefix steps]

/-- State projection after executable event-history execution agrees exactly
with the state projection of the analytic event-coordinate marginal. -/
theorem measure_stateCoordinateLawFrom_eq_partialTraj_map
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) :
    letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
    μ[(policy.stateCoordinateLawFrom
      start initialPrefix steps coordinate).atoms] =
      (Kernel.partialTraj
        (analytic.pathStepKernel
          A.toMeasurable_measurableSet_terminalSet)
        start (start + steps) initialPrefix.toAnalytic).map
          (fun history => (history
            ⟨coordinate.1,
              Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩).state) := by
  letI : MeasurableSpace A.State := A.toMeasurable.stateMeasurable
  let analyticCoordinate : Finset.Iic (start + steps) :=
    ⟨coordinate.1,
      Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp coordinate.2)⟩
  let prefixLaw := policy.prefixLawFrom start initialPrefix steps
  calc
    μ[(policy.stateCoordinateLawFrom
        start initialPrefix steps coordinate).atoms] =
        μ[((prefixLaw.map fun history => history.toAnalytic).map
          fun history => (history analyticCoordinate).state).atoms] := by
      congr 1
      simp only [EventHistoryPolicy.stateCoordinateLawFrom,
        EventHistoryPolicy.eventCoordinateLawFrom, prefixLaw,
        FiniteLaw.map_comp]
      congr 2
    _ = μ[(prefixLaw.map fun history => history.toAnalytic).atoms].map
          (fun history => (history analyticCoordinate).state) :=
      (FiniteLaw.measure_map
        (prefixLaw.map fun history => history.toAnalytic)
        (fun history => (history analyticCoordinate).state)
        (MeasurableKernelArena.PathEvent.measurable_state.comp
          (measurable_pi_apply analyticCoordinate))).symm
    _ = (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic).map
            (fun history => (history analyticCoordinate).state) := by
      rw [policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start initialPrefix steps]

end EventHistoryPolicy

end KernelArena
