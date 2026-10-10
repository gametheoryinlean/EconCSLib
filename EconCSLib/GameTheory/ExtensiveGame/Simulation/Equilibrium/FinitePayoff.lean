/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution

/-!
# Analytic semantics of executable finite payoffs

The executable payoff layer computes exact rational expectations from
`FiniteLaw`.  This module proves that those numbers are the Bochner integrals
of the same observables under the library's analytic interpretations.
It is the payoff branch of the semantic compatibility layer and owns no
integral-valued numerical definition.

For deterministic-transition `Arena` histories, the first bridge uses the
finite Dirac interpretation directly.  A second bridge applies to any
caller-supplied complete path law whose coordinate marginals are certified to
be the executable laws.  For `KernelArena`, the state- and action-recording
prefix bridges use `Simulation.Kernel.FiniteExecution` to identify the finite
laws with Mathlib partial trajectories.

All definitions that return numbers remain in `Execution.FinitePayoff` and
use exact rationals.  This file introduces only theorems about real integrals;
it does not replace the executable result by an integral-valued definition.

## Main results

* finite Arena history and supplied-path coordinate integral equalities;
* exact identification of analytic unfinished mass with the executable mass;
* the stopped-payoff error bound computed by `Execution.Truncation`;
* state-prefix partial-trajectory integral equalities;
* event-prefix partial-trajectory integral equalities;
* stopped-payoff variants with the same terminal convention.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

@[reducible] private def piMeasurableSingletonClass
    {index : Type*} [Countable index]
    {coordinate : index → Type*}
    [(i : index) → MeasurableSpace (coordinate i)]
    [(i : index) → MeasurableSingletonClass (coordinate i)] :
    MeasurableSingletonClass ((i : index) → coordinate i) :=
  ⟨fun point => by
    have hsingleton :
        ({point} : Set ((i : index) → coordinate i)) =
          Set.univ.pi (fun i => {point i}) := by
      ext candidate
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
        true_implies]
      constructor
      · intro heq
        subst candidate
        intro i
        rfl
      · intro hcoordinate
        funext i
        exact hcoordinate i
    rw [hsingleton]
    exact MeasurableSet.pi Set.countable_univ fun i _ =>
      measurableSet_singleton (point i)⟩

@[reducible] private def kernelArenaStateMeasurableSingletonClass (A : KernelArena) :
    MeasurableSingletonClass A.toMeasurable.State :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

@[reducible] private def kernelArenaActionBundleMeasurableSingletonClass
    (A : KernelArena) :
    MeasurableSingletonClass A.toMeasurable.ActionBundle :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

@[reducible] private def kernelArenaPathEventMeasurableSingletonClass (A : KernelArena) :
    MeasurableSingletonClass A.toMeasurable.PathEvent := by
  letI := kernelArenaStateMeasurableSingletonClass A
  letI := kernelArenaActionBundleMeasurableSingletonClass A
  have hsum (event : Unit ⊕ A.toMeasurable.ActionBundle) :
      MeasurableSet ({event} : Set (Unit ⊕ A.toMeasurable.ActionBundle)) := by
    cases event with
    | inl unitValue =>
        have heq :
            ({Sum.inl unitValue} : Set (Unit ⊕ A.toMeasurable.ActionBundle)) =
              Sum.inl '' {unitValue} := by
          ext candidate
          simp
        rw [heq]
        exact (measurableSet_singleton unitValue).inl_image
    | inr bundle =>
        have heq :
            ({Sum.inr bundle} : Set (Unit ⊕ A.toMeasurable.ActionBundle)) =
              Sum.inr '' {bundle} := by
          ext candidate
          simp
        rw [heq]
        exact (measurableSet_singleton bundle).inr_image
  refine ⟨fun event => ?_⟩
  have heq :
      ({event} : Set A.toMeasurable.PathEvent) =
        {event.1} ×ˢ {event.2} := by
    ext candidate
    simp
  rw [heq]
  exact (measurableSet_singleton event.1).prod (hsum event.2)

namespace Arena.StochasticHistoryPolicy

variable {A : Arena} {start : A.State}
variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- The exact rational complete-history expectation is the integral under the
finite Dirac interpretation of the executable history law. -/
theorem integral_historyLaw_eq_expectedHistoryPayoffFrom
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (payoff : A.HistoryFrom start → ℚ) :
    (∫ history, (payoff history : ℝ)
        ∂μ[(A.stochasticHistoryLawFrom policy current fuel).atoms]) =
      (policy.expectedHistoryPayoffFrom current fuel payoff : ℝ) := by
  simpa only [expectedHistoryPayoffFrom] using
    FiniteLaw.integral_measure_eq_expectRat
      (A.stochasticHistoryLawFrom policy current fuel) payoff

/-- The executable stopped-history expectation uses exactly the same
terminal test and zero-before-termination convention as its finite integral.
-/
theorem integral_stoppedHistoryLaw_eq_stoppedExpectedPayoffFrom
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (payoff : A.HistoryFrom start → ℚ) :
    (∫ history,
        (if A.IsTerminal history.1 then (payoff history : ℝ) else 0)
        ∂μ[(A.stochasticHistoryLawFrom policy current fuel).atoms]) =
      (policy.stoppedExpectedPayoffFrom current fuel payoff : ℝ) := by
  simpa only [stoppedExpectedPayoffFrom, apply_ite Rat.cast, Rat.cast_zero]
    using policy.integral_historyLaw_eq_expectedHistoryPayoffFrom
      current fuel
      (fun history => if A.IsTerminal history.1 then payoff history else 0)

/-- For any supplied complete path law with the required finite-marginal
certificate, a coordinate payoff integral equals the executable rational
history expectation. -/
theorem integral_pathLaw_coordinate_eq_expectedHistoryPayoffFrom
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          μ[(Arena.pathMarginal policy current time).atoms])
    (time : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (hpayoff : Measurable fun history => (payoff history : ℝ)) :
    (∫ path, (payoff (path time) : ℝ)
        ∂Arena.pathLaw policy current supplied) =
      (policy.expectedHistoryPayoffFrom current time payoff : ℝ) := by
  have hmap := integral_map
    (μ := Arena.pathLaw policy current supplied)
    (φ := fun path => path time)
    (measurable_pi_apply time).aemeasurable
    hpayoff.aestronglyMeasurable
  refine hmap.symm.trans ?_
  rw [Arena.pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    policy current supplied finiteMarginal time]
  exact policy.integral_historyLaw_eq_expectedHistoryPayoffFrom
    current time payoff

/-- The supplied-path coordinate integral also agrees with the exact stopped
payoff when the stopped observable is measurable. -/
theorem integral_pathLaw_stoppedCoordinate_eq_stoppedExpectedPayoffFrom
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          μ[(Arena.pathMarginal policy current time).atoms])
    (time : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (hmeasurable : Measurable fun history : A.HistoryFrom start =>
      if A.IsTerminal history.1 then (payoff history : ℝ) else 0) :
    (∫ path,
        (if A.IsTerminal (path time).1 then (payoff (path time) : ℝ) else 0)
        ∂Arena.pathLaw policy current supplied) =
      (policy.stoppedExpectedPayoffFrom current time payoff : ℝ) := by
  simpa only [stoppedExpectedPayoffFrom, apply_ite Rat.cast, Rat.cast_zero]
    using policy.integral_pathLaw_coordinate_eq_expectedHistoryPayoffFrom
      current supplied finiteMarginal time
      (fun history => if A.IsTerminal history.1 then payoff history else 0)
      (by
        simpa only [apply_ite Rat.cast, Rat.cast_zero] using hmeasurable)

/-- Under the same finite-marginal certificate, the analytic mass of paths
still unfinished at one horizon is exactly the executable rational
`Arena.unfinishedMass`.  This is the probability term used by the truncation
radius; no infinite-path probability is evaluated by the runtime function. -/
theorem pathLaw_unfinishedAt_eq_unfinishedMass
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          μ[(Arena.pathMarginal policy current time).atoms])
    (time : ℕ) :
    Arena.pathLaw policy current supplied
        (Arena.unfinishedAt (A := A) (start := start) time) =
      (Arena.unfinishedMass policy current time : ENNReal) := by
  let unfinishedHistory : Set (A.HistoryFrom start) :=
    {history | ¬ A.IsTerminal history.1}
  have hunfinishedHistory : MeasurableSet unfinishedHistory := by
    exact (Set.to_countable
      (Arena.terminalHistorySet (A := A) (start := start))).measurableSet.compl
  have hevent :
      {history : A.HistoryFrom start |
          decide (¬ A.IsTerminal history.1)} = unfinishedHistory := by
    ext history
    simp [unfinishedHistory]
  have heventMeasurable :
      MeasurableSet {history : A.HistoryFrom start |
        decide (¬ A.IsTerminal history.1)} := by
    rw [hevent]
    exact hunfinishedHistory
  change
    Arena.pathLaw policy current supplied
        ((fun path : ℕ → A.HistoryFrom start => path time) ⁻¹'
          unfinishedHistory) = _
  rw [← Measure.map_apply (measurable_pi_apply time)
    hunfinishedHistory]
  rw [Arena.pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    policy current supplied finiteMarginal time]
  rw [← hevent]
  rw [FiniteLaw.measure_eventMass _ _ heventMeasurable]
  rfl

/-- A bounded complete-path target that agrees with the terminal payoff on
paths finished by `time` differs from the executable stopped center by at
most `bound * unfinishedMass`.  This is the analytic correctness statement
for the radius computed by `Execution.Truncation`; convergence or existence
of a suitable target remains a separate analytic premise. -/
theorem integral_pathLaw_sub_stoppedExpectedPayoffFrom_le_radius
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          μ[(Arena.pathMarginal policy current time).atoms])
    (time : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (target : (ℕ → A.HistoryFrom start) → ℝ)
    (bound : ℚ≥0)
    (htargetIntegrable :
      Integrable target (Arena.pathLaw policy current supplied))
    (hstoppedMeasurable : Measurable fun history : A.HistoryFrom start =>
      if A.IsTerminal history.1 then (payoff history : ℝ) else 0)
    (htargetBound : ∀ path, ‖target path‖ ≤ (bound : ℝ))
    (htargetTerminal : ∀ path,
      A.IsTerminal (path time).1 →
        target path = (payoff (path time) : ℝ)) :
    ‖(∫ path, target path ∂Arena.pathLaw policy current supplied) -
        (policy.stoppedExpectedPayoffFrom current time payoff : ℝ)‖ ≤
      ((bound * Arena.unfinishedMass policy current time : ℚ≥0) : ℝ) := by
  let pathMeasure := Arena.pathLaw policy current supplied
  let unfinished := Arena.unfinishedAt (A := A) (start := start) time
  let stopped : (ℕ → A.HistoryFrom start) → ℝ :=
    fun path =>
      if A.IsTerminal (path time).1 then (payoff (path time) : ℝ) else 0
  letI : IsProbabilityMeasure pathMeasure := by
    dsimp only [pathMeasure, Arena.pathLaw]
    infer_instance
  letI : IsFiniteMeasure pathMeasure := inferInstance
  have hunfinished : MeasurableSet unfinished :=
    Arena.unfinishedAt_measurableSet (A := A) (start := start) time
  have hstoppedMeasurable' : Measurable stopped := by
    exact hstoppedMeasurable.comp (measurable_pi_apply time)
  have hstoppedBound (path : ℕ → A.HistoryFrom start) :
      ‖stopped path‖ ≤ (bound : ℝ) := by
    by_cases hterminal : A.IsTerminal (path time).1
    · have hbound := htargetBound path
      rw [htargetTerminal path hterminal] at hbound
      simpa only [stopped, if_pos hterminal] using hbound
    · simp [stopped, hterminal]
      positivity
  have hstoppedIntegrable : Integrable stopped pathMeasure := by
    apply (integrable_const (bound : ℝ)).mono
      hstoppedMeasurable'.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun path => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (bound : ℝ) by positivity)] using
        hstoppedBound path
  have hindicatorIntegrable :
      Integrable
        (unfinished.indicator fun _ => (bound : ℝ))
        pathMeasure :=
    (integrable_const (bound : ℝ)).indicator hunfinished
  have hpointwise (path : ℕ → A.HistoryFrom start) :
      ‖target path - stopped path‖ ≤
        unfinished.indicator (fun _ => (bound : ℝ)) path := by
    by_cases hterminal : A.IsTerminal (path time).1
    · have htarget := htargetTerminal path hterminal
      simp [unfinished, Arena.unfinishedAt, stopped, hterminal, htarget]
    · have hbound := htargetBound path
      simpa [unfinished, Arena.unfinishedAt, stopped, hterminal] using hbound
  rw [← policy.integral_pathLaw_stoppedCoordinate_eq_stoppedExpectedPayoffFrom
    current supplied finiteMarginal time payoff hstoppedMeasurable]
  rw [← integral_sub htargetIntegrable hstoppedIntegrable]
  calc
    ‖∫ path, target path - stopped path ∂pathMeasure‖ ≤
        ∫ path,
          unfinished.indicator (fun _ => (bound : ℝ)) path
          ∂pathMeasure :=
      norm_integral_le_of_norm_le hindicatorIntegrable
        (Filter.Eventually.of_forall hpointwise)
    _ = pathMeasure.real unfinished * (bound : ℝ) := by
      rw [integral_indicator hunfinished, setIntegral_const]
      simp [smul_eq_mul]
    _ = ((bound * Arena.unfinishedMass policy current time : ℚ≥0) : ℝ) := by
      change (pathMeasure unfinished).toReal * (bound : ℝ) = _
      rw [show pathMeasure unfinished =
          (Arena.unfinishedMass policy current time : ENNReal) by
        exact policy.pathLaw_unfinishedAt_eq_unfinishedMass
          current supplied finiteMarginal time]
      change
        (Arena.unfinishedMass policy current time : ℝ) * (bound : ℝ) = _
      rw [mul_comm]
      norm_cast

end Arena.StochasticHistoryPolicy

namespace KernelArena.StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- An executable rational state-prefix expectation is exactly the integral
of the corresponding observable under the analytic partial trajectory. -/
theorem integral_partialTraj_eq_expectedPrefixValueFrom
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (value : A.StatePrefix (start + steps) → ℚ) :
    (∫ history,
        (value (StatePrefix.ofAnalytic history) : ℝ)
        ∂Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic) =
      (policy.expectedPrefixValueFrom
        start initialPrefix steps value : ℝ) := by
  letI := kernelArenaStateMeasurableSingletonClass A
  letI : MeasurableSingletonClass
      ((index : Finset.Iic (start + steps)) → A.toMeasurable.State) :=
    piMeasurableSingletonClass
  rw [← policy.measure_prefixLawFrom_eq_partialTraj
    analytic realizes start initialPrefix steps]
  let law := policy.prefixLawFrom start initialPrefix steps
  calc
    (∫ history,
        (value (StatePrefix.ofAnalytic history) : ℝ)
        ∂μ[(law.map fun history => history.toAnalytic).atoms]) =
        ((law.map fun history => history.toAnalytic).expectRat
          (fun history => value (StatePrefix.ofAnalytic history)) : ℝ) :=
      FiniteLaw.integral_measure_eq_expectRat _ _
    _ = (law.expectRat value : ℝ) := by
      have hq :
          (law.map fun history => history.toAnalytic).expectRat
              (fun history => value (StatePrefix.ofAnalytic history)) =
            law.expectRat value := by
        simpa only [Function.comp_apply,
          StatePrefix.ofAnalytic_toAnalytic] using
          FiniteLaw.expectRat_map
          (fun history => history.toAnalytic) law
          (fun history => value (StatePrefix.ofAnalytic history))
      exact congrArg (fun rational : ℚ => (rational : ℝ)) hq
    _ = (policy.expectedPrefixValueFrom
          start initialPrefix steps value : ℝ) := rfl

/-- The state-prefix stopped-value computation is the integral of the same
terminal test and payoff under the analytic partial trajectory. -/
theorem integral_partialTraj_stopped_eq_stoppedExpectedValueFrom
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (payoff : A.StatePrefix (start + steps) → ℚ) :
    (∫ history,
        (if IsEmpty (A.Action (StatePrefix.ofAnalytic history).latest) then
          (payoff (StatePrefix.ofAnalytic history) : ℝ)
        else 0)
        ∂Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic) =
      (policy.stoppedExpectedValueFrom
        start initialPrefix steps payoff : ℝ) := by
  simpa only [stoppedExpectedValueFrom, apply_ite Rat.cast, Rat.cast_zero]
    using policy.integral_partialTraj_eq_expectedPrefixValueFrom
      analytic realizes start initialPrefix steps
      (fun history =>
        if IsEmpty (A.Action history.latest) then payoff history else 0)

end KernelArena.StateHistoryPolicy

namespace KernelArena.EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- An executable rational action-recording prefix expectation is exactly the
integral under the matching analytic event partial trajectory. -/
theorem integral_partialTraj_eq_expectedPrefixValueFrom
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (value : A.EventPrefix (start + steps) → ℚ) :
    (∫ history,
        (value (EventPrefix.ofAnalytic history) : ℝ)
        ∂Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic) =
      (policy.expectedPrefixValueFrom
        start initialPrefix steps value : ℝ) := by
  letI := kernelArenaPathEventMeasurableSingletonClass A
  letI : MeasurableSingletonClass
      ((index : Finset.Iic (start + steps)) →
        MeasurableKernelArena.EventAt A.toMeasurable index) :=
    piMeasurableSingletonClass
  rw [← policy.measure_prefixLawFrom_eq_partialTraj
    analytic realizes start initialPrefix steps]
  let law := policy.prefixLawFrom start initialPrefix steps
  calc
    (∫ history,
        (value (EventPrefix.ofAnalytic history) : ℝ)
        ∂μ[(law.map fun history => history.toAnalytic).atoms]) =
        ((law.map fun history => history.toAnalytic).expectRat
          (fun history => value (EventPrefix.ofAnalytic history)) : ℝ) :=
      FiniteLaw.integral_measure_eq_expectRat _ _
    _ = (law.expectRat value : ℝ) := by
      have hq :
          (law.map fun history => history.toAnalytic).expectRat
              (fun history => value (EventPrefix.ofAnalytic history)) =
            law.expectRat value := by
        simpa only [Function.comp_apply,
          EventPrefix.ofAnalytic_toAnalytic] using
          FiniteLaw.expectRat_map
          (fun history => history.toAnalytic) law
          (fun history => value (EventPrefix.ofAnalytic history))
      exact congrArg (fun rational : ℚ => (rational : ℝ)) hq
    _ = (policy.expectedPrefixValueFrom
          start initialPrefix steps value : ℝ) := rfl

/-- The event-prefix stopped-value computation is the integral of the same
terminal test and route-dependent payoff under the analytic partial
trajectory. -/
theorem integral_partialTraj_stopped_eq_stoppedExpectedValueFrom
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (payoff : A.EventPrefix (start + steps) → ℚ) :
    (∫ history,
        (if IsEmpty
            (A.Action (EventPrefix.ofAnalytic history).latestState) then
          (payoff (EventPrefix.ofAnalytic history) : ℝ)
        else 0)
        ∂Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) initialPrefix.toAnalytic) =
      (policy.stoppedExpectedValueFrom
        start initialPrefix steps payoff : ℝ) := by
  simpa only [stoppedExpectedValueFrom, apply_ite Rat.cast, Rat.cast_zero]
    using policy.integral_partialTraj_eq_expectedPrefixValueFrom
      analytic realizes start initialPrefix steps
      (fun history =>
        if IsEmpty (A.Action history.latestState) then payoff history else 0)

end KernelArena.EventHistoryPolicy
