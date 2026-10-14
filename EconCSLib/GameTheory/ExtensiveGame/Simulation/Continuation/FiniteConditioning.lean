/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ConditionalContinuation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path

/-!
# Analytic semantics of exact finite conditional continuation

`Execution.Discrete.ConditionalContinuation` computes a finite posterior and
continues every retained complete event prefix with an exact `FiniteLaw`.
This module proves that interpreting the resulting law as a finite sum of
Dirac measures gives the existing measurable-kernel continuation semantics.
It is the conditioning branch of the semantic compatibility layer and owns no
numerical result definition.

The bridge is deliberately finite-windowed.  It first identifies continuation
of an arbitrary exact posterior with measure bind against Mathlib's
`Kernel.partialTraj`.  It then identifies the same measure with the requested
finite-prefix marginal of `absolutePathMeasureFromPrefix`.  The conditional
version uses a successful `conditionOnFiber` result and therefore inherits the
executable API's explicit `none` result at zero-mass observations.

No regular conditional distribution is selected here.  At a positive prefix
atom, `Continuation.Conditioning` already identifies its conditional tail
kernel with constructive absolute-prefix continuation.  At a null prefix that
kernel is determined only almost everywhere, so it cannot replace the exact
finite posterior used below.

## Main results

* `measure_posteriorContinuation_eq_bind_partialTraj`;
* `measure_posteriorContinuation_eq_bind_absolutePathMarginal`;
* `measure_conditionalPrefixLawFrom_eq_bind_partialTraj`;
* `measure_conditionalPrefixLawFrom_eq_bind_absolutePathMarginal`.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena.EventHistoryPolicy

universe uS uA uO

variable {A : KernelArena}

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

/-- Continuing every atom of an exact posterior and then interpreting the
result as a measure is measure bind against the analytic partial trajectory.
The source prefix space is given its discrete measurable structure locally;
the analytic target retains the measurable structure of `A.toMeasurable`. -/
theorem measure_posteriorContinuation_eq_bind_partialTraj
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (posterior : FiniteLaw (A.EventPrefix start))
    (steps : ℕ) :
    μ[((posterior.bind fun history =>
          policy.prefixLawFrom start history steps).map fun history =>
        history.toAnalytic).atoms] =
      Measure.bind
        μ[(posterior.map fun history => history.toAnalytic).atoms]
        (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps)) := by
  let next : A.toMeasurable.ContinuationPrefix start →
      FiniteLaw (A.toMeasurable.ContinuationPrefix (start + steps)) :=
    fun history =>
      (policy.prefixLawFrom start (EventPrefix.ofAnalytic history) steps).map fun result =>
        result.toAnalytic
  have hfinite :
      (posterior.bind fun history =>
          policy.prefixLawFrom start history steps).map
            (fun history => history.toAnalytic) =
        (posterior.map fun history => history.toAnalytic).bind next := by
    rw [FiniteLaw.map_bind, FiniteLaw.bind_map]
    congr
  have hnext (history : A.toMeasurable.ContinuationPrefix start) :
      μ[(next history).atoms] =
        Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps) history := by
    simpa only [next, EventPrefix.toAnalytic_ofAnalytic] using
      policy.measure_prefixLawFrom_eq_partialTraj
        analytic realizes start (EventPrefix.ofAnalytic history) steps
  have hnextFunction :
      (fun history : A.toMeasurable.ContinuationPrefix start =>
        μ[(next history).atoms]) =
        Kernel.partialTraj
            (analytic.pathStepKernel
              A.toMeasurable_measurableSet_terminalSet)
            start (start + steps) := by
    funext history
    exact hnext history
  have hnextMeasurable :
      Measurable fun history : A.toMeasurable.ContinuationPrefix start =>
        μ[(next history).atoms] := by
    rw [hnextFunction]
    exact Kernel.measurable _
  rw [hfinite]
  calc
    μ[((posterior.map fun history => history.toAnalytic).bind next).atoms] =
        Measure.bind
          μ[(posterior.map fun history => history.toAnalytic).atoms]
          (fun history => μ[(next history).atoms]) :=
      (FiniteLaw.measure_bind
        (posterior.map fun history => history.toAnalytic)
        next hnextMeasurable).symm
    _ = Measure.bind
          μ[(posterior.map fun history => history.toAnalytic).atoms]
          (Kernel.partialTraj
            (analytic.pathStepKernel
              A.toMeasurable_measurableSet_terminalSet)
            start (start + steps)) := by
      rw [hnextFunction]

/-- The same posterior continuation measure is the mixture of the requested
finite-prefix marginals of constructive absolute-path continuations. -/
theorem measure_posteriorContinuation_eq_bind_absolutePathMarginal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (posterior : FiniteLaw (A.EventPrefix start))
    (steps : ℕ) :
    μ[((posterior.bind fun history =>
          policy.prefixLawFrom start history steps).map fun history =>
        history.toAnalytic).atoms] =
      Measure.bind
        μ[(posterior.map fun history => history.toAnalytic).atoms]
        (fun history =>
        (analytic.absolutePathMeasureFromPrefix
          A.toMeasurable_measurableSet_terminalSet start
          history).map
            (Preorder.frestrictLe (start + steps))) := by
  rw [policy.measure_posteriorContinuation_eq_bind_partialTraj
    analytic realizes start posterior steps]
  congr 1
  funext history
  rw [MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix]
  symm
  exact
    @Kernel.traj_map_frestrictLe_apply
      (MeasurableKernelArena.EventAt A.toMeasurable)
      (fun _ => inferInstance)
      (analytic.pathStepKernel
        A.toMeasurable_measurableSet_terminalSet)
      (fun _ => inferInstance)
      start (start + steps) history

/-- A successful exact conditioning result, followed by finite continuation,
has the analytic semantics obtained by binding its posterior atoms against
the corresponding partial trajectories. -/
theorem measure_conditionalPrefixLawFrom_eq_bind_partialTraj
    {Observation : Type uO} [DecidableEq Observation]
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (prior : FiniteLaw (A.EventPrefix start))
    (observe : A.EventPrefix start → Observation)
    (observed : Observation) (steps : ℕ)
    (posterior : FiniteLaw (A.EventPrefix start))
    (result : FiniteLaw (A.EventPrefix (start + steps)))
    (hposterior :
      prior.conditionOnFiber observe observed = some posterior)
    (hresult :
      policy.conditionalPrefixLawFrom start prior observe observed steps =
        some result) :
    μ[(result.map fun history => history.toAnalytic).atoms] =
      Measure.bind
        μ[(posterior.map fun history => history.toAnalytic).atoms]
        (Kernel.partialTraj
          (analytic.pathStepKernel
            A.toMeasurable_measurableSet_terminalSet)
          start (start + steps)) := by
  have hresult' := hresult
  change
    (prior.conditionOnFiber observe observed).map
        (fun posterior => posterior.bind fun history =>
          policy.prefixLawFrom start history steps) =
      some result at hresult'
  rw [hposterior] at hresult'
  simp only [Option.map_some] at hresult'
  have hresultEq :
      posterior.bind (fun history =>
        policy.prefixLawFrom start history steps) = result :=
    Option.some.inj hresult'
  rw [← hresultEq]
  exact policy.measure_posteriorContinuation_eq_bind_partialTraj
    analytic realizes start posterior steps

/-- A successful exact conditional continuation is also the mixture of the
finite-prefix marginals of constructive absolute-path continuations. -/
theorem measure_conditionalPrefixLawFrom_eq_bind_absolutePathMarginal
    {Observation : Type uO} [DecidableEq Observation]
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy)
    (analytic : A.toMeasurable.EventHistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (start : ℕ) (prior : FiniteLaw (A.EventPrefix start))
    (observe : A.EventPrefix start → Observation)
    (observed : Observation) (steps : ℕ)
    (posterior : FiniteLaw (A.EventPrefix start))
    (result : FiniteLaw (A.EventPrefix (start + steps)))
    (hposterior :
      prior.conditionOnFiber observe observed = some posterior)
    (hresult :
      policy.conditionalPrefixLawFrom start prior observe observed steps =
        some result) :
    μ[(result.map fun history => history.toAnalytic).atoms] =
      Measure.bind
        μ[(posterior.map fun history => history.toAnalytic).atoms]
        (fun history =>
        (analytic.absolutePathMeasureFromPrefix
          A.toMeasurable_measurableSet_terminalSet start
          history).map
            (Preorder.frestrictLe (start + steps))) := by
  rw [policy.measure_conditionalPrefixLawFrom_eq_bind_partialTraj
    analytic realizes start prior observe observed steps posterior result
    hposterior hresult]
  congr 1
  funext history
  rw [MeasurableKernelArena.EventHistoryActionPolicy.absolutePathMeasureFromPrefix]
  symm
  exact
    @Kernel.traj_map_frestrictLe_apply
      (MeasurableKernelArena.EventAt A.toMeasurable)
      (fun _ => inferInstance)
      (analytic.pathStepKernel
        A.toMeasurable_measurableSet_terminalSet)
      (fun _ => inferInstance)
      start (start + steps) history

end KernelArena.EventHistoryPolicy
