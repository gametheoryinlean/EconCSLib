/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath
import EconCSLib.Math.Probability.PMF.ToMeasure
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# A genuinely continuous stochastic-arena boundary

This regression prevents `MeasurableKernelArena` from becoming a cosmetic
wrapper around the existing discrete `PMF` layer.

The example has unit-interval states, one action at every state, and the
non-atomic uniform volume law as its successor distribution.  The reverse
theorem proves that no `PMF` on the same state space has this measure, because
every `PMF` is concentrated on a countable support while unit-interval volume
assigns every countable set measure zero.

Its unique-action measurable policy also produces the same uniform law through
the terminal-aware analytic step kernel.  A second reverse theorem therefore
checks the execution layer, rather than only the raw transition layer.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace EconCSLib.Examples.ExtensiveGame.ContinuousKernelBoundary

/-- The legal-action bundle carries exactly the sigma algebra pulled back from
its current-state projection. -/
@[reducible]
def actionBundleMeasurable :
    MeasurableSpace (Σ _state : Set.Icc (0 : ℝ) 1, Unit) :=
  (inferInstance : MeasurableSpace (Set.Icc (0 : ℝ) 1)).comap Sigma.fst

/-- Explicit analytic input for the non-atomic regression.

Both kernels are supplied mathematical objects. The certificates fix their
laws exactly; neither uniform sampling nor Dirac-measure construction is
claimed to be an executable operation. -/
class AnalyticInput where
  /-- Uniform successor law, supplied as a measurable kernel. -/
  transition : @Kernel (Σ _state : Set.Icc (0 : ℝ) 1, Unit)
    (Set.Icc (0 : ℝ) 1) actionBundleMeasurable inferInstance
  /-- Every transition is unit-interval volume. -/
  transition_eq : ∀ stateAction, transition stateAction = volume
  /-- The unique-action law, supplied as a measurable kernel. -/
  action : @Kernel (Set.Icc (0 : ℝ) 1)
    (Σ _state : Set.Icc (0 : ℝ) 1, Unit) inferInstance actionBundleMeasurable
  /-- The supplied action kernel selects precisely the legal unique action. -/
  action_eq : ∀ state, action state =
    @Measure.dirac (Σ _state : Set.Icc (0 : ℝ) 1, Unit)
      actionBundleMeasurable ⟨state, ()⟩

variable [inputs : AnalyticInput]

/-- A one-action arena whose next state is uniformly distributed on the unit
interval, independently of the current state. -/
def continuousArena : MeasurableKernelArena where
  State := Set.Icc (0 : ℝ) 1
  Action := fun _ => Unit
  stateMeasurable := inferInstance
  actionBundleMeasurable := actionBundleMeasurable
  stateProjection_measurable := comap_measurable Sigma.fst
  transition := inputs.transition
  transition_isMarkov := by
    constructor
    intro stateAction
    rw [inputs.transition_eq]
    infer_instance

@[simp]
theorem continuousArena_nextMeasure
    (state : continuousArena.State)
    (action : continuousArena.Action state) :
    continuousArena.nextMeasure state action =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) :=
  inputs.transition_eq ⟨state, action⟩

/-- Selecting the arena's unique action is measurable for the pullback sigma
algebra on the dependent action bundle. -/
theorem measurable_uniqueAction :
    @Measurable
      continuousArena.State continuousArena.ActionBundle
      continuousArena.stateMeasurable
      continuousArena.actionBundleMeasurable
      (fun state => (⟨state, Unit.unit⟩ :
        continuousArena.ActionBundle)) := by
  change
    @Measurable
      (Set.Icc (0 : ℝ) 1)
      (Σ _state : Set.Icc (0 : ℝ) 1, Unit)
      inferInstance actionBundleMeasurable
      (fun state => (⟨state, Unit.unit⟩ :
        Σ _state : Set.Icc (0 : ℝ) 1, Unit))
  rw [measurable_comap_iff]
  exact measurable_id

/-- The unique-action analytic policy.  There are no terminal states, so its
action kernel is a Dirac probability law at every state. -/
def continuousPolicy :
    continuousArena.ActionPolicy where
  kernel := inputs.action
  terminal_zero := by
    intro state hterminal
    exact (hterminal.false Unit.unit).elim
  nonterminal_isProbability := by
    intro state _
    change @IsProbabilityMeasure (Σ _state : Set.Icc (0 : ℝ) 1, Unit)
      actionBundleMeasurable (inputs.action state)
    rw [inputs.action_eq state]
    infer_instance
  legal := by
    intro state _
    letI : MeasurableSpace (Σ _state : Set.Icc (0 : ℝ) 1, Unit) :=
      actionBundleMeasurable
    change ∀ᵐ stateAction ∂inputs.action state, stateAction.1 = state
    rw [inputs.action_eq state]
    have hfiber :
        @MeasurableSet continuousArena.ActionBundle
          continuousArena.actionBundleMeasurable
          (continuousArena.actionFiber state) := by
      change
        @MeasurableSet
          (Σ _state : Set.Icc (0 : ℝ) 1, Unit)
          actionBundleMeasurable
          {stateAction | stateAction.1 = state}
      exact
        ⟨({state} : Set (Set.Icc (0 : ℝ) 1)),
          @measurableSet_singleton
            (Set.Icc (0 : ℝ) 1) inferInstance inferInstance state,
          rfl⟩
    apply (ae_dirac_iff hfiber).2
    simp

/-- The continuous example has no terminal states, and its empty terminal set
is measurable. -/
theorem continuousArena_measurableSet_terminalSet :
    MeasurableSet continuousArena.terminalSet := by
  have hempty : continuousArena.terminalSet = ∅ := by
    ext state
    constructor
    · intro hstate
      exact (hstate.false Unit.unit).elim
    · intro hstate
      simp at hstate
  rw [hempty]
  exact MeasurableSet.empty

/-- Policy-controlled one-step execution remains the non-atomic uniform
successor law. -/
@[simp]
theorem continuousPolicy_stepKernel
    (state : continuousArena.State) :
    continuousPolicy.stepKernel
        continuousArena_measurableSet_terminalSet state =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  rw [MeasurableKernelArena.ActionPolicy.stepKernel_apply_nonterminal]
  · change (inputs.action state).bind continuousArena.transition = _
    rw [inputs.action_eq state]
    change
      (Measure.dirac
        (⟨state, Unit.unit⟩ : continuousArena.ActionBundle)).bind
          continuousArena.transition =
        (volume : Measure (Set.Icc (0 : ℝ) 1))
    rw [Measure.dirac_bind continuousArena.transition.measurable]
    exact inputs.transition_eq _
  · intro hterminal
    exact hterminal.false Unit.unit

/-- Every positive-horizon endpoint kernel of the continuous example is the
constant volume kernel. -/
theorem continuousPolicy_endpointKernel_succ
    [MeasurableKernelArena.ActionPolicy.EndpointExecution continuousPolicy
      continuousArena_measurableSet_terminalSet] (horizon : ℕ) :
    continuousPolicy.endpointKernel
        continuousArena_measurableSet_terminalSet horizon.succ =
      Kernel.const continuousArena.State
        (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  induction horizon with
  | zero =>
      rw [MeasurableKernelArena.ActionPolicy.endpointKernel_succ]
      rw [MeasurableKernelArena.ActionPolicy.endpointKernel_zero]
      rw [Kernel.id_comp]
      apply Kernel.ext
      intro state
      exact continuousPolicy_stepKernel state
  | succ horizon ih =>
      rw [MeasurableKernelArena.ActionPolicy.endpointKernel_succ]
      rw [ih]
      exact Kernel.const_comp' _ _

/-- Every positive finite endpoint law remains unit-interval volume. -/
@[simp]
theorem continuousPolicy_endpointMeasure_succ
    [MeasurableKernelArena.ActionPolicy.EndpointExecution continuousPolicy
      continuousArena_measurableSet_terminalSet]
    (horizon : ℕ) (state : continuousArena.State) :
    continuousPolicy.endpointMeasure
        continuousArena_measurableSet_terminalSet
        horizon.succ state =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  change
    continuousPolicy.endpointKernel
        continuousArena_measurableSet_terminalSet
        horizon.succ state =
      (volume : Measure (Set.Icc (0 : ℝ) 1))
  rw [continuousPolicy_endpointKernel_succ]
  rfl

omit inputs in
/-- The continuous transition law is not the measure associated to any
discrete probability mass function on the unit interval. -/
theorem no_discretePMF_representation :
    ¬ ∃ p : PMF (Set.Icc (0 : ℝ) 1),
      p.toMeasure = (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  rintro ⟨p, hp⟩
  have hsupportOne :
      p.toMeasure p.support = 1 :=
    (p.toMeasure_apply_eq_one_iff
      p.support_countable.measurableSet).mpr Set.Subset.rfl
  have hsupportZero :
      (volume : Measure (Set.Icc (0 : ℝ) 1)) p.support = 0 :=
    p.support_countable.measure_zero volume
  rw [hp, hsupportZero] at hsupportOne
  exact zero_ne_one hsupportOne

/-- The analytic execution step cannot be represented by any discrete PMF,
even though the policy itself is deterministic. -/
theorem no_discretePMF_stepKernel_representation
    (state : continuousArena.State) :
    ¬ ∃ p : PMF (Set.Icc (0 : ℝ) 1),
      p.toMeasure =
        continuousPolicy.stepKernel
          continuousArena_measurableSet_terminalSet state := by
  simpa only [continuousPolicy_stepKernel] using
    no_discretePMF_representation

/-- No positive finite endpoint law of the continuous example comes from a
discrete PMF. -/
theorem no_discretePMF_endpointMeasure_representation
    [MeasurableKernelArena.ActionPolicy.EndpointExecution continuousPolicy
      continuousArena_measurableSet_terminalSet]
    (horizon : ℕ) (state : continuousArena.State) :
    ¬ ∃ p : PMF (Set.Icc (0 : ℝ) 1),
      p.toMeasure =
        continuousPolicy.endpointMeasure
          continuousArena_measurableSet_terminalSet
          horizon.succ state := by
  simpa only [continuousPolicy_endpointMeasure_succ] using
    no_discretePMF_representation

/-- Every positive-time path coordinate has the non-atomic volume law. -/
@[simp]
theorem continuousPolicy_coordinateMeasure_succ
    [MeasurableKernelArena.ActionPolicy.PathExecution continuousPolicy
      continuousArena_measurableSet_terminalSet]
    (time : ℕ) (state : continuousArena.State) :
    continuousPolicy.coordinateMeasure
        continuousArena_measurableSet_terminalSet
        state time.succ =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨execution⟩ :=
    MeasurableKernelArena.ActionPolicy.EndpointExecution.nonempty
      continuousPolicy continuousArena_measurableSet_terminalSet
  letI := execution
  rw [MeasurableKernelArena.ActionPolicy.coordinateMeasure_eq_endpointMeasure]
  exact continuousPolicy_endpointMeasure_succ time state

/-- The entire continuous state-path law is not the measure associated to any
discrete PMF on path space. -/
theorem no_discretePMF_pathMeasure_representation
    [MeasurableKernelArena.ActionPolicy.PathExecution continuousPolicy
      continuousArena_measurableSet_terminalSet]
    (state : continuousArena.State) :
    ¬ ∃ p : PMF (ℕ → Set.Icc (0 : ℝ) 1),
      p.toMeasure =
        continuousPolicy.pathMeasure
          continuousArena_measurableSet_terminalSet state := by
  rintro ⟨p, hp⟩
  apply no_discretePMF_representation
  refine ⟨p.map (fun path => path 1), ?_⟩
  have hcoordinate :
      (p.map (fun path => path 1)).toMeasure =
        continuousPolicy.coordinateMeasure
          continuousArena_measurableSet_terminalSet state 1 := by
    calc
      (p.map (fun path => path 1)).toMeasure =
          p.toMeasure.map (fun path => path 1) := by
        symm
        exact PMF.toMeasure_map (fun path => path 1) p
          (@measurable_pi_apply
            ℕ (fun _ => Set.Icc (0 : ℝ) 1)
            (fun _ => inferInstance) 1)
      _ =
          (continuousPolicy.pathMeasure
            continuousArena_measurableSet_terminalSet state).map
              (fun path => path 1) := by
        exact congrArg
          (fun measure : Measure (ℕ → Set.Icc (0 : ℝ) 1) =>
            measure.map (fun path => path 1))
          hp
      _ =
          continuousPolicy.coordinateMeasure
            continuousArena_measurableSet_terminalSet state 1 :=
        (MeasurableKernelArena.ActionPolicy.PathExecution.coordinate_eq state 1).symm
  exact hcoordinate.trans
    (continuousPolicy_coordinateMeasure_succ 0 state)

end EconCSLib.Examples.ExtensiveGame.ContinuousKernelBoundary
