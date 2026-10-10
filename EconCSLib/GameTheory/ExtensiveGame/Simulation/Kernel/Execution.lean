/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Kernel.Execution — terminal-aware measurable-kernel execution

One-step policy-controlled execution for `MeasurableKernelArena`.

A policy is a measurable kernel into the total dependent action bundle.  It
is a probability measure concentrated on the current state's legal-action
fiber at nonterminal states, and the zero measure at terminal states.  The
resulting state-step kernel absorbs terminal states with a Dirac law and
composes the policy kernel with the arena transition elsewhere.

## Main definitions

* `MeasurableKernelArena.ActionPolicy` — measurable legal action laws with
  explicit terminal behavior.
* `ActionPolicy.actionStepKernel` — action selection followed by transition.
* `ActionPolicy.stepKernel` — normalized terminal-absorbing execution.
* `KernelArena.Policy.toMeasurable` — exact embedding of discrete policies.

## Main results

* `ActionPolicy.stepKernel_isMarkov` — stopped execution is normalized.
* `ActionPolicy.ae_mem_actionFiber` — policy legality holds almost surely.
* `KernelArena.Policy.toMeasurable_stepKernel_apply_nonterminal` — the
  analytic step law exactly recovers the existing finite-law step law, with no
  countability assumption on the action carrier and no public decidability
  assumption on terminality.

This module deliberately stops at one-step execution.  Finite and infinite
analytic trajectory laws require a separate construction and audit. The
discrete embedding is noncomputable and performs its terminal split
classically; it is not an executable terminal classifier.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

/-- States with no legal action. -/
def terminalSet (A : MeasurableKernelArena) : Set A.State :=
  {state | IsEmpty (A.Action state)}

/-- Bundled legal actions based at a particular state. -/
def actionFiber (A : MeasurableKernelArena) (state : A.State) :
    Set A.ActionBundle :=
  {stateAction | stateAction.1 = state}

theorem measurableSet_actionFiber (A : MeasurableKernelArena)
    [MeasurableSingletonClass A.State] (state : A.State) :
    MeasurableSet (A.actionFiber state) := by
  exact A.stateProjection_measurable
    (measurableSet_singleton state)

/-- A terminal-aware measurable policy.

At terminal states its action measure is zero.  At nonterminal states it is a
probability measure concentrated on the dependent action fiber of the current
state. -/
structure ActionPolicy (A : MeasurableKernelArena) where
  /-- A measurable, possibly killed, kernel into bundled legal actions. -/
  kernel : Kernel A.State A.ActionBundle
  /-- No action mass is produced at terminal states. -/
  terminal_zero :
    ∀ state, IsEmpty (A.Action state) → kernel state = 0
  /-- Action mass is normalized at nonterminal states. -/
  nonterminal_isProbability :
    ∀ state, ¬ IsEmpty (A.Action state) →
      IsProbabilityMeasure (kernel state)
  /-- At nonterminal states, the selected bundled action is based at the
  current state almost surely.

  This is stated directly in the almost-everywhere filter.  The action fiber
  need not be measurable when state singletons are not measurable, so the
  numerically weaker outer-measure equation `kernel state fiber = 1` is not a
  sound legality certificate in the general analytic model. -/
  legal :
    ∀ state, ¬ IsEmpty (A.Action state) →
      ∀ᵐ stateAction ∂kernel state,
        stateAction ∈ A.actionFiber state

namespace ActionPolicy

variable {A : MeasurableKernelArena}

/-- The policy chooses a legal bundled action almost surely at each
nonterminal state. -/
theorem ae_mem_actionFiber (policy : A.ActionPolicy)
    (state : A.State) (hnonterminal : ¬ IsEmpty (A.Action state)) :
    ∀ᵐ stateAction ∂policy.kernel state,
      stateAction ∈ A.actionFiber state := by
  exact policy.legal state hnonterminal

/-- On state spaces with measurable singletons, genuine almost-sure legality
recovers the familiar measure-one action-fiber equation. -/
theorem legal_mass_one (policy : A.ActionPolicy)
    [MeasurableSingletonClass A.State]
    (state : A.State) (hnonterminal : ¬ IsEmpty (A.Action state)) :
    policy.kernel state (A.actionFiber state) = 1 := by
  letI : IsProbabilityMeasure (policy.kernel state) :=
    policy.nonterminal_isProbability state hnonterminal
  have hmeasure :=
    (ae_mem_iff_measure_eq
      (A.measurableSet_actionFiber state).nullMeasurableSet).mp
        (policy.ae_mem_actionFiber state hnonterminal)
  simpa using hmeasure

/-- Compose the policy's legal-action law with the arena transition. -/
noncomputable def actionStepKernel (policy : A.ActionPolicy) :
    Kernel A.State A.State :=
  A.transition ∘ₖ policy.kernel

/-- Terminal-absorbing one-step execution.

The measurable terminal-set proof is explicit because measurability of
dependent-action emptiness does not follow from the arena fields alone. -/
noncomputable def stepKernel (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    Kernel A.State A.State := by
  classical
  exact Kernel.piecewise hterminal Kernel.id policy.actionStepKernel

instance stepKernel_isMarkov (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    IsMarkovKernel (policy.stepKernel hterminal) := by
  classical
  constructor
  intro state
  rw [stepKernel, Kernel.piecewise_apply]
  split_ifs with hstate
  · infer_instance
  · have hnonterminal :
        ¬ IsEmpty (A.Action state) := by
      simpa only [terminalSet, Set.mem_setOf_eq] using hstate
    change
      IsProbabilityMeasure
        ((policy.kernel state).bind A.transition)
    letI : IsProbabilityMeasure (policy.kernel state) :=
      policy.nonterminal_isProbability state hnonterminal
    exact MeasureTheory.isProbabilityMeasure_bind
      A.transition.aemeasurable
      (Filter.Eventually.of_forall fun stateAction => inferInstance)

@[simp]
theorem stepKernel_apply_terminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.stepKernel hterminal state = Measure.dirac state := by
  classical
  rw [stepKernel, Kernel.piecewise_apply, if_pos]
  · exact Kernel.id_apply state
  · exact hstate

@[simp]
theorem stepKernel_apply_nonterminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.stepKernel hterminal state =
      (policy.kernel state).bind A.transition := by
  classical
  rw [stepKernel, Kernel.piecewise_apply, if_neg]
  · rfl
  · exact hstate

end ActionPolicy

end MeasurableKernelArena

namespace KernelArena

private theorem finiteLawMeasure_isProbability
    {X : Type*} [MeasurableSpace X] (law : FiniteLaw X) :
    IsProbabilityMeasure
      (law.atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0) := by
  constructor
  change
    (law.atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0) Set.univ = 1
  have hzero : ((0 : ℚ≥0) : ENNReal) = 0 := by
    change (((0 : ℚ≥0) : NNReal) : ENNReal) = 0
    simp
  have hadd (p q : ℚ≥0) :
      ((p + q : ℚ≥0) : ENNReal) =
        (p : ENNReal) + (q : ENNReal) := by
    change (((p + q : ℚ≥0) : NNReal) : ENNReal) =
      ((p : NNReal) : ENNReal) + ((q : NNReal) : ENNReal)
    simp
  have hsum :
      (law.atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0) Set.univ =
      ((FiniteLaw.totalWeight law.atoms : ℚ≥0) : ENNReal) := by
    induction law.atoms with
    | nil => simp [FiniteLaw.totalWeight, hzero]
    | cons atom atoms ih =>
        simp [FiniteLaw.totalWeight, ih, hadd]
  rw [hsum, FiniteLaw.totalWeight_atoms]
  change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
  norm_num

private theorem finiteLawMeasure_map_ae
    {X Y : Type*} [MeasurableSpace Y]
    (law : FiniteLaw X) (f : X → Y) (predicate : Y → Prop)
    (hmeasurable : MeasurableSet {y | predicate y})
    (holds : ∀ x, predicate (f x)) :
    ∀ᵐ y ∂(law.map f).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0,
      predicate y := by
  rw [FiniteLaw.map_atoms]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.map_cons, List.foldr_cons,
        MeasureTheory.ae_add_measure_iff]
      exact
        ⟨Measure.ae_smul_measure
            ((MeasureTheory.ae_dirac_iff hmeasurable).2
              (holds outcome)) _,
          ih⟩

private theorem finiteLawMeasure_append
    {X : Type*} [MeasurableSpace X]
    (left right : List (X × ℚ≥0)) :
    (left ++ right).foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0 =
      left.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0 +
        right.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0 := by
  induction left with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih, add_assoc]

private theorem finiteLawMeasure_map_mul
    {X : Type*} [MeasurableSpace X]
    (weight : ℚ≥0) (atoms : List (X × ℚ≥0)) :
    (atoms.map fun atom => (atom.1, weight * atom.2)).foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0 =
      (weight : ENNReal) •
        atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0 := by
  have hmul (p q : ℚ≥0) :
      ((p * q : ℚ≥0) : ENNReal) =
        (p : ENNReal) * (q : ENNReal) := by
    change (((p * q : ℚ≥0) : NNReal) : ENNReal) =
      ((p : NNReal) : ENNReal) * ((q : NNReal) : ENNReal)
    simp
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, innerWeight⟩
      simp only [List.map_cons, List.foldr_cons]
      rw [hmul, ih, smul_add, smul_smul]

private theorem measure_bind_add
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (left right : Measure X) (next : X → Measure Y)
    (hmeasurable : Measurable next) :
    (left + right).bind next =
      left.bind next + right.bind next := by
  ext event hevent
  simp [Measure.bind_apply, hevent, hmeasurable.aemeasurable,
    MeasureTheory.lintegral_add_measure]

private theorem finiteLawMeasure_flatMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (atoms : List (X × ℚ≥0)) (next : X → FiniteLaw Y)
    (hmeasurable : Measurable fun x =>
      (next x).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0) :
    (atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0).bind
        (fun x =>
          (next x).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
            0) =
      (atoms.flatMap fun atom =>
          (next atom.1).atoms.map fun target =>
            (target.1, atom.2 * target.2)).foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0 := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.foldr_cons, List.flatMap_cons]
      rw [measure_bind_add _ _ _ hmeasurable,
        Measure.bind_smul, Measure.dirac_bind hmeasurable,
        ih, finiteLawMeasure_append,
        finiteLawMeasure_map_mul]

/-- The killed analytic action kernel induced by a discrete policy. -/
noncomputable def Policy.toMeasurableKernel {A : KernelArena}
    (policy : A.Policy) :
    @Kernel A.State (Σ state, A.Action state) ⊤ ⊤ := by
  classical
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  exact
      { toFun := fun state =>
          (if hterminal : IsEmpty (A.Action state) then
            0
          else
            (FiniteLaw.map
                (fun action =>
                  (⟨state, action⟩ : Σ state, A.Action state))
                (policy state hterminal)).atoms.foldr
              (fun atom rest =>
                (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
              0)
        measurable' := by
          exact fun _ _ => MeasurableSpace.measurableSet_top }

@[simp]
theorem Policy.toMeasurableKernel_apply_terminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.toMeasurableKernel state = 0 := by
  classical
  simp [Policy.toMeasurableKernel, hstate]

@[simp]
theorem Policy.toMeasurableKernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurableKernel state =
      (FiniteLaw.map
          (fun action =>
            (⟨state, action⟩ : Σ state, A.Action state))
          (policy state hstate)).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
        0 := by
  classical
  simp [Policy.toMeasurableKernel, hstate]

private theorem Policy.toMeasurableKernel_isProbability
    {A : KernelArena} (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    IsProbabilityMeasure (policy.toMeasurableKernel state) := by
  classical
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  change IsProbabilityMeasure
    (if hterminal : IsEmpty (A.Action state) then
      0
    else
      (FiniteLaw.map
          (fun action =>
            (⟨state, action⟩ : Σ state, A.Action state))
          (policy state hterminal)).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0)
  rw [dif_neg hstate]
  exact finiteLawMeasure_isProbability _

private theorem Policy.toMeasurableKernel_legal
    {A : KernelArena} (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    ∀ᵐ stateAction ∂policy.toMeasurableKernel state,
      stateAction.1 = state := by
  classical
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  rw [Policy.toMeasurableKernel_apply_nonterminal
    policy state hstate]
  exact finiteLawMeasure_map_ae
    (policy state hstate)
    (fun action =>
      (⟨state, action⟩ : Σ state, A.Action state))
    (fun stateAction => stateAction.1 = state)
    MeasurableSpace.measurableSet_top
    (fun _ => rfl)

/-- Embed a discrete terminal-aware policy as an analytic action policy. -/
noncomputable def Policy.toMeasurable {A : KernelArena}
    (policy : A.Policy) :
    A.toMeasurable.ActionPolicy := by
  classical
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  exact
    { kernel := policy.toMeasurableKernel
      terminal_zero := by
        intro state hterminal
        exact policy.toMeasurableKernel_apply_terminal state hterminal
      nonterminal_isProbability := by
        intro state hnonterminal
        change A.State at state
        change ¬ IsEmpty (A.Action state) at hnonterminal
        exact policy.toMeasurableKernel_isProbability state hnonterminal
      legal := by
        intro state hnonterminal
        change A.State at state
        change ¬ IsEmpty (A.Action state) at hnonterminal
        exact policy.toMeasurableKernel_legal state hnonterminal }

/-- Terminal states form a measurable set after the discrete embedding. -/
theorem toMeasurable_measurableSet_terminalSet (A : KernelArena) :
    MeasurableSet A.toMeasurable.terminalSet :=
  MeasurableSpace.measurableSet_top

@[simp]
theorem Policy.toMeasurable_kernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurable.kernel state =
      (FiniteLaw.map
          (fun action =>
            (⟨state, action⟩ : Σ state, A.Action state))
          (policy state hstate)).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
        0 := by
  exact policy.toMeasurableKernel_apply_nonterminal state hstate

/-- Analytic one-step execution recovers the finite-law step law exactly at
nonterminal states, without assuming a countable action carrier. -/
theorem Policy.toMeasurable_stepKernel_apply_nonterminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : ¬ IsEmpty (A.Action state)) :
    policy.toMeasurable.stepKernel
        A.toMeasurable_measurableSet_terminalSet state =
      (A.stepLaw policy state hstate).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
        0 := by
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  rw [MeasurableKernelArena.ActionPolicy.stepKernel_apply_nonterminal
    _ _ _ hstate]
  rw [Policy.toMeasurable_kernel_apply_nonterminal policy state hstate]
  change
    ((FiniteLaw.map
        (fun action =>
          (⟨state, action⟩ : Σ state, A.Action state))
        (policy state hstate)).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0).bind
      (fun stateAction =>
        (A.next stateAction.1 stateAction.2).atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0) =
    (A.stepLaw policy state hstate).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0
  have htransition :
      Measurable fun stateAction : Σ state, A.Action state =>
        (A.next stateAction.1 stateAction.2).atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0 :=
    A.toMeasurable.transition.measurable
  rw [finiteLawMeasure_flatMap _ _ htransition]
  change
    ((FiniteLaw.map
        (fun action =>
          (⟨state, action⟩ : Σ state, A.Action state))
        (policy state hstate)).bind
      (fun stateAction =>
        A.next stateAction.1 stateAction.2)).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0 =
    (A.stepLaw policy state hstate).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0
  rw [FiniteLaw.bind_map]
  rfl

/-- The embedded analytic execution absorbs a discrete terminal state with
exactly the same Dirac law used by the stopped finite-law execution. -/
theorem Policy.toMeasurable_stepKernel_apply_terminal
    {A : KernelArena}
    (policy : A.Policy)
    (state : A.State) (hstate : IsEmpty (A.Action state)) :
    policy.toMeasurable.stepKernel
        A.toMeasurable_measurableSet_terminalSet state =
      @Measure.dirac A.State ⊤ state :=
  MeasurableKernelArena.ActionPolicy.stepKernel_apply_terminal
    _ _ _ hstate

end KernelArena
