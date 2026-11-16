/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution

/-!
# Kernel.Endpoint — finite-horizon measurable endpoint laws

Supplied finite-horizon kernels certified to iterate the terminal-absorbing
state-step kernel from `Kernel.Execution`.

The declarations here describe only the state law at a selected finite
horizon.  They do not construct a joint law of the intermediate states and are
therefore deliberately named endpoint kernels and measures, not trajectories.

## Main definitions

* `ActionPolicy.EndpointExecution` — supplied kernels with exact zero and
  successor equations; analytic existence is a `Nonempty` theorem.
* `ActionPolicy.endpointKernel` — the stopped state kernel after a finite
  number of steps.
* `ActionPolicy.endpointMeasure` — that kernel evaluated at an initial state.

## Main results

* `ActionPolicy.endpointKernel_isMarkov` — every finite endpoint kernel is
  normalized.
* `ActionPolicy.endpointMeasure_succ` — the Chapman--Kolmogorov successor
  recursion.
* `ActionPolicy.endpointMeasure_terminal` — terminal states remain Dirac at
  every horizon.
* `KernelArena.Policy.toMeasurable_endpointMeasure` — exact recovery of the
  existing discrete `stateLawFrom` finite law at every finite horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uS uA

namespace MeasurableKernelArena

namespace ActionPolicy

variable {A : MeasurableKernelArena}

/-- Supplied analytic endpoint kernels for one stopped policy.

Finite horizons do not make abstract kernel composition executable. The caller
supplies the kernels; the zero and successor certificates determine them
uniquely and retain the exact Chapman--Kolmogorov equations. -/
class EndpointExecution (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) where
  /-- Analytic state kernel at each finite horizon. -/
  kernel : ℕ → Kernel A.State A.State
  /-- At horizon zero the state is unchanged. -/
  zero_eq : kernel 0 = Kernel.id
  /-- One stopped step followed by the remaining horizon. -/
  succ_eq : ∀ horizon,
    kernel (horizon + 1) = kernel horizon ∘ₖ policy.stepKernel hterminal

/-- Analytic iteration proves existence without extracting executable kernels. -/
theorem EndpointExecution.nonempty (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) :
    Nonempty (EndpointExecution policy hterminal) := by
  let kernels : ℕ → Kernel A.State A.State :=
    Nat.rec Kernel.id (fun _ previous => previous ∘ₖ policy.stepKernel hterminal)
  exact ⟨{ kernel := kernels, zero_eq := rfl, succ_eq := fun _ => rfl }⟩

/-- The supplied state kernel after exactly `horizon` stopped steps. -/
def endpointKernel (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [execution : EndpointExecution policy hterminal] :
    ℕ → Kernel A.State A.State :=
  execution.kernel

@[simp]
theorem endpointKernel_zero (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal] :
    policy.endpointKernel hterminal 0 = Kernel.id :=
  EndpointExecution.zero_eq

theorem endpointKernel_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal] (horizon : ℕ) :
    policy.endpointKernel hterminal horizon.succ =
      policy.endpointKernel hterminal horizon ∘ₖ
        policy.stepKernel hterminal :=
  EndpointExecution.succ_eq horizon

@[simp]
theorem endpointKernel_one (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal] :
    policy.endpointKernel hterminal 1 =
      policy.stepKernel hterminal := by
  rw [show 1 = Nat.succ 0 by rfl, endpointKernel_succ,
    endpointKernel_zero, Kernel.id_comp]

/-- Finite endpoint kernels satisfy the Chapman--Kolmogorov composition law:
run `first` steps and then `second` steps. -/
theorem endpointKernel_add (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (first second : ℕ) :
    policy.endpointKernel hterminal (first + second) =
      policy.endpointKernel hterminal second ∘ₖ
        policy.endpointKernel hterminal first := by
  induction first with
  | zero =>
      rw [Nat.zero_add, endpointKernel_zero, Kernel.comp_id]
  | succ first ih =>
      rw [Nat.succ_add, endpointKernel_succ, ih,
        endpointKernel_succ, Kernel.comp_assoc]

instance endpointKernel_isMarkov (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal] (horizon : ℕ) :
    IsMarkovKernel (policy.endpointKernel hterminal horizon) := by
  induction horizon with
  | zero =>
      rw [endpointKernel_zero]
      infer_instance
  | succ horizon ih =>
      letI : IsMarkovKernel
          (policy.endpointKernel hterminal horizon) := ih
      rw [endpointKernel_succ]
      infer_instance

/-- The endpoint law from a particular initial state. -/
abbrev endpointMeasure (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (horizon : ℕ) (state : A.State) :
    Measure A.State :=
  policy.endpointKernel hterminal horizon state

@[simp]
theorem endpointMeasure_zero (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal] (state : A.State) :
    policy.endpointMeasure hterminal 0 state =
      Measure.dirac state := by
  rw [endpointMeasure, endpointKernel_zero, Kernel.id_apply]

/-- Successor endpoint laws satisfy the Chapman--Kolmogorov recursion: take
one stopped step, then run the remaining horizon. -/
theorem endpointMeasure_succ (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (horizon : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal horizon.succ state =
      (policy.stepKernel hterminal state).bind
        (policy.endpointKernel hterminal horizon) := by
  rw [endpointMeasure, endpointKernel_succ]
  rfl

/-- Measure-level Chapman--Kolmogorov equation for finite endpoints. -/
theorem endpointMeasure_add (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (first second : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal (first + second) state =
      (policy.endpointMeasure hterminal first state).bind
        (policy.endpointKernel hterminal second) := by
  rw [endpointMeasure, endpointKernel_add]
  rfl

/-- Equivalent successor recursion obtained by taking the existing endpoint
law and then one more stopped step. -/
theorem endpointMeasure_succ_right (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (horizon : ℕ) (state : A.State) :
    policy.endpointMeasure hterminal horizon.succ state =
      (policy.endpointMeasure hterminal horizon state).bind
        (policy.stepKernel hterminal) := by
  rw [show horizon.succ = horizon + 1 by omega,
    endpointMeasure_add, endpointKernel_one]

/-- A terminal state remains a Dirac endpoint at every horizon. -/
theorem endpointMeasure_terminal (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [EndpointExecution policy hterminal]
    (horizon : ℕ) (state : A.State)
    (hstate : IsEmpty (A.Action state)) :
    policy.endpointMeasure hterminal horizon state =
      Measure.dirac state := by
  induction horizon with
  | zero =>
      exact policy.endpointMeasure_zero hterminal state
  | succ horizon ih =>
      rw [policy.endpointMeasure_succ hterminal horizon state]
      rw [policy.stepKernel_apply_terminal hterminal state hstate]
      rw [Measure.dirac_bind
        (policy.endpointKernel hterminal horizon).measurable]
      exact ih

end ActionPolicy

end MeasurableKernelArena

namespace KernelArena

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

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
    (hmeasurable : Measurable fun x => finiteLawMeasure(next x)) :
    (atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
        0).bind (fun x => finiteLawMeasure(next x)) =
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

/-- Every finite analytic endpoint of an embedded discrete policy is exactly
the measure associated to the executable stopped endpoint law. -/
theorem Policy.toMeasurable_endpointMeasure
    {A : KernelArena}
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.Policy)
    [MeasurableKernelArena.ActionPolicy.EndpointExecution policy.toMeasurable
      A.toMeasurable_measurableSet_terminalSet]
    (horizon : ℕ) (state : A.State) :
    policy.toMeasurable.endpointMeasure
        A.toMeasurable_measurableSet_terminalSet horizon state =
      (A.stateLawFrom policy horizon state).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
        0 := by
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  induction horizon generalizing state with
  | zero =>
      rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_zero]
      rw [stateLawFrom]
      simp only [FiniteLaw.pure_atoms, List.foldr_cons, List.foldr_nil,
        add_zero]
      change
        Measure.dirac state =
          (((1 : ℚ≥0) : NNReal) : ENNReal) • Measure.dirac state
      simp
  | succ horizon ih =>
      by_cases hterminal : IsEmpty (A.Action state)
      · rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_terminal
          _ _ _ _ hterminal]
        simp only [stateLawFrom, dif_pos hterminal]
        simp only [FiniteLaw.pure_atoms, List.foldr_cons, List.foldr_nil,
          add_zero]
        change
          Measure.dirac state =
            (((1 : ℚ≥0) : NNReal) : ENNReal) • Measure.dirac state
        simp
      · rw [MeasurableKernelArena.ActionPolicy.endpointMeasure_succ]
        rw [Policy.toMeasurable_stepKernel_apply_nonterminal
          policy state hterminal]
        have hfunction :
            (fun nextState =>
              (A.stateLawFrom policy horizon nextState).atoms.foldr
                (fun atom rest =>
                  (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
                0) =
            (policy.toMeasurable.endpointKernel
              A.toMeasurable_measurableSet_terminalSet horizon) := by
          funext nextState
          exact (ih nextState).symm
        rw [← hfunction]
        have hmeasurable :
            Measurable fun nextState =>
              (A.stateLawFrom policy horizon nextState).atoms.foldr
                (fun atom rest =>
                  (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
                0 := by
          rw [hfunction]
          exact
            (policy.toMeasurable.endpointKernel
              A.toMeasurable_measurableSet_terminalSet horizon).measurable
        simp only [stateLawFrom, dif_neg hterminal,
          FiniteLaw.bind_atoms]
        exact finiteLawMeasure_flatMap _ _ hmeasurable

end KernelArena
