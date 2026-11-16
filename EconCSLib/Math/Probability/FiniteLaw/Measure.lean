/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

/-!
# Measure semantics of exact finite laws

This analytic leaf proves that the finite weighted sum of Dirac measures
represented by a `FiniteLaw` has exactly the probability and expectation
computed by its executable rational operations.  It deliberately introduces
no measure-producing definition: numerical code continues to consume
`FiniteLaw`, while analytic modules spell out the finite Dirac interpretation
in theorem statements.

The ambient carrier need not be finite or countable.  Event evaluation only
requires the event to be measurable.  Integrability of arbitrary real-valued
observables additionally uses measurable singletons, because the measure has
finite support even when the observable is unbounded off that support.

## Main results

* `FiniteLaw.measure_eventMass` and `measure_isProbability`;
* `FiniteLaw.measure_pure`, `measure_map`, and `measure_bind`;
* `FiniteLaw.measure_eq_of_equivalent`;
* `FiniteLaw.integrable_measure` and `integral_measure_eq_expectRat`.
-/

open MeasureTheory

namespace FiniteLaw

universe uα uβ

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

section Basic

variable {α : Type uα} [MeasurableSpace α]

private theorem measure_apply (atoms : List (α × ℚ≥0))
    (event : α → Bool) (hevent : MeasurableSet {x | event x}) :
    μ[atoms] {x | event x} =
      (((atoms.map fun atom => if event atom.1 then atom.2 else 0).sum : ℚ≥0) :
        ENNReal) := by
  induction atoms with
  | nil => simp [← ENNReal.coe_nnratCast]
  | cons atom atoms ih =>
      simp only [List.foldr_cons, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ hevent,
        List.map_cons, List.sum_cons, ih]
      cases heq : event atom.1 <;>
        simp [heq, ← ENNReal.coe_nnratCast]

/-- The finite Dirac interpretation assigns every measurable Boolean event
its executable exact mass. -/
theorem measure_eventMass (law : FiniteLaw α) (event : α → Bool)
    (hevent : MeasurableSet {x | event x}) :
    μ[law.atoms] {x | event x} = (law.eventMass event : ENNReal) :=
  measure_apply law.atoms event hevent

/-- Normalization of the finite Dirac interpretation follows from the
normalization stored by the executable law. -/
theorem measure_isProbability (law : FiniteLaw α) :
    IsProbabilityMeasure μ[law.atoms] := by
  constructor
  have h := law.measure_eventMass (fun _ => true) (by simp)
  simpa [eventMass, law.normalized, ← ENNReal.coe_nnratCast] using h

/-- A point finite law is interpreted as the corresponding Dirac measure. -/
theorem measure_pure (outcome : α) :
    μ[(FiniteLaw.pure outcome).atoms] = Measure.dirac outcome := by
  rw [pure_atoms]
  simp only [List.foldr_cons, List.foldr_nil]
  change (((1 : ℚ≥0) : NNReal) : ENNReal) •
      Measure.dirac outcome + 0 = Measure.dirac outcome
  simp

private theorem measure_append (left right : List (α × ℚ≥0)) :
    μ[left ++ right] = μ[left] + μ[right] := by
  induction left with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.cons_append, List.foldr_cons]
      rw [ih, add_assoc]

private theorem measure_map_mul (weight : ℚ≥0)
    (atoms : List (α × ℚ≥0)) :
    μ[atoms.map fun atom => (atom.1, weight * atom.2)] =
      (weight : ENNReal) • μ[atoms] := by
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

/-- Measurable pushforward commutes with the finite Dirac interpretation. -/
theorem measure_map {β : Type uβ} [MeasurableSpace β]
    (law : FiniteLaw α) (f : α → β) (hf : Measurable f) :
    μ[law.atoms].map f = μ[(law.map f).atoms] := by
  rw [map_atoms]
  ext event hevent
  rw [Measure.map_apply hf hevent]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.map_cons, List.foldr_cons]
      simp [Measure.dirac_apply' _ hevent,
        Measure.dirac_apply' _ (hf hevent), ih]
      rfl

private theorem measure_bind_add {β : Type uβ} [MeasurableSpace β]
    (left right : Measure α) (next : α → Measure β)
    (hmeasurable : Measurable next) :
    (left + right).bind next = left.bind next + right.bind next := by
  ext event hevent
  simp [Measure.bind_apply, hevent, hmeasurable.aemeasurable,
    MeasureTheory.lintegral_add_measure]

/-- Measure bind commutes with executable finite-law bind whenever the
interpreted continuation family is measurable. -/
theorem measure_bind {β : Type uβ} [MeasurableSpace β]
    (law : FiniteLaw α) (next : α → FiniteLaw β)
    (hmeasurable : Measurable fun x => μ[(next x).atoms]) :
    μ[law.atoms].bind (fun x => μ[(next x).atoms]) =
      μ[(law.bind next).atoms] := by
  rw [bind_atoms]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.foldr_cons, List.flatMap_cons]
      rw [measure_bind_add _ _ _ hmeasurable,
        Measure.bind_smul, Measure.dirac_bind hmeasurable,
        ih, measure_append, measure_map_mul]

/-- Semantically equivalent sparse finite laws induce equal measures. -/
theorem measure_eq_of_equivalent {left right : FiniteLaw α}
    (h : left.Equivalent right) : μ[left.atoms] = μ[right.atoms] := by
  classical
  apply Measure.ext
  intro event hevent
  let test : α → Bool := fun x => decide (x ∈ event)
  have htest : {x | test x} = event := by
    ext x
    simp [test]
  have hmeasurable : MeasurableSet {x | test x} := htest.symm ▸ hevent
  rw [← htest, left.measure_eventMass test hmeasurable,
    right.measure_eventMass test hmeasurable, h.eventMass test]

section Integral

variable [MeasurableSingletonClass α]

private theorem integrable_atoms (atoms : List (α × ℚ≥0))
    (value : α → ℝ) : Integrable value μ[atoms] := by
  induction atoms with
  | nil => exact integrable_zero_measure
  | cons atom atoms ih =>
      exact
        ((integrable_dirac (f := value) (a := atom.1) (by simp)).smul_measure
          ENNReal.coe_ne_top).add_measure ih

/-- Every real observable is integrable against the finite Dirac
interpretation when singletons are measurable. -/
theorem integrable_measure (law : FiniteLaw α) (value : α → ℝ) :
    Integrable value μ[law.atoms] :=
  integrable_atoms law.atoms value

private theorem integral_atoms (atoms : List (α × ℚ≥0))
    (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[atoms]) =
      (((atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum : ℚ) : ℝ) := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      rw [List.foldr_cons, integral_add_measure
        ((integrable_dirac (f := fun x => (value x : ℝ))
          (a := atom.1) (by simp)).smul_measure
            (c := (atom.2 : ENNReal)) ENNReal.coe_ne_top)
        (integrable_atoms atoms _), integral_smul_measure,
        integral_dirac, ih]
      have hweight : (atom.2 : ENNReal).toReal = (atom.2 : ℝ) := rfl
      simp [hweight]

/-- Exact rational expectation equals the Bochner integral of the same
observable under the finite Dirac interpretation. -/
theorem integral_measure_eq_expectRat (law : FiniteLaw α)
    (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[law.atoms]) =
      (law.expectRat value : ℝ) :=
  integral_atoms law.atoms value

end Integral

/-- Integration is unchanged by semantic equivalence of finite laws. -/
theorem integral_measure_eq_of_equivalent {left right : FiniteLaw α}
    (h : left.Equivalent right) (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[left.atoms]) =
      ∫ x, (value x : ℝ) ∂μ[right.atoms] := by
  rw [measure_eq_of_equivalent h]

end Basic

end FiniteLaw
