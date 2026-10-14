/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact finite expectations and their measure interpretation

This opt-in prototype proves that `FiniteLaw.expectRat` agrees with integration
against the finite weighted Dirac expression used by `KernelArena.toMeasurable`.
The local notation `μ[atoms]` only abbreviates that expression in statements;
it introduces no measure-producing declaration or alternative expectation.

`measure_eventMass` and `isProbabilityMeasure` identify event probabilities and
normalization on any measurable space. For `integrable` and
`integral_eq_expectRat`, measurable singletons suffice: any real function is
integrable against a finite weighted list of Dirac measures. The ambient type
need not be finite or countable, and the utility need not be globally measurable.
`measure_eq_of_equivalent` and `integral_eq_of_equivalent` separate equality of
measures from equality of sparse atom lists.

All numerical computation remains in the existing exact rational operations.
Measure expressions and integrals occur only in theorems and proofs. These
are experimental example results, not additions to the frozen frontend API.
-/

open MeasureTheory

namespace Examples.ExtensiveGame.FiniteLawIntegral

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

section MeasureInterpretation

variable {α : Type*} [MeasurableSpace α]

private theorem atomsMeasure_apply (atoms : List (α × ℚ≥0))
    (event : α → Bool) (hevent : MeasurableSet {x | event x}) :
    μ[atoms] {x | event x} =
      (((atoms.map fun atom => if event atom.1 then atom.2 else 0).sum : ℚ≥0) : ENNReal) := by
  induction atoms with
  | nil => simp [← ENNReal.coe_nnratCast]
  | cons atom atoms ih =>
      simp only [List.foldr_cons, Measure.add_apply, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ hevent,
        List.map_cons, List.sum_cons, ih]
      cases heq : event atom.1 <;> simp [heq, ← ENNReal.coe_nnratCast]

/-- The interpreted measure assigns exactly the executable Boolean event
mass to each measurable event. Measurability is required for Dirac evaluation. -/
theorem measure_eventMass (law : FiniteLaw α) (event : α → Bool)
    (hevent : MeasurableSet {x | event x}) :
    μ[law.atoms] {x | event x} = (law.eventMass event : ENNReal) :=
  atomsMeasure_apply law.atoms event hevent

/-- Normalization follows from the stored sum of atom weights; it is not an
additional certificate supplied by the caller. -/
theorem isProbabilityMeasure (law : FiniteLaw α) : IsProbabilityMeasure μ[law.atoms] := by
  constructor
  have h := measure_eventMass law (fun _ => true) (by simp)
  simpa [FiniteLaw.eventMass, law.normalized, ← ENNReal.coe_nnratCast] using h

/-- Equivalent sparse laws induce equal measures. No equality decision or
measurable-singleton assumption on the outcome type is needed. -/
theorem measure_eq_of_equivalent {left right : FiniteLaw α}
    (h : left.Equivalent right) : μ[left.atoms] = μ[right.atoms] := by
  classical
  apply Measure.ext
  intro s hs
  let event : α → Bool := fun x => decide (x ∈ s)
  have hevent : {x | event x} = s := by ext x; simp [event]
  have hmeasurable : MeasurableSet {x | event x} := hevent.symm ▸ hs
  rw [← hevent, measure_eventMass left event hmeasurable,
    measure_eventMass right event hmeasurable, h.eventMass event]

section Integral

variable [MeasurableSingletonClass α]

private theorem integrable_atomsMeasure (atoms : List (α × ℚ≥0)) (value : α → ℝ) :
    Integrable value μ[atoms] := by
  induction atoms with
  | nil => exact integrable_zero_measure
  | cons atom atoms ih =>
      exact ((integrable_dirac (f := value) (a := atom.1) (by simp)).smul_measure
        ENNReal.coe_ne_top).add_measure ih

/-- Every real observable is integrable against this finite atomic measure.
Measurable singletons make it almost everywhere equal to measurable point data. -/
theorem integrable (law : FiniteLaw α) (value : α → ℝ) : Integrable value μ[law.atoms] :=
  integrable_atomsMeasure law.atoms value

private theorem integral_atomsMeasure (atoms : List (α × ℚ≥0)) (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[atoms]) =
      (((atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum : ℚ) : ℝ) := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      rw [List.foldr_cons, integral_add_measure
        ((integrable_dirac (f := fun x => (value x : ℝ)) (a := atom.1) (by simp)).smul_measure
          (c := (atom.2 : ENNReal)) ENNReal.coe_ne_top) (integrable_atomsMeasure atoms _),
        integral_smul_measure, integral_dirac, ih]
      have hweight : (atom.2 : ENNReal).toReal = (atom.2 : ℝ) := rfl
      simp [hweight]

/-- The exact rational computation is the Bochner integral of the same utility
under the law's actual finite weighted Dirac interpretation. -/
theorem integral_eq_expectRat (law : FiniteLaw α) (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[law.atoms]) = (law.expectRat value : ℝ) :=
  integral_atomsMeasure law.atoms value

end Integral

/-- The integral is unchanged by semantic equivalence of finite laws,
including reordered, duplicated, or zero-weight atoms. Equality of measures
suffices here, without any measurable-singleton assumption. -/
theorem integral_eq_of_equivalent {left right : FiniteLaw α}
    (h : left.Equivalent right) (value : α → ℚ) :
    (∫ x, (value x : ℝ) ∂μ[left.atoms]) =
      ∫ x, (value x : ℝ) ∂μ[right.atoms] := by
  rw [measure_eq_of_equivalent h]

end MeasureInterpretation

section Regression

local instance : MeasurableSpace ℕ := ⊤

/-- A sparse law with a duplicated state and a zero-weight occurrence, on an
infinite ambient state type. -/
def splitLaw : FiniteLaw ℕ where
  atoms := [(2, 1 / 4), (7, 1 / 3), (2, 1 / 4), (99, 0), (11, 1 / 6)]
  normalized := by norm_num

/-- The same law with repetitions merged, the zero occurrence removed, and
the remaining atoms reordered. -/
def mergedLaw : FiniteLaw ℕ where
  atoms := [(11, 1 / 6), (2, 1 / 2), (7, 1 / 3)]
  normalized := by norm_num

/-- Signed rational payoffs on the positive support, with large and unbounded
off-support values. In particular the zero-weight occurrence has payoff 1099. -/
def payoff (state : ℕ) : ℚ :=
  if state = 2 then -3 / 2
  else if state = 7 then 5 / 2
  else if state = 11 then -1
  else state + 1000

/-- Equality of sparse representations is strictly stronger than the semantic
comparison used here: the lists even have different lengths. -/
theorem splitLaw_ne_mergedLaw : splitLaw ≠ mergedLaw := by
  intro h
  have hlength := congrArg (fun law : FiniteLaw ℕ => law.atoms.length) h
  norm_num [splitLaw, mergedLaw] at hlength

/-- Merging, deleting zero weight, and reordering preserve every rational
observable, not just the selected regression payoff. -/
theorem splitLaw_equivalent : splitLaw.Equivalent mergedLaw := by
  intro value
  change splitLaw.expectRat value = mergedLaw.expectRat value
  norm_num [FiniteLaw.expectRat, splitLaw, mergedLaw]
  ring

/-- The exact expectation is negative and nonintegral. -/
theorem splitLaw_expectRat : splitLaw.expectRat payoff = -1 / 12 := by
  norm_num [FiniteLaw.expectRat, splitLaw, payoff]

/-- Integration against the actual atom measure agrees with the executable
value; no separately supplied integral or measure certificate is used. -/
theorem splitLaw_integral : (∫ x, (payoff x : ℝ) ∂μ[splitLaw.atoms]) = -1 / 12 := by
  rw [integral_eq_expectRat, splitLaw_expectRat]
  norm_num

/-- Both occurrences of state two contribute to its event probability. -/
theorem splitLaw_duplicate_probability :
    μ[splitLaw.atoms] {2} = ((1 / 2 : ℚ≥0) : ENNReal) := by
  have h := measure_eventMass splitLaw (fun x => decide (x = 2)) (by simp)
  norm_num [FiniteLaw.eventMass, splitLaw] at h ⊢
  exact h

/-- The explicitly listed zero-weight state still has probability zero. -/
theorem splitLaw_zero_probability : μ[splitLaw.atoms] {99} = 0 := by
  simp [splitLaw, ← ENNReal.coe_nnratCast]

/-- Different sparse presentations induce the same measure, and hence all
measurable events have the same probabilities. -/
theorem splitLaw_measure_eq : μ[splitLaw.atoms] = μ[mergedLaw.atoms] :=
  measure_eq_of_equivalent splitLaw_equivalent

/-- The reordered and merged presentation has the same analytic expectation. -/
theorem mergedLaw_integral : (∫ x, (payoff x : ℝ) ∂μ[mergedLaw.atoms]) = -1 / 12 := by
  rw [← integral_eq_of_equivalent splitLaw_equivalent payoff]
  exact splitLaw_integral

-- Native evaluation checks exact arithmetic; the exported proofs above use the kernel.
/-- info: true -/
#guard_msgs in
#eval splitLaw.expectRat payoff == (-1 / 12 : ℚ) &&
  mergedLaw.expectRat payoff == (-1 / 12 : ℚ) &&
  splitLaw.eventMass (fun x => decide (x = 2)) == (1 / 2 : ℚ≥0) &&
  splitLaw.eventMass (fun x => decide (x = 99)) == 0

end Regression

end Examples.ExtensiveGame.FiniteLawIntegral
