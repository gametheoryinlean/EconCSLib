/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteMarkovChain

/-!
# Exact discounted values for finite rational Markov chains

This module computes infinite-horizon discounted values for the transient
states of any `FiniteMarkovChain.Chain`.  The chain need not absorb: closed
nonterminal classes are harmless because the explicit discount is a rational
number `γ` satisfying `0 ≤ γ < 1`.

The executable solver checks that rational inequality and then applies
Cramer's rule to `I - γQ`.  Nonsingularity is proved internally by a finite,
purely rational maximum-coordinate argument.  Callers supply neither an
inverse nor a determinant certificate.  Finite-horizon values, exact Bellman
unrolling, and a rational geometric remainder bound are provided alongside
the solver.

The implementation imports no measure theory, real analysis, or domain
library.  All computed coefficients and comparisons are exact rationals.

## Reading order

The discounted operator and its coordinate bounds come first.  A fixed-point
lemma then proves nonsingularity, which justifies the executable solver.
Bellman uniqueness precedes finite unrolling and the geometric error bound.
Only these correctness results assume a valid discount; the definitions and
the finite unrolling identity remain available for any rational discount.
-/

namespace FiniteMarkovChain.Chain

open Matrix
open scoped BigOperators

variable {n m : ℕ} (C : Chain n m)

/-! ## Discounted operators and coordinate bounds -/

section Operators

/-- The discounted transient operator `γQ`. -/
def discountedQ (γ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  γ • C.Q

/-- The discounted Bellman coefficient matrix `I - γQ`. -/
def discountedMatrix (γ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  1 - C.discountedQ γ

/-- Executable validation of a rational discount. -/
def validDiscount (γ : ℚ) : Bool :=
  decide (0 ≤ γ ∧ γ < 1)

@[simp]
theorem validDiscount_eq_true_iff (γ : ℚ) :
    validDiscount γ = true ↔ 0 ≤ γ ∧ γ < 1 := by
  simp [validDiscount]

/-- Every transient row has mass at most one, whether or not the chain
eventually absorbs. -/
theorem Q_rowSum_le_one (i : Fin n) : (∑ j, C.Q i j) ≤ 1 := by
  have hterminal :=
    Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => C.R_nonneg i a)
  linarith [C.row_sum i]

/-- Discounted transient coefficients are nonnegative at a valid
nonnegative discount. -/
theorem discountedQ_nonneg {γ : ℚ} (hγ : 0 ≤ γ) (i j : Fin n) :
    0 ≤ C.discountedQ γ i j := by
  exact mul_nonneg hγ (C.Q_nonneg i j)

/-- Every discounted transient row has mass at most `γ`. -/
theorem discountedQ_rowSum_le {γ : ℚ} (hγ : 0 ≤ γ) (i : Fin n) :
    (∑ j, C.discountedQ γ i j) ≤ γ := by
  simp only [discountedQ, smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (C.Q_rowSum_le_one i) hγ

/-- One application of `γQ` contracts a coordinatewise absolute bound by
the factor `γ`. -/
theorem abs_discountedQ_mulVec_le
    {γ bound : ℚ} (hγ : 0 ≤ γ) (hbound : 0 ≤ bound)
    (value : Fin n → ℚ) (hvalue : ∀ j, |value j| ≤ bound)
    (i : Fin n) :
    |(C.discountedQ γ *ᵥ value) i| ≤ γ * bound := by
  calc
    |(C.discountedQ γ *ᵥ value) i| =
        |∑ j, C.discountedQ γ i j * value j| := rfl
    _ ≤ ∑ j, |C.discountedQ γ i j * value j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, C.discountedQ γ i j * |value j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (C.discountedQ_nonneg hγ i j)]
    _ ≤ ∑ j, C.discountedQ γ i j * bound := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (hvalue j) (C.discountedQ_nonneg hγ i j)
    _ = (∑ j, C.discountedQ γ i j) * bound := by
      rw [Finset.sum_mul]
    _ ≤ γ * bound :=
      mul_le_mul_of_nonneg_right (C.discountedQ_rowSum_le hγ i) hbound

/-- Powers of `γQ` satisfy the exact geometric coordinate bound. -/
theorem abs_discountedQ_pow_mulVec_le
    {γ bound : ℚ} (hγ : 0 ≤ γ) (hbound : 0 ≤ bound)
    (value : Fin n → ℚ) (hvalue : ∀ j, |value j| ≤ bound)
    (horizon : ℕ) (i : Fin n) :
    |(C.discountedQ γ ^ horizon *ᵥ value) i| ≤ γ ^ horizon * bound := by
  induction horizon generalizing i with
  | zero => simpa using hvalue i
  | succ horizon ih =>
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      have hpow : 0 ≤ γ ^ horizon * bound :=
        mul_nonneg (_root_.pow_nonneg hγ _) hbound
      have hstep := C.abs_discountedQ_mulVec_le hγ hpow
        (C.discountedQ γ ^ horizon *ᵥ value) (fun j => ih j) i
      calc
        _ ≤ γ * (γ ^ horizon * bound) := hstep
        _ = γ ^ (horizon + 1) * bound := by
          rw [pow_succ]
          ring

end Operators

/-! ## Strict contraction and nonsingularity -/

section ValidDiscount

variable {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

include hγ0 hγ1

private lemma eq_zero_of_discounted_fixed (difference : Fin n → ℚ)
    (hfixed : difference = C.discountedQ γ *ᵥ difference) : difference = 0 := by
  cases isEmpty_or_nonempty (Fin n)
  · funext i
    exact isEmptyElim i
  · have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty
    obtain ⟨maxIndex, _, hmaxValue⟩ :=
      Finset.exists_mem_eq_sup' huniv fun i => |difference i|
    have hmax (j : Fin n) :
        |difference j| ≤ |difference maxIndex| := by
      rw [← hmaxValue]
      exact Finset.le_sup' (fun i => |difference i|) (Finset.mem_univ j)
    have hcontract :
        |difference maxIndex| ≤ γ * |difference maxIndex| := by
      calc
        |difference maxIndex| =
            |(C.discountedQ γ *ᵥ difference) maxIndex| :=
          congrArg abs (congrFun hfixed maxIndex)
        _ ≤ γ * |difference maxIndex| :=
          C.abs_discountedQ_mulVec_le hγ0
            (abs_nonneg (difference maxIndex)) difference hmax maxIndex
    have hmaxZero : difference maxIndex = 0 := by
      by_contra hne
      have hpositive : 0 < |difference maxIndex| := abs_pos.mpr hne
      have hstrict :
          γ * |difference maxIndex| < |difference maxIndex| := by
        nlinarith
      exact (not_lt_of_ge hcontract) hstrict
    funext j
    apply abs_eq_zero.mp
    apply le_antisymm
    · simpa [hmaxZero] using hmax j
    · exact abs_nonneg _

/-- For `0 ≤ γ < 1`, the Bellman coefficient matrix acts injectively on
rational vectors.  Strict contraction makes the difference of two solutions
zero. -/
theorem discountedMatrix_mulVec_injective :
    Function.Injective (C.discountedMatrix γ).mulVec := by
  intro left right hequal
  have hzero : C.discountedMatrix γ *ᵥ (left - right) = 0 := by
    rw [Matrix.mulVec_sub, hequal, sub_self]
  have hfixed : left - right = C.discountedQ γ *ᵥ (left - right) := by
    rw [discountedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec] at hzero
    exact sub_eq_zero.mp hzero
  exact sub_eq_zero.mp (C.eq_zero_of_discounted_fixed hγ0 hγ1 _ hfixed)

/-- The discounted Bellman matrix is nonsingular for every valid rational
discount.  This is proved by the algorithm's own contraction argument. -/
theorem discountedMatrix_det_ne_zero :
    (C.discountedMatrix γ).det ≠ 0 := by
  have hunit : IsUnit (C.discountedMatrix γ) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (C.discountedMatrix_mulVec_injective hγ0 hγ1)
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

end ValidDiscount

/-! ## Executable solver and Bellman correctness -/

section Solver

/-- Direct exact Cramer vector for discounted reward.  Correctness is stated
under the explicit rational discount inequalities below. -/
def discountedValue (γ : ℚ) (reward : Fin n → ℚ) : Fin n → ℚ :=
  (C.discountedMatrix γ).det⁻¹ •
    (C.discountedMatrix γ).cramer reward

/-- Total executable discounted solver.  Invalid discounts return `none`;
every valid discount returns the exact Cramer vector, with nonsingularity
proved internally rather than checked as a second possible failure. -/
def solveDiscounted (γ : ℚ) (reward : Fin n → ℚ) :
    Option (Fin n → ℚ) :=
  if validDiscount γ then some (C.discountedValue γ reward) else none

@[simp]
theorem solveDiscounted_eq_none_iff (γ : ℚ) (reward : Fin n → ℚ) :
    C.solveDiscounted γ reward = none ↔ ¬ (0 ≤ γ ∧ γ < 1) := by
  simp [solveDiscounted, validDiscount]

theorem solveDiscounted_eq_some_iff
    (γ : ℚ) (reward value : Fin n → ℚ) :
    C.solveDiscounted γ reward = some value ↔
      0 ≤ γ ∧ γ < 1 ∧ value = C.discountedValue γ reward := by
  by_cases hvalid : 0 ≤ γ ∧ γ < 1
  · simp [solveDiscounted, validDiscount, hvalid, eq_comm]
  · constructor
    · intro hsome
      simp [solveDiscounted, validDiscount, hvalid] at hsome
    · rintro ⟨hγ0, hγ1, _⟩
      exact (hvalid ⟨hγ0, hγ1⟩).elim

/-- The exact Cramer vector solves `(I - γQ)v = r`. -/
theorem discountedValue_system
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) :
    C.discountedMatrix γ *ᵥ C.discountedValue γ reward = reward := by
  have hdet := C.discountedMatrix_det_ne_zero hγ0 hγ1
  unfold discountedValue
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
    inv_mul_cancel₀ hdet, one_smul]

/-- Matrix form and Bellman fixed-point form are exactly equivalent. -/
theorem discountedMatrix_mulVec_eq_iff_bellman
    (γ : ℚ) (reward value : Fin n → ℚ) :
    C.discountedMatrix γ *ᵥ value = reward ↔
      value = reward + C.discountedQ γ *ᵥ value := by
  rw [discountedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_eq_iff_eq_add

/-- The computed value satisfies the discounted Bellman equation. -/
theorem discountedValue_bellman
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) :
    C.discountedValue γ reward =
      reward + C.discountedQ γ *ᵥ C.discountedValue γ reward :=
  (C.discountedMatrix_mulVec_eq_iff_bellman
    γ reward (C.discountedValue γ reward)).mp
      (C.discountedValue_system hγ0 hγ1 reward)

/-- The Bellman equation has at most one rational solution at a valid
discount. -/
theorem discountedBellman_unique
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) {left right : Fin n → ℚ}
    (hleft : left = reward + C.discountedQ γ *ᵥ left)
    (hright : right = reward + C.discountedQ γ *ᵥ right) :
    left = right := by
  apply C.discountedMatrix_mulVec_injective hγ0 hγ1
  rw [(C.discountedMatrix_mulVec_eq_iff_bellman γ reward left).mpr hleft]
  rw [(C.discountedMatrix_mulVec_eq_iff_bellman γ reward right).mpr hright]

/-- Every successful executable call returns the unique Bellman solution. -/
theorem solveDiscounted_sound
    (γ : ℚ) (reward value : Fin n → ℚ)
    (hsolve : C.solveDiscounted γ reward = some value) :
    0 ≤ γ ∧ γ < 1 ∧
      C.discountedMatrix γ *ᵥ value = reward ∧
      ∀ candidate,
        candidate = reward + C.discountedQ γ *ᵥ candidate →
          candidate = value := by
  obtain ⟨hγ0, hγ1, rfl⟩ :=
    (C.solveDiscounted_eq_some_iff γ reward value).mp hsolve
  refine ⟨hγ0, hγ1, C.discountedValue_system hγ0 hγ1 reward, ?_⟩
  intro candidate hcandidate
  exact C.discountedBellman_unique hγ0 hγ1 reward hcandidate
    (C.discountedValue_bellman hγ0 hγ1 reward)

end Solver

/-! ## Finite horizons and geometric error -/

section FiniteHorizon

/-- Exact finite-horizon discounted reward, with rewards collected at times
`0, ..., horizon - 1`. -/
def finiteDiscountedValue
    (γ : ℚ) (reward : Fin n → ℚ) (horizon : ℕ) : Fin n → ℚ :=
  ∑ step ∈ Finset.range horizon,
    C.discountedQ γ ^ step *ᵥ reward

@[simp]
theorem finiteDiscountedValue_zero
    (γ : ℚ) (reward : Fin n → ℚ) :
    C.finiteDiscountedValue γ reward 0 = 0 := by
  simp [finiteDiscountedValue]

/-- Extending the finite horizon adds exactly the next discounted reward
vector. -/
theorem finiteDiscountedValue_succ
    (γ : ℚ) (reward : Fin n → ℚ) (horizon : ℕ) :
    C.finiteDiscountedValue γ reward (horizon + 1) =
      C.finiteDiscountedValue γ reward horizon +
        C.discountedQ γ ^ horizon *ᵥ reward := by
  simp [finiteDiscountedValue, Finset.sum_range_succ]

/-- Any discounted Bellman fixed point admits an exact finite geometric
unroll with an explicit remainder. -/
theorem discountedBellman_unroll
    (γ : ℚ) (reward value : Fin n → ℚ)
    (hvalue : value = reward + C.discountedQ γ *ᵥ value)
    (horizon : ℕ) :
    value = C.finiteDiscountedValue γ reward horizon +
      C.discountedQ γ ^ horizon *ᵥ value := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      calc
        value = C.finiteDiscountedValue γ reward horizon +
            C.discountedQ γ ^ horizon *ᵥ value := ih
        _ = C.finiteDiscountedValue γ reward horizon +
            C.discountedQ γ ^ horizon *ᵥ
              (reward + C.discountedQ γ *ᵥ value) :=
          congrArg
            (fun continuation : Fin n → ℚ =>
              C.finiteDiscountedValue γ reward horizon +
                C.discountedQ γ ^ horizon *ᵥ continuation)
            hvalue
        _ = (C.finiteDiscountedValue γ reward horizon +
              C.discountedQ γ ^ horizon *ᵥ reward) +
            C.discountedQ γ ^ (horizon + 1) *ᵥ value := by
          rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ]
          simp only [add_assoc]
        _ = C.finiteDiscountedValue γ reward (horizon + 1) +
            C.discountedQ γ ^ (horizon + 1) *ᵥ value := by
          rw [C.finiteDiscountedValue_succ]

/-- The computed infinite-horizon value is the finite discounted value plus
the exact continuation remainder. -/
theorem discountedValue_unroll
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) (horizon : ℕ) :
    C.discountedValue γ reward =
      C.finiteDiscountedValue γ reward horizon +
        C.discountedQ γ ^ horizon *ᵥ C.discountedValue γ reward :=
  C.discountedBellman_unroll γ reward (C.discountedValue γ reward)
    (C.discountedValue_bellman hγ0 hγ1 reward) horizon

/-- A uniformly bounded per-step reward gives the exact rational value bound
`B / (1 - γ)`, without any absorption premise. -/
theorem abs_discountedValue_le
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) (bound : ℚ≥0)
    (hreward : ∀ i, |reward i| ≤ (bound : ℚ))
    (i : Fin n) :
    |C.discountedValue γ reward i| ≤ (bound : ℚ) / (1 - γ) := by
  let value := C.discountedValue γ reward
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨i, Finset.mem_univ i⟩
  obtain ⟨maxIndex, _, hmaxValue⟩ :=
    Finset.exists_mem_eq_sup' huniv fun j => |value j|
  have hmax (j : Fin n) : |value j| ≤ |value maxIndex| := by
    rw [← hmaxValue]
    exact Finset.le_sup' (fun k => |value k|) (Finset.mem_univ j)
  have hoperator :
      |(C.discountedQ γ *ᵥ value) maxIndex| ≤
        γ * |value maxIndex| :=
    C.abs_discountedQ_mulVec_le hγ0 (abs_nonneg (value maxIndex))
      value hmax maxIndex
  have hbellman := C.discountedValue_bellman hγ0 hγ1 reward
  have hcenter :
      |value maxIndex| ≤ (bound : ℚ) + γ * |value maxIndex| := by
    calc
      |value maxIndex| =
          |reward maxIndex + (C.discountedQ γ *ᵥ value) maxIndex| := by
        exact congrArg abs (congrFun hbellman maxIndex)
      _ ≤ |reward maxIndex| +
          |(C.discountedQ γ *ᵥ value) maxIndex| :=
        abs_add_le _ _
      _ ≤ (bound : ℚ) + γ * |value maxIndex| :=
        add_le_add (hreward maxIndex) hoperator
  have hmaxBound :
      |value maxIndex| ≤ (bound : ℚ) / (1 - γ) := by
    apply (le_div_iff₀ (sub_pos.mpr hγ1)).mpr
    nlinarith
  exact (hmax i).trans hmaxBound

/-- Exact rational truncation error.  If every per-step reward has absolute
value at most `B`, the horizon-`H` remainder is at most
`B * γ^H / (1 - γ)` at every start state. -/
theorem abs_discountedValue_sub_finite_le
    {γ : ℚ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (reward : Fin n → ℚ) (bound : ℚ≥0)
    (hreward : ∀ i, |reward i| ≤ (bound : ℚ))
    (horizon : ℕ) (i : Fin n) :
    |C.discountedValue γ reward i -
        C.finiteDiscountedValue γ reward horizon i| ≤
      (bound : ℚ) * γ ^ horizon / (1 - γ) := by
  have hunroll := congrFun
    (C.discountedValue_unroll hγ0 hγ1 reward horizon) i
  have hdifference :
      C.discountedValue γ reward i -
          C.finiteDiscountedValue γ reward horizon i =
        (C.discountedQ γ ^ horizon *ᵥ
          C.discountedValue γ reward) i := by
    rw [hunroll]
    simp
  rw [hdifference]
  have hdenom : 0 ≤ (bound : ℚ) / (1 - γ) :=
    div_nonneg bound.property (sub_nonneg.mpr hγ1.le)
  calc
    |(C.discountedQ γ ^ horizon *ᵥ
        C.discountedValue γ reward) i| ≤
        γ ^ horizon * ((bound : ℚ) / (1 - γ)) :=
      C.abs_discountedQ_pow_mulVec_le hγ0 hdenom
        (C.discountedValue γ reward)
        (C.abs_discountedValue_le hγ0 hγ1 reward bound hreward)
        horizon i
    _ = (bound : ℚ) * γ ^ horizon / (1 - γ) := by
      ring

end FiniteHorizon

end FiniteMarkovChain.Chain
