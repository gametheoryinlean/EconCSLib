/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NoRegret.Basic
import EconCSLib.Math.Probability.Blackwell
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# External regret and Blackwell approachability

This module formalizes external regret, the negative-orthant Blackwell
argument, and external-regret matching from [MFoGT, Section 7.3.1].
It provides both a reusable conditional-process theorem and, in
`NoRegret.Process`, a canonical finite-history realization of the rule.

MFoGT uses `alternative payoff - realized payoff` and the nonpositive orthant.
[MSZ, Section 14.8] uses the negated vector and the nonnegative orthant.

## References

* [MFoGT] Chapter 7, Section 7.3.1
* [MSZ] Chapter 14, Section 14.8
-/

open Finset BigOperators Filter Topology
open scoped MeasureTheory

namespace StrategicGame

universe uK uL uN uS uΩ uOut

/-! ### Approachability skeleton: MFoGT Theorem 7.3.2 and Lemma 7.3.3 -/

/-- Projection to the negative orthant in coordinates. -/
noncomputable def negativeOrthantProjection {K : Type uK} (x : K → ℝ) : K → ℝ :=
  fun k => min (x k) 0

/-- Coordinatewise positive part of a vector. -/
noncomputable def vectorPosPart {K : Type uK} (x : K → ℝ) : K → ℝ :=
  fun k => posPart (x k)

/-- Empirical average of a vector-valued sequence up to stage `n + 1`. -/
noncomputable def averageVector {K : Type uK}
    (x : ℕ → K → ℝ) (n : ℕ) : K → ℝ :=
  fun k => ((n + 1 : ℝ)⁻¹) * ∑ t : Fin (n + 1), x t.val k

/-- The Blackwell one-step inequality for approaching the negative orthant,
written in finite coordinates. The second sequence is the conditional-expectation
sequence `y_{n+1}` from [MFoGT Theorem 7.3.2]. -/
noncomputable def BlackwellNegativeOrthantCondition {K : Type uK} [Fintype K]
    (xbar y : ℕ → K → ℝ) : Prop :=
  ∀ n : ℕ,
    ∑ k : K,
      (vectorPosPart (xbar n) k) *
        (y (n + 1) k - negativeOrthantProjection (xbar n) k) ≤ 0

/-- Approaching the negative orthant in finite coordinates. -/
def ApproachesNegativeOrthant {K : Type uK} (xbar : ℕ → K → ℝ) : Prop :=
  ∀ k : K, VanishesAboveZero fun n => posPart (xbar n k)

/-! ### Pathwise potential recursion

The squared distance from the running average to the nonpositive orthant
satisfies a one-step inequality whose cross term is the Blackwell inner
product. The probability layer later takes conditional expectations of this
inequality. -/

/-- Squared-distance-to-the-negative-orthant potential of a vector: sum of squared positive
parts. -/
noncomputable def orthantPotential {K : Type uK} [Fintype K] (x : K → ℝ) : ℝ :=
  ∑ k : K, posPart (x k) ^ 2

lemma orthantPotential_nonneg {K : Type uK} [Fintype K] (x : K → ℝ) :
    0 ≤ orthantPotential x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- If `p ≤ 0`, the positive part of `a` is dominated by `a - p`: this is the elementary fact
that the negative orthant contains every nonpositive vector, so the distance from `a` to the
orthant is at most the distance from `a` to `p`. -/
lemma posPart_sq_le_sub_sq {a p : ℝ} (hp : p ≤ 0) : posPart a ^ 2 ≤ (a - p) ^ 2 := by
  unfold posPart
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    nlinarith [sq_nonneg (a - p)]
  · rw [max_eq_left ha]
    nlinarith [mul_nonneg (neg_nonneg.mpr hp) ha, sq_nonneg p]

/-- The recursive update of the running average when a new sample is appended at stage
`n + 1`. -/
lemma averageVector_succ {K : Type uK} (x : ℕ → K → ℝ) (n : ℕ) (k : K) :
    averageVector x (n + 1) k
      = ((n + 1 : ℝ) / (n + 2)) * averageVector x n k + (1 / (n + 2 : ℝ)) * x (n + 1) k := by
  unfold averageVector
  have hsum : ∑ t : Fin (n + 1 + 1), x t.val k
      = (∑ t : Fin (n + 1), x t.val k) + x (n + 1) k := by
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hsum]
  have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The running average up to stage `n`, scaled by `n + 1`, splits as the average up to an
earlier stage `m`, scaled by `m + 1`, plus the sum of the intervening samples. -/
lemma averageVector_sum_split {K : Type uK} (x : ℕ → K → ℝ) {m n : ℕ} (hmn : m ≤ n) (k : K) :
    (n + 1 : ℝ) * averageVector x n k
      = (m + 1 : ℝ) * averageVector x m k + ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k := by
  unfold averageVector
  have hn : ∑ t : Fin (n + 1), x t.val k = ∑ t ∈ Finset.range (n + 1), x t k :=
    Fin.sum_univ_eq_sum_range (fun t => x t k) (n + 1)
  have hm : ∑ t : Fin (m + 1), x t.val k = ∑ t ∈ Finset.range (m + 1), x t k :=
    Fin.sum_univ_eq_sum_range (fun t => x t k) (m + 1)
  rw [hn, hm, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun t => x t k) (Nat.zero_le (m + 1))
      (by omega : m + 1 ≤ n + 1)]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- If every sample is bounded by `B` in absolute value, so is the running average. -/
lemma abs_averageVector_le {K : Type uK} (x : ℕ → K → ℝ) {B : ℝ} {k : K}
    (hbound : ∀ t : ℕ, |x t k| ≤ B) (n : ℕ) : |averageVector x n k| ≤ B := by
  unfold averageVector
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℝ))⁻¹)]
  calc ((n + 1 : ℝ))⁻¹ * |∑ t : Fin (n + 1), x t.val k|
      ≤ ((n + 1 : ℝ))⁻¹ * ∑ t : Fin (n + 1), |x t.val k| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((n + 1 : ℝ))⁻¹ * ∑ _t : Fin (n + 1), B := by
        gcongr with t _
        exact hbound t.val
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp

/-- Coordinatewise control of how much the running average can move between an earlier
stage `m` and a later stage `n`, in terms of the uniform sample bound `B`. This is the
"checkpoint gap" estimate used to interpolate the a.s. convergence obtained at sparse
checkpoints to the full sequence. -/
lemma abs_averageVector_sub_le {K : Type uK} (x : ℕ → K → ℝ) {B : ℝ} {k : K}
    (hbound : ∀ t : ℕ, |x t k| ≤ B) {m n : ℕ} (hmn : m ≤ n) :
    |averageVector x n k - averageVector x m k| ≤ 2 * B * (n - m : ℝ) / (n + 1) := by
  have hsplit := averageVector_sum_split x hmn k
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgap : |∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k| ≤ (n - m : ℝ) * B := by
    calc |∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k|
        ≤ ∑ t ∈ Finset.Ico (m + 1) (n + 1), |x t k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.Ico (m + 1) (n + 1), B := Finset.sum_le_sum fun t _ => hbound t
      _ = (n - m : ℝ) * B := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          have : ((n + 1 - (m + 1) : ℕ) : ℝ) = (n : ℝ) - m := by
            have : n + 1 - (m + 1) = n - m := by omega
            rw [this]
            push_cast [Nat.cast_sub hmn]
            ring
          rw [this]
  have habsm : |averageVector x m k| ≤ B := abs_averageVector_le x hbound m
  have key : averageVector x n k - averageVector x m k
      = (- (n - m : ℝ) / (n + 1)) * averageVector x m k
        + (1 / (n + 1 : ℝ)) * ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k := by
    have hn1' : (n : ℝ) + 1 ≠ 0 := by positivity
    have hcast : ((m : ℝ) + 1) = ((n : ℝ) + 1) - (n - m : ℝ) := by ring
    field_simp
    nlinarith [hsplit, hcast]
  rw [key]
  calc |(- (n - m : ℝ) / (n + 1)) * averageVector x m k
        + (1 / (n + 1 : ℝ)) * ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k|
      ≤ |(- (n - m : ℝ) / (n + 1)) * averageVector x m k|
        + |(1 / (n + 1 : ℝ)) * ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t k| := abs_add_le _ _
    _ ≤ ((n - m : ℝ) / (n + 1)) * B + (1 / (n + 1 : ℝ)) * ((n - m : ℝ) * B) := by
        have hcast : (0:ℝ) ≤ (n - m : ℝ) := by
          have : (m:ℝ) ≤ n := by exact_mod_cast hmn
          linarith
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 / (n+1:ℝ))),
          abs_div, abs_neg, abs_of_nonneg hcast, abs_of_pos hn1]
        gcongr
    _ = 2 * B * (n - m : ℝ) / (n + 1) := by ring

/-- The orthant potential is "2-Lipschitz-squared": moving each coordinate by at most the
Euclidean gap `w` inflates the potential by at most a factor of two plus twice the squared
gap. This lets us interpolate a.s. bounds obtained at sparse checkpoints to every stage. -/
lemma posPart_sq_le_two_mul_add_two_mul_sq (a b : ℝ) :
    posPart a ^ 2 ≤ 2 * posPart b ^ 2 + 2 * (a - b) ^ 2 := by
  unfold posPart
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    nlinarith [sq_nonneg (max b 0), sq_nonneg (a - b)]
  · rw [max_eq_left ha]
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb]
      nlinarith [sq_nonneg (a - b), mul_nonneg (neg_nonneg.mpr hb) ha]
    · rw [max_eq_left hb]
      nlinarith [sq_nonneg (a - 2 * b)]

/-- The positive part shrinks absolute value. -/
lemma abs_posPart_le_abs (t : ℝ) : |posPart t| ≤ |t| := by
  unfold posPart
  rcases le_total t 0 with h | h
  · simp [max_eq_right h]
  · rw [max_eq_left h, abs_of_nonneg h]

/-- The projection to the nonpositive reals shrinks absolute value. -/
lemma abs_min_zero_le_abs (t : ℝ) : |min t 0| ≤ |t| := by
  rcases le_total t 0 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_zero]; exact abs_nonneg t

/-- The triangle inequality for subtraction. -/
lemma abs_sub_le_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

lemma orthantPotential_le_two_mul_add_two_mul_sq {K : Type uK} [Fintype K] (z w : K → ℝ) :
    orthantPotential z ≤ 2 * orthantPotential w + 2 * (∑ k : K, (z k - w k) ^ 2) := by
  unfold orthantPotential
  have hrw : 2 * (∑ k : K, posPart (w k) ^ 2) + 2 * (∑ k : K, (z k - w k) ^ 2)
      = ∑ k : K, (2 * posPart (w k) ^ 2 + 2 * (z k - w k) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hrw]
  exact Finset.sum_le_sum fun k _ => posPart_sq_le_two_mul_add_two_mul_sq (z k) (w k)

/-- One-step pathwise inequality for the squared distance to the nonpositive
orthant. The terms are the previous potential, the Blackwell inner product,
and a quadratic correction. -/
lemma orthantPotential_averageVector_succ_le {K : Type uK} [Fintype K] (x : ℕ → K → ℝ) (n : ℕ) :
    orthantPotential (averageVector x (n + 1))
      ≤ ((n + 1 : ℝ) / (n + 2)) ^ 2 * orthantPotential (averageVector x n)
        + 2 * ((n + 1 : ℝ) / (n + 2)) * (1 / (n + 2 : ℝ)) *
            (∑ k : K, vectorPosPart (averageVector x n) k *
              (x (n + 1) k - negativeOrthantProjection (averageVector x n) k))
        + (1 / (n + 2 : ℝ)) ^ 2 *
            (∑ k : K, (x (n + 1) k - negativeOrthantProjection (averageVector x n) k) ^ 2) := by
  have hα : ((n + 1 : ℝ) / (n + 2)) + (1 / (n + 2 : ℝ)) = 1 := by
    have : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have hpk : ∀ k : K, negativeOrthantProjection (averageVector x n) k ≤ 0 :=
    fun k => min_le_right (averageVector x n k) 0
  have hid : ∀ k : K, averageVector x n k - negativeOrthantProjection (averageVector x n) k
      = vectorPosPart (averageVector x n) k := by
    intro k
    unfold negativeOrthantProjection vectorPosPart posPart
    rcases le_total (averageVector x n k) 0 with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h]
  have heq : ∀ k : K, averageVector x (n + 1) k - negativeOrthantProjection (averageVector x n) k
      = ((n + 1 : ℝ) / (n + 2)) * vectorPosPart (averageVector x n) k
        + (1 / (n + 2 : ℝ)) * (x (n + 1) k - negativeOrthantProjection (averageVector x n) k) := by
    intro k
    rw [averageVector_succ]
    have hstep2 : ((n + 1 : ℝ) / (n + 2)) * (averageVector x n k
          - negativeOrthantProjection (averageVector x n) k)
        + (1 / (n + 2 : ℝ)) * (x (n + 1) k - negativeOrthantProjection (averageVector x n) k)
        = ((n + 1 : ℝ) / (n + 2)) * averageVector x n k + (1 / (n + 2 : ℝ)) * x (n + 1) k
          - negativeOrthantProjection (averageVector x n) k := by
      have h1 : (((n + 1 : ℝ) / (n + 2)) + (1 / (n + 2 : ℝ)))
            * negativeOrthantProjection (averageVector x n) k
          = negativeOrthantProjection (averageVector x n) k := by rw [hα]; ring
      nlinarith [h1]
    rw [← hstep2, hid]
  have hstep : ∀ k : K, posPart (averageVector x (n + 1) k) ^ 2 ≤
      (((n + 1 : ℝ) / (n + 2)) * vectorPosPart (averageVector x n) k
        + (1 / (n + 2 : ℝ)) * (x (n + 1) k
            - negativeOrthantProjection (averageVector x n) k)) ^ 2 := by
    intro k
    calc posPart (averageVector x (n + 1) k) ^ 2
        ≤ (averageVector x (n + 1) k - negativeOrthantProjection (averageVector x n) k) ^ 2 :=
          posPart_sq_le_sub_sq (hpk k)
      _ = (((n + 1 : ℝ) / (n + 2)) * vectorPosPart (averageVector x n) k
            + (1 / (n + 2 : ℝ)) * (x (n + 1) k
                - negativeOrthantProjection (averageVector x n) k)) ^ 2 := by rw [heq]
  calc orthantPotential (averageVector x (n + 1))
      = ∑ k : K, posPart (averageVector x (n + 1) k) ^ 2 := rfl
    _ ≤ ∑ k : K, (((n + 1 : ℝ) / (n + 2)) * vectorPosPart (averageVector x n) k
            + (1 / (n + 2 : ℝ)) * (x (n + 1) k
                - negativeOrthantProjection (averageVector x n) k)) ^ 2 :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = ((n + 1 : ℝ) / (n + 2)) ^ 2 * orthantPotential (averageVector x n)
          + 2 * ((n + 1 : ℝ) / (n + 2)) * (1 / (n + 2 : ℝ)) *
              (∑ k : K, vectorPosPart (averageVector x n) k *
                (x (n + 1) k - negativeOrthantProjection (averageVector x n) k))
          + (1 / (n + 2 : ℝ)) ^ 2 *
              (∑ k : K, (x (n + 1) k - negativeOrthantProjection (averageVector x n) k) ^ 2) := by
        simp only [orthantPotential, vectorPosPart]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- Expected external-regret vector under a mixed action `x`. -/
noncomputable def expectedExternalRegret {K : Type uK} [Fintype K]
    (x : stdSimplex ℝ K) (U : K → ℝ) : K → ℝ :=
  fun k => ∑ ℓ : K, x.val ℓ * externalRegretStage ℓ U k

/-- [MFoGT Lemma 7.3.3] The expected external-regret vector is orthogonal to the
mixed action used to generate it. -/
theorem expected_externalRegret_orthogonal {K : Type uK} [Fintype K]
    (x : stdSimplex ℝ K) (U : K → ℝ) :
    ∑ k : K, x.val k * expectedExternalRegret x U k = 0 := by
  have hsum : ∑ ℓ : K, x.val ℓ = 1 := x.property.2
  have h1 : ∑ k : K, ∑ ℓ : K, x.val k * (x.val ℓ * U k) = ∑ k : K, x.val k * U k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (∑ ℓ : K, x.val k * (x.val ℓ * U k)) = x.val k * U k * ∑ ℓ : K, x.val ℓ from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro ℓ _; ring, hsum, mul_one]
  have h2 : ∑ k : K, ∑ ℓ : K, x.val k * (x.val ℓ * U ℓ) = ∑ ℓ : K, x.val ℓ * U ℓ := by
    rw [show (∑ k : K, ∑ ℓ : K, x.val k * (x.val ℓ * U ℓ))
        = (∑ k : K, x.val k) * ∑ ℓ : K, x.val ℓ * U ℓ from by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum], hsum,
      one_mul]
  calc
    ∑ k : K, x.val k * expectedExternalRegret x U k
        = ∑ k : K, ∑ ℓ : K, x.val k * (x.val ℓ * U k)
            - ∑ k : K, ∑ ℓ : K, x.val k * (x.val ℓ * U ℓ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k _
          simp only [expectedExternalRegret, externalRegretStage]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ℓ _
          ring
    _ = ∑ k : K, x.val k * U k - ∑ ℓ : K, x.val ℓ * U ℓ := by rw [h1, h2]
    _ = 0 := sub_self _

/-! ### External-regret-matching rule from MFoGT Proposition 7.3.4 -/

/-- Positive-part regret-matching mixed action: proportional to the coordinatewise positive
part of `r`, falling back to the uniform distribution when the positive part vanishes
identically. This is the strategy `σ(h_n) ∝ R_n^+` from the proof of [MFoGT Proposition 7.3.4]. -/
noncomputable def regretMatchingAction {K : Type*} [Fintype K] [Nonempty K]
    (r : K → ℝ) : stdSimplex ℝ K :=
  if h : ∑ k : K, posPart (r k) = 0 then
    ⟨fun _ => (Fintype.card K : ℝ)⁻¹,
      fun _ => by positivity,
      by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hc : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        field_simp⟩
  else
    ⟨fun k => posPart (r k) / ∑ k' : K, posPart (r k'),
      fun k => div_nonneg (posPart_nonneg _) (Finset.sum_nonneg fun _ _ => posPart_nonneg _),
      by rw [← Finset.sum_div]; field_simp⟩

/-- `regretMatchingAction` only depends on the direction of `r`'s positive part: rescaling `r`
by a positive constant does not change the resulting mixed action. Used to identify the
strategy's raw-sum computation over a finite history with its computation on the corresponding
running average. -/
lemma regretMatchingAction_pos_smul {K : Type*} [Fintype K] [Nonempty K]
    {c : ℝ} (hc : 0 < c) (r : K → ℝ) :
    regretMatchingAction (fun k => c * r k) = regretMatchingAction r := by
  have hposPart : ∀ k : K, posPart (c * r k) = c * posPart (r k) := by
    intro k
    unfold posPart
    rcases le_total (r k) 0 with h | h
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc.le h), mul_zero]
    · rw [max_eq_left h, max_eq_left (mul_nonneg hc.le h)]
  unfold regretMatchingAction
  simp_rw [hposPart, ← Finset.mul_sum]
  by_cases hz : ∑ k : K, posPart (r k) = 0
  · rw [dif_pos (by rw [hz, mul_zero]), dif_pos hz]
  · rw [dif_neg (mul_ne_zero hc.ne' hz), dif_neg hz]
    congr 1
    funext k
    rw [mul_div_mul_left _ _ hc.ne']

/-- The regret-matching mixed action is orthogonal, pointwise, to the negative-orthant
projection: the coordinatewise identity `posPart r k * negativeOrthantProjection r k = 0`
underlying `⟨Π_D(r), r - Π_D(r)⟩ = 0` in the proof of [MFoGT Proposition 7.3.4]. -/
lemma vectorPosPart_mul_negativeOrthantProjection_eq_zero {K : Type*} [Fintype K]
    (r : K → ℝ) (k : K) : vectorPosPart r k * negativeOrthantProjection r k = 0 := by
  unfold vectorPosPart negativeOrthantProjection posPart
  rcases le_total (r k) 0 with h | h
  · rw [max_eq_right h, zero_mul]
  · rw [min_eq_right h, mul_zero]

/-- The regret-matching online strategy: at each stage, mix over actions proportionally to the
positive part of the total external regret accumulated so far, falling back to the uniform
distribution before any regret has accrued (in particular at the first stage). -/
noncomputable def externalRegretMatchingStrategy (K : Type uK) [Fintype K] [Nonempty K] :
    ExternalOnlineStrategy K :=
  fun n hist => regretMatchingAction
    (fun k => ∑ t : Fin n, externalRegretStage (hist.1 t) (hist.2 t) k)

/-- The regret-matching strategy's raw per-history computation coincides, up to the scale
invariance of `regretMatchingAction`, with `regretMatchingAction` applied to the running average
external regret over the corresponding realized play/payoff path. -/
lemma externalRegretMatchingStrategy_eq_regretMatchingAction_averageExternalRegret
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) :
    externalRegretMatchingStrategy K (n + 1)
        (fun t : Fin (n + 1) => play t.val, fun t : Fin (n + 1) => payoff t.val)
      = regretMatchingAction (fun k => averageExternalRegret play payoff n k) := by
  show regretMatchingAction
      (fun k => ∑ t : Fin (n + 1), externalRegretStage (play t.val) (payoff t.val) k)
    = regretMatchingAction (fun k => averageExternalRegret play payoff n k)
  have hc : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hrw : (fun k => ∑ t : Fin (n + 1), externalRegretStage (play t.val) (payoff t.val) k)
      = (fun k => (n + 1 : ℝ) * averageExternalRegret play payoff n k) := by
    funext k
    unfold averageExternalRegret
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [hrw]
  exact regretMatchingAction_pos_smul hc _

namespace NoRegretProbability

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω]

/-! ### Almost-sure lifting -/

/-- A vector-valued random average approaches the negative orthant almost
surely. -/
def ApproachesNegativeOrthantAE {K : Type uK}
    (P : MeasureTheory.Measure Ω) (xbar : ℕ → Ω → K → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ApproachesNegativeOrthant fun n => xbar n ω

/-- A bounded vector-valued process, almost surely and uniformly in time in each
coordinate. -/
def IsUniformlyBoundedVectorProcessAE {K : Type uK}
    (P : MeasureTheory.Measure Ω) (x : ℕ → Ω → K → ℝ) : Prop :=
  ∀ k : K, ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂P, ∀ n : ℕ, |x n ω k| ≤ B

/-! ### Conditional-expectation layer for approachability -/

/-- `y_{n+1}` is the conditional expectation of `x_{n+1}` given the `n`-stage
past filtration, coordinate by coordinate. -/
structure IsConditionalExpectationSequence {K : Type uK}
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (x y : ℕ → Ω → K → ℝ) : Prop where
  /-- Coordinate integrability of the process whose conditional expectation is
  being taken. -/
  integrable : ∀ n : ℕ, ∀ k : K, MeasureTheory.Integrable (fun ω => x n ω k) P
  /-- Conditional-expectation identity for the next-stage process. -/
  condExp :
    ∀ n : ℕ, ∀ k : K,
      (fun ω => y (n + 1) ω k) =ᵐ[P]
        MeasureTheory.condExp (ℱ n) P (fun ω => x (n + 1) ω k)

/-- The Blackwell one-step inequality holds almost surely. -/
noncomputable def BlackwellNegativeOrthantConditionAE {K : Type uK} [Fintype K]
    (P : MeasureTheory.Measure Ω) (x y : ℕ → Ω → K → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    BlackwellNegativeOrthantCondition
      (fun n => averageVector (fun m k => x m ω k) n)
      (fun n => y n ω)

/-! ### Measurability and boundedness infrastructure for the Blackwell argument -/

/-- Each coordinate of the running average is measurable with respect to the current stage
of the filtration, since it is a finite combination of adapted samples. -/
lemma measurable_averageVector {K : Type uK} [Fintype K] {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {x : ℕ → Ω → K → ℝ} (hadapted : MeasureTheory.Adapted ℱ x) (n : ℕ) (k : K) :
    Measurable[ℱ n] (fun ω => averageVector (fun m k' => x m ω k') n k) := by
  unfold averageVector
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum Finset.univ ?_
  intro t _
  have ht : t.val ≤ n := Nat.lt_succ_iff.mp t.isLt
  exact (measurable_pi_apply k).comp (hadapted.measurable_le ht)

/-- Strongly-measurable form of `measurable_averageVector`. -/
lemma stronglyMeasurable_averageVector {K : Type uK} [Fintype K]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x) (n : ℕ) (k : K) :
    StronglyMeasurable[ℱ n]
      (fun ω => averageVector (fun m k' => x m ω k') n k) :=
  (measurable_averageVector hadapted n k).stronglyMeasurable

/-- From a per-coordinate almost-sure uniform bound, extract a single almost-sure uniform
bound valid for every coordinate simultaneously (using finiteness of `K`). -/
lemma exists_uniform_bound_ae {K : Type uK} [Fintype K] {P : MeasureTheory.Measure Ω}
    {x : ℕ → Ω → K → ℝ} (hbounded : IsUniformlyBoundedVectorProcessAE P x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂P, ∀ k : K, ∀ n : ℕ, |x n ω k| ≤ B := by
  choose Bf hBf0 hBfae using hbounded
  refine ⟨∑ k : K, Bf k, Finset.sum_nonneg fun k _ => hBf0 k, ?_⟩
  have hBge : ∀ k : K, Bf k ≤ ∑ k' : K, Bf k' := fun k =>
    Finset.single_le_sum (fun k' _ => hBf0 k') (Finset.mem_univ k)
  have : ∀ k : K, ∀ᵐ ω ∂P, ∀ n : ℕ, |x n ω k| ≤ ∑ k' : K, Bf k' := by
    intro k
    filter_upwards [hBfae k] with ω hω n
    exact (hω n).trans (hBge k)
  exact (MeasureTheory.ae_all_iff).mpr this

/-- A strongly-measurable, uniformly bounded process is integrable on a probability space. -/
lemma integrable_of_stronglyMeasurable_abs_bound {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    {f : Ω → ℝ} (hm : m ≤ mΩ) (hf : StronglyMeasurable[m] f) {C : ℝ}
    (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) : MeasureTheory.Integrable f P := by
  apply MeasureTheory.Integrable.of_bound (hf.mono hm).aestronglyMeasurable C
  filter_upwards [hC] with ω hω
  rwa [Real.norm_eq_abs]

/-- Conditional-expectation form of the orthant-potential recursion. The
Blackwell condition makes the cross term nonpositive, leaving the correction
`β ^ 2 * (4 * B ^ 2 * |K|)`. -/
lemma condExp_orthantPotential_succ_le_ae {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    (MeasureTheory.condExp (ℱ n) P
      (fun ω => orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k)))
      ≤ᵐ[P]
      (fun ω => ((n + 1 : ℝ) / (n + 2)) ^ 2 *
          orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k)
        + (1 / (n + 2 : ℝ)) ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ))) := by
  have hle : ℱ n ≤ mΩ := ℱ.le n
  set xbarN : Ω → K → ℝ := fun ω => averageVector (fun m k' => x m ω k') n with hxbarN_def
  set u : Ω → K → ℝ := fun ω k => vectorPosPart (xbarN ω) k with hu_def
  set p : Ω → K → ℝ := fun ω k => negativeOrthantProjection (xbarN ω) k with hp_def
  set α : ℝ := (n + 1 : ℝ) / (n + 2) with hα_def
  set β : ℝ := 1 / (n + 2 : ℝ) with hβ_def
  have hcardK : (0:ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _

  have hmeasN : ∀ k, StronglyMeasurable[ℱ n] (fun ω => xbarN ω k) :=
    fun k => stronglyMeasurable_averageVector hadapted n k
  have hmeasU : ∀ k, StronglyMeasurable[ℱ n] (fun ω => u ω k) := fun k =>
    ((measurable_averageVector hadapted n k).max measurable_const).stronglyMeasurable
  have hmeasP : ∀ k, StronglyMeasurable[ℱ n] (fun ω => p ω k) := fun k =>
    ((measurable_averageVector hadapted n k).min measurable_const).stronglyMeasurable
  have hmeasV : StronglyMeasurable[ℱ n]
      (fun ω => orthantPotential (xbarN ω)) := by
    show StronglyMeasurable[ℱ n] (fun ω => ∑ k : K, posPart (xbarN ω k) ^ 2)
    exact Finset.stronglyMeasurable_fun_sum Finset.univ
      (fun k _ => (hmeasU k).pow 2)

  have hboundN : ∀ᵐ ω ∂P, ∀ k, |xbarN ω k| ≤ B := by
    filter_upwards [hBbound] with ω hω k
    exact abs_averageVector_le (fun m k' => x m ω k') (hω k) n
  have hboundU : ∀ᵐ ω ∂P, ∀ k, |u ω k| ≤ B := by
    filter_upwards [hboundN] with ω hω k
    exact (abs_posPart_le_abs (xbarN ω k)).trans (hω k)
  have hboundP : ∀ᵐ ω ∂P, ∀ k, |p ω k| ≤ B := by
    filter_upwards [hboundN] with ω hω k
    exact (abs_min_zero_le_abs (xbarN ω k)).trans (hω k)
  have hboundV : ∀ᵐ ω ∂P, |orthantPotential (xbarN ω)| ≤ (Fintype.card K : ℝ) * B ^ 2 := by
    filter_upwards [hboundN] with ω hω
    rw [abs_of_nonneg (orthantPotential_nonneg _)]
    show ∑ k : K, posPart (xbarN ω k) ^ 2 ≤ (Fintype.card K : ℝ) * B ^ 2
    calc ∑ k : K, posPart (xbarN ω k) ^ 2
        ≤ ∑ _k : K, B ^ 2 := Finset.sum_le_sum fun k _ => by
          have h1 := abs_posPart_le_abs (xbarN ω k)
          have h2 := hω k
          nlinarith [abs_nonneg (posPart (xbarN ω k)), sq_abs (posPart (xbarN ω k)), h1, h2]
      _ = (Fintype.card K : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

  have hintV : MeasureTheory.Integrable (fun ω => orthantPotential (xbarN ω)) P :=
    integrable_of_stronglyMeasurable_abs_bound hle hmeasV hboundV
  have hintXk : ∀ k : K, MeasureTheory.Integrable (fun ω => x (n + 1) ω k) P :=
    fun k => hcondExp.integrable (n + 1) k
  have hintU : ∀ k : K, MeasureTheory.Integrable (fun ω => u ω k) P := fun k =>
    integrable_of_stronglyMeasurable_abs_bound hle (hmeasU k)
      (hboundU.mono fun ω hω => hω k)
  have hintP : ∀ k : K, MeasureTheory.Integrable (fun ω => p ω k) P := fun k =>
    integrable_of_stronglyMeasurable_abs_bound hle (hmeasP k)
      (hboundP.mono fun ω hω => hω k)
  have hmeasX : ∀ k : K, StronglyMeasurable[mΩ] (fun ω => x (n + 1) ω k) := fun k =>
    ((measurable_pi_apply k).comp (hadapted.measurable (i := n + 1))).stronglyMeasurable
  have hboundX : ∀ᵐ ω ∂P, ∀ k, |x (n + 1) ω k| ≤ B := by
    filter_upwards [hBbound] with ω hω k
    exact hω k (n + 1)
  have hmeasU_top : ∀ k, StronglyMeasurable[mΩ] (fun ω => u ω k) := fun k => (hmeasU k).mono hle
  have hmeasP_top : ∀ k, StronglyMeasurable[mΩ] (fun ω => p ω k) := fun k => (hmeasP k).mono hle
  have hintDiff : ∀ k : K,
      MeasureTheory.Integrable (fun ω => x (n + 1) ω k - p ω k) P := fun k =>
    (hintXk k).sub (integrable_of_stronglyMeasurable_abs_bound hle (hmeasP k)
      (hboundP.mono fun ω hω => hω k))
  have hintCross : ∀ k : K,
      MeasureTheory.Integrable (fun ω => u ω k * (x (n + 1) ω k - p ω k)) P := by
    intro k
    apply integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ)
      ((hmeasU_top k).mul ((hmeasX k).sub (hmeasP_top k))) (C := B * (2 * B))
    filter_upwards [hboundU, hboundX, hboundP] with ω hωU hωX hωP
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [abs_mul]
    calc |u ω k| * |x (n + 1) ω k - p ω k|
        ≤ B * (|x (n + 1) ω k| + |p ω k|) := by
          gcongr
          · exact hωU k
          · exact abs_sub_le_add_abs _ _
      _ ≤ B * (B + B) := by gcongr; exacts [hωX k, hωP k]
      _ = B * (2 * B) := by ring
  have hintS : MeasureTheory.Integrable
      (fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k)) P :=
    MeasureTheory.integrable_finsetSum Finset.univ fun k _ => hintCross k
  have hintTk : ∀ k : K,
      MeasureTheory.Integrable (fun ω => (x (n + 1) ω k - p ω k) ^ 2) P := by
    intro k
    apply integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ)
      (((hmeasX k).sub (hmeasP_top k)).pow 2) (C := (2 * B) ^ 2)
    filter_upwards [hboundX, hboundP] with ω hωX hωP
    simp only [Pi.pow_apply, Pi.sub_apply]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hbd : |x (n + 1) ω k - p ω k| ≤ 2 * B := by
      calc |x (n + 1) ω k - p ω k| ≤ |x (n + 1) ω k| + |p ω k| := abs_sub_le_add_abs _ _
        _ ≤ B + B := by gcongr; exacts [hωX k, hωP k]
        _ = 2 * B := by ring
    calc (x (n + 1) ω k - p ω k) ^ 2 = |x (n + 1) ω k - p ω k| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * B) ^ 2 := by
          have h0 : (0:ℝ) ≤ |x (n + 1) ω k - p ω k| := abs_nonneg _
          nlinarith [hbd, h0]
  have hintT : MeasureTheory.Integrable
      (fun ω => ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2) P :=
    MeasureTheory.integrable_finsetSum Finset.univ fun k _ => hintTk k

  have hboundN1 : ∀ᵐ ω ∂P, ∀ k, |averageVector (fun m k' => x m ω k') (n + 1) k| ≤ B := by
    filter_upwards [hBbound] with ω hω k
    exact abs_averageVector_le (fun m k' => x m ω k') (hω k) (n + 1)
  have hmeasV1 : StronglyMeasurable[mΩ]
      (fun ω => orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k)) := by
    show StronglyMeasurable[mΩ]
      (fun ω => ∑ k : K, posPart (averageVector (fun m k' => x m ω k') (n + 1) k) ^ 2)
    refine Finset.stronglyMeasurable_fun_sum Finset.univ fun k _ => ?_
    exact (((measurable_averageVector hadapted (n + 1) k).mono
      (ℱ.le (n + 1)) le_rfl).stronglyMeasurable.sup
        (MeasureTheory.stronglyMeasurable_const : StronglyMeasurable[mΩ] (fun _ : Ω => (0:ℝ)))).pow 2
  have hboundV1 : ∀ᵐ ω ∂P,
      |orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k)|
        ≤ (Fintype.card K : ℝ) * B ^ 2 := by
    filter_upwards [hboundN1] with ω hω
    rw [abs_of_nonneg (orthantPotential_nonneg _)]
    unfold orthantPotential
    calc ∑ k : K, posPart (averageVector (fun m k' => x m ω k') (n + 1) k) ^ 2
        ≤ ∑ _k : K, B ^ 2 := Finset.sum_le_sum fun k _ => by
          nlinarith [abs_posPart_le_abs (averageVector (fun m k' => x m ω k') (n + 1) k),
            hω k, abs_nonneg (posPart (averageVector (fun m k' => x m ω k') (n + 1) k)),
            sq_abs (posPart (averageVector (fun m k' => x m ω k') (n + 1) k))]
      _ = (Fintype.card K : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hintV1 : MeasureTheory.Integrable
      (fun ω => orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k)) P :=
    integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) hmeasV1 hboundV1

  have hdet : ∀ ω : Ω,
      orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k)
        ≤ α ^ 2 * orthantPotential (xbarN ω)
          + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
          + β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2) := by
    intro ω
    exact orthantPotential_averageVector_succ_le (fun m k' => x m ω k') n
  have hintRHS : MeasureTheory.Integrable
      (fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
        + β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)) P :=
    ((hintV.const_mul (α ^ 2)).add (hintS.const_mul (2 * α * β))).add (hintT.const_mul (β ^ 2))
  have hstep1 := MeasureTheory.condExp_mono hintV1 hintRHS
    (Filter.Eventually.of_forall hdet) (m := ℱ n)

  have hcondV : MeasureTheory.condExp (ℱ n) P (fun ω => orthantPotential (xbarN ω))
      =ᵐ[P] fun ω => orthantPotential (xbarN ω) :=
    MeasureTheory.condExp_of_aestronglyMeasurable' hle hmeasV.aestronglyMeasurable hintV
  have hcondS_eq : MeasureTheory.condExp (ℱ n) P
      (fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
      =ᵐ[P] fun ω => ∑ k : K, u ω k * (y (n + 1) ω k - p ω k) := by
    have hfun_eq : (fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
        = ∑ k : K, (fun ω => u ω k * (x (n + 1) ω k - p ω k)) :=
      (Finset.sum_fn Finset.univ (fun k ω => u ω k * (x (n + 1) ω k - p ω k))).symm
    rw [hfun_eq]
    have hstep := MeasureTheory.condExp_finsetSum (μ := P) (s := Finset.univ)
      (f := fun k ω => u ω k * (x (n + 1) ω k - p ω k)) (fun k _ => hintCross k) (ℱ n)
    refine hstep.trans ?_
    have hterm : ∀ k : K,
        MeasureTheory.condExp (ℱ n) P (fun ω => u ω k * (x (n + 1) ω k - p ω k))
          =ᵐ[P] fun ω => u ω k * (y (n + 1) ω k - p ω k) := by
      intro k
      have hpullout := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (hmeasU k) (hintCross k)
        (hintDiff k) (m := ℱ n)
      refine hpullout.trans ?_
      have hsub : MeasureTheory.condExp (ℱ n) P (fun ω => x (n + 1) ω k - p ω k)
          =ᵐ[P] fun ω => y (n + 1) ω k - p ω k := by
        have := MeasureTheory.condExp_sub (hintXk k)
          (integrable_of_stronglyMeasurable_abs_bound hle (hmeasP k)
            (hboundP.mono fun ω hω => hω k)) (ℱ n)
        refine this.trans ?_
        have hpcond : MeasureTheory.condExp (ℱ n) P (fun ω => p ω k)
            =ᵐ[P] fun ω => p ω k :=
          MeasureTheory.condExp_of_aestronglyMeasurable' hle (hmeasP k).aestronglyMeasurable
            (integrable_of_stronglyMeasurable_abs_bound hle (hmeasP k)
              (hboundP.mono fun ω hω => hω k))
        filter_upwards [hcondExp.condExp n k, hpcond] with ω hω1 hω2
        simp only [Pi.sub_apply]
        rw [hω1, hω2]
      filter_upwards [hsub] with ω hω
      simp only [Pi.mul_apply]
      rw [hω]
    filter_upwards [Finset.univ.eventually_all.mpr fun k (_ : k ∈ Finset.univ) => hterm k] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => hω k (Finset.mem_univ k)
  have hcondS_le : MeasureTheory.condExp (ℱ n) P
      (fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k)) ≤ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hcondS_eq, hcond] with ω hω1 hω2
    rw [hω1]
    exact hω2 n
  have hcondT_le : MeasureTheory.condExp (ℱ n) P
      (fun ω => ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)
      ≤ᵐ[P] fun _ => (4 : ℝ) * B ^ 2 * (Fintype.card K : ℝ) := by
    have hTbound : (fun ω => ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)
        ≤ᵐ[P] fun _ => (4 : ℝ) * B ^ 2 * (Fintype.card K : ℝ) := by
      filter_upwards [hboundX, hboundP] with ω hωX hωP
      calc ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2
          ≤ ∑ _k : K, (2 * B) ^ 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            have hbd : |x (n + 1) ω k - p ω k| ≤ 2 * B := by
              calc |x (n + 1) ω k - p ω k| ≤ |x (n + 1) ω k| + |p ω k| :=
                    abs_sub_le_add_abs _ _
                _ ≤ B + B := by gcongr; exacts [hωX k, hωP k]
                _ = 2 * B := by ring
            calc (x (n + 1) ω k - p ω k) ^ 2 = |x (n + 1) ω k - p ω k| ^ 2 := (sq_abs _).symm
              _ ≤ (2 * B) ^ 2 := by nlinarith [hbd, abs_nonneg (x (n + 1) ω k - p ω k)]
        _ = (4 : ℝ) * B ^ 2 * (Fintype.card K : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have hmono := MeasureTheory.condExp_mono hintT (MeasureTheory.integrable_const _) hTbound
      (m := ℱ n)
    rwa [MeasureTheory.condExp_const hle] at hmono
  have hαβ_nonneg : (0:ℝ) ≤ 2 * α * β := by
    have hα0 : (0:ℝ) ≤ α := by rw [hα_def]; positivity
    have hβ0 : (0:ℝ) ≤ β := by rw [hβ_def]; positivity
    positivity
  have hβsq_nonneg : (0:ℝ) ≤ β ^ 2 := sq_nonneg _
  have hIntA : MeasureTheory.Integrable (fun ω => α ^ 2 * orthantPotential (xbarN ω)) P :=
    hintV.const_mul (α ^ 2)
  have hIntB : MeasureTheory.Integrable
      (fun ω => 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))) P :=
    hintS.const_mul (2 * α * β)
  have hIntC : MeasureTheory.Integrable
      (fun ω => β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)) P :=
    hintT.const_mul (β ^ 2)
  have hIntAB : MeasureTheory.Integrable
      (fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))) P :=
    hIntA.add hIntB
  have hcVmul : MeasureTheory.condExp (ℱ n) P (fun ω => α ^ 2 * orthantPotential (xbarN ω))
      =ᵐ[P] fun ω => α ^ 2 * orthantPotential (xbarN ω) :=
    MeasureTheory.condExp_of_aestronglyMeasurable' hle
      (hmeasV.const_mul (α ^ 2)).aestronglyMeasurable hIntA
  have hcSmul : MeasureTheory.condExp (ℱ n) P
      (fun ω => 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k)))
      ≤ᵐ[P] fun _ => (0 : ℝ) := by
    have hpull : MeasureTheory.condExp (ℱ n) P
        (fun ω => 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k)))
        =ᵐ[P] fun ω => 2 * α * β * MeasureTheory.condExp (ℱ n) P
          (fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k)) ω :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left (f := fun _ : Ω => 2 * α * β)
        (g := fun ω => ∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
        (MeasureTheory.stronglyMeasurable_const : StronglyMeasurable[ℱ n] (fun _ : Ω => 2 * α * β))
        hIntB hintS (m := ℱ n)
    filter_upwards [hpull, hcondS_le] with ω hω1 hω2
    rw [hω1]
    nlinarith [hαβ_nonneg, hω2]
  have hcTmul : MeasureTheory.condExp (ℱ n) P
      (fun ω => β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2))
      ≤ᵐ[P] fun _ => β ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ)) := by
    have hpull : MeasureTheory.condExp (ℱ n) P
        (fun ω => β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2))
        =ᵐ[P] fun ω => β ^ 2 * MeasureTheory.condExp (ℱ n) P
          (fun ω => ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2) ω :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left (f := fun _ : Ω => β ^ 2)
        (g := fun ω => ∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)
        (MeasureTheory.stronglyMeasurable_const : StronglyMeasurable[ℱ n] (fun _ : Ω => β ^ 2))
        hIntC hintT (m := ℱ n)
    filter_upwards [hpull, hcondT_le] with ω hω1 hω2
    rw [hω1]
    exact mul_le_mul_of_nonneg_left hω2 hβsq_nonneg
  have hadd : MeasureTheory.condExp (ℱ n) P
      (fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
        + β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2))
      =ᵐ[P] MeasureTheory.condExp (ℱ n) P
          (fun ω => α ^ 2 * orthantPotential (xbarN ω)
            + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k)))
        + MeasureTheory.condExp (ℱ n) P
            (fun ω => β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2)) :=
    MeasureTheory.condExp_add hIntAB hIntC (ℱ n)
  have hadd2 : MeasureTheory.condExp (ℱ n) P
      (fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k)))
      =ᵐ[P] MeasureTheory.condExp (ℱ n) P (fun ω => α ^ 2 * orthantPotential (xbarN ω))
        + MeasureTheory.condExp (ℱ n) P
            (fun ω => 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))) :=
    MeasureTheory.condExp_add hIntA hIntB (ℱ n)
  have hstep2 : MeasureTheory.condExp (ℱ n) P
      (fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + 2 * α * β * (∑ k : K, u ω k * (x (n + 1) ω k - p ω k))
        + β ^ 2 * (∑ k : K, (x (n + 1) ω k - p ω k) ^ 2))
      ≤ᵐ[P] fun ω => α ^ 2 * orthantPotential (xbarN ω)
        + β ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ)) := by
    filter_upwards [hadd, hadd2, hcVmul, hcSmul, hcTmul] with ω hω hω2 hω3 hω4 hω5
    simp only [Pi.add_apply] at hω hω2
    rw [hω, hω2]
    nlinarith [hω3, hω4, hω5]
  filter_upwards [hstep1, hstep2] with ω hω1 hω2
  exact hω1.trans hω2

lemma integrable_orthantPotential_averageVector {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    {B : ℝ} (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω => orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k)) P := by
  have hbound : ∀ᵐ ω ∂P, ∀ k, |averageVector (fun m k' => x m ω k') n k| ≤ B := by
    filter_upwards [hBbound] with ω hω k
    exact abs_averageVector_le (fun m k' => x m ω k') (hω k) n
  have hmeas : StronglyMeasurable[mΩ]
      (fun ω => orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k)) := by
    show StronglyMeasurable[mΩ]
      (fun ω => ∑ k : K, posPart (averageVector (fun m k' => x m ω k') n k) ^ 2)
    refine Finset.stronglyMeasurable_fun_sum Finset.univ fun k _ => ?_
    exact (((measurable_averageVector hadapted n k).mono
      (ℱ.le n) le_rfl).stronglyMeasurable.sup
        (MeasureTheory.stronglyMeasurable_const : StronglyMeasurable[mΩ] (fun _ : Ω => (0:ℝ)))).pow 2
  have hboundV : ∀ᵐ ω ∂P,
      |orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k)|
        ≤ (Fintype.card K : ℝ) * B ^ 2 := by
    filter_upwards [hbound] with ω hω
    rw [abs_of_nonneg (orthantPotential_nonneg _)]
    unfold orthantPotential
    calc ∑ k : K, posPart (averageVector (fun m k' => x m ω k') n k) ^ 2
        ≤ ∑ _k : K, B ^ 2 := Finset.sum_le_sum fun k _ => by
          nlinarith [abs_posPart_le_abs (averageVector (fun m k' => x m ω k') n k),
            hω k, abs_nonneg (posPart (averageVector (fun m k' => x m ω k') n k)),
            sq_abs (posPart (averageVector (fun m k' => x m ω k') n k))]
      _ = (Fintype.card K : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) hmeas hboundV

/-- Integral form of the one-step conditional-expectation recursion: taking expectations
throughout `condExp_orthantPotential_succ_le_ae` and using the tower property of conditional
expectation. -/
lemma integral_orthantPotential_succ_le {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k) ∂P
      ≤ ((n + 1 : ℝ) / (n + 2)) ^ 2 *
          ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
        + (1 / (n + 2 : ℝ)) ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ)) := by
  have hle : ℱ n ≤ mΩ := ℱ.le n
  have hcondIneq := condExp_orthantPotential_succ_le_ae hadapted hcondExp hcond hB0 hBbound n
  have hIntV1 := integrable_orthantPotential_averageVector hadapted hBbound (n + 1)
  have hIntVn := integrable_orthantPotential_averageVector hadapted hBbound n
  have hIntRHS : MeasureTheory.Integrable
      (fun ω => ((n + 1 : ℝ) / (n + 2)) ^ 2 *
          orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k)
        + (1 / (n + 2 : ℝ)) ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ))) P :=
    (hIntVn.const_mul _).add (MeasureTheory.integrable_const _)
  have hmono := MeasureTheory.integral_mono_ae MeasureTheory.integrable_condExp hIntRHS hcondIneq
  rwa [MeasureTheory.integral_condExp hle,
    MeasureTheory.integral_add (hIntVn.const_mul _) (MeasureTheory.integrable_const _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const,
    MeasureTheory.measureReal_def, MeasureTheory.measure_univ, ENNReal.toReal_one, one_smul]
      at hmono

/-- Scaled form of the one-step integral recursion, clearing denominators: `(n + 2) ^ 2` times
the expected potential at stage `n + 1` is controlled by `(n + 1) ^ 2` times the expected
potential at stage `n`, plus the fixed correction `4 * B ^ 2 * |K|`. This form is what drives
the induction giving `E_n = O (1 / n)`. -/
lemma sq_mul_integral_orthantPotential_succ_le {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    ((n + 2 : ℝ)) ^ 2 *
        ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k) ∂P
      ≤ ((n + 1 : ℝ)) ^ 2 *
          ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
        + 4 * B ^ 2 * (Fintype.card K : ℝ) := by
  have hstep := integral_orthantPotential_succ_le hadapted hcondExp hcond hB0 hBbound n
  have hn2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstep (sq_nonneg ((n : ℝ) + 2))
  have hcard : (0:ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  calc ((n + 2 : ℝ)) ^ 2 *
        ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') (n + 1) k) ∂P
      ≤ ((n + 2 : ℝ)) ^ 2 * (((n + 1 : ℝ) / (n + 2)) ^ 2 *
          ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
        + (1 / (n + 2 : ℝ)) ^ 2 * (4 * B ^ 2 * (Fintype.card K : ℝ))) := hmul
    _ = ((n + 1 : ℝ)) ^ 2 *
          ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
        + 4 * B ^ 2 * (Fintype.card K : ℝ) := by
        have hne : ((n : ℝ) + 2) ≠ 0 := hn2.ne'
        field_simp

/-- Induction on the one-step recursion: the running average's expected orthant potential,
scaled by `(n + 1) ^ 2`, grows by at most the fixed correction `4 * B ^ 2 * |K|` at every
stage. -/
lemma sq_mul_integral_orthantPotential_le {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    ((n + 1 : ℝ)) ^ 2 *
        ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
      ≤ (∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') 0 k) ∂P)
        + n * (4 * B ^ 2 * (Fintype.card K : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := sq_mul_integral_orthantPotential_succ_le hadapted hcondExp hcond hB0 hBbound n
    push_cast
    push_cast at ih
    nlinarith [hstep, ih]

/-- Final quantitative bound: the expected orthant potential of the running average decays like
`O (1 / n)`, with an explicit constant `C` given by the initial expected potential plus the
fixed correction `4 * B ^ 2 * |K|`. -/
lemma integral_orthantPotential_le_const_div {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B) (n : ℕ) :
    ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ∂P
      ≤ ((∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') 0 k) ∂P)
          + 4 * B ^ 2 * (Fintype.card K : ℝ)) / (n + 1) := by
  have hkey := sq_mul_integral_orthantPotential_le hadapted hcondExp hcond hB0 hBbound n
  have hE0 : (0:ℝ) ≤ ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') 0 k) ∂P :=
    MeasureTheory.integral_nonneg fun ω => orthantPotential_nonneg _
  have hcard : (0:ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hn1]
  nlinarith [hkey, hE0, hcard, sq_nonneg ((n:ℝ)+1), Nat.cast_nonneg (α := ℝ) n]

/-- Markov's inequality plus the first Borel–Cantelli lemma, applied along the sparse
checkpoints `n_l = (l + 1) ^ 2`: since `∑ l, P (V (n_l) ≥ ε)` is summable (comparison with the
convergent `p`-series `∑ l, 1 / (l + 1) ^ 2`), almost every `ω` eventually satisfies
`V (n_l) ω < ε`. -/
lemma ae_eventually_orthantPotential_checkpoint_lt {K : Type uK} [Fintype K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → K → ℝ}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y)
    {B : ℝ} (hB0 : 0 ≤ B) (hBbound : ∀ᵐ ω ∂P, ∀ k n, |x n ω k| ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ l in Filter.atTop,
      orthantPotential (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k) < ε := by
  set C : ℝ := (∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') 0 k) ∂P)
      + 4 * B ^ 2 * (Fintype.card K : ℝ) with hC_def
  have hCnonneg : 0 ≤ C := by
    have hE0 : (0:ℝ) ≤ ∫ ω, orthantPotential (fun k => averageVector (fun m k' => x m ω k') 0 k) ∂P :=
      MeasureTheory.integral_nonneg fun ω => orthantPotential_nonneg _
    have hcard : (0:ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
    rw [hC_def]; positivity
  have hPle : ∀ l : ℕ, P.real {ω | ε ≤ orthantPotential
      (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)}
      ≤ C / (ε * ((l : ℝ) + 1) ^ 2) := by
    intro l
    have hnonneg : 0 ≤ᵐ[P] (fun ω => orthantPotential
        (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)) :=
      Filter.Eventually.of_forall fun ω => orthantPotential_nonneg _
    have hint := integrable_orthantPotential_averageVector hadapted hBbound ((l + 1) ^ 2)
    have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint ε
    have hdecay := integral_orthantPotential_le_const_div hadapted hcondExp hcond hB0 hBbound
      ((l + 1) ^ 2)
    have hcombine : ε * P.real {ω | ε ≤ orthantPotential
        (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)}
        ≤ C / (((l : ℝ) + 1) ^ 2 + 1) := by
      refine hmarkov.trans ?_
      rw [hC_def]
      convert hdecay using 3
      push_cast
      ring
    have hstep : C / (((l : ℝ) + 1) ^ 2 + 1) ≤ C / ((l : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left hCnonneg (by positivity) (by linarith)
    have hle : ε * P.real {ω | ε ≤ orthantPotential
        (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)}
        ≤ C / ((l : ℝ) + 1) ^ 2 := hcombine.trans hstep
    rw [div_mul_eq_div_div_swap, le_div_iff₀ hε]
    linarith [hle]
  have hEle : ∀ l : ℕ, P {ω | ε ≤ orthantPotential
      (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)}
      ≤ ENNReal.ofReal (C / (ε * ((l : ℝ) + 1) ^ 2)) := by
    intro l
    have hne : P {ω | ε ≤ orthantPotential
        (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)} ≠ ⊤ :=
      MeasureTheory.measure_ne_top P _
    rw [← ENNReal.ofReal_toReal hne, ← MeasureTheory.measureReal_def]
    exact ENNReal.ofReal_le_ofReal (hPle l)
  have hsum2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hsumshift : Summable (fun l : ℕ => (((l : ℝ) + 1) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).mpr hsum2
    simpa using this
  have hsumfin : Summable (fun l : ℕ => C / (ε * ((l : ℝ) + 1) ^ 2)) := by
    have := hsumshift.mul_left (C / ε)
    convert this using 1
    ext l
    field_simp
  have hne_top : (∑' l : ℕ, P {ω | ε ≤ orthantPotential
      (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)}) ≠ ⊤ := by
    have hle_sum : (∑' l : ℕ, P {ω | ε ≤ orthantPotential
        (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)})
        ≤ ∑' l : ℕ, ENNReal.ofReal (C / (ε * ((l : ℝ) + 1) ^ 2)) :=
      ENNReal.tsum_le_tsum hEle
    refine ne_top_of_le_ne_top ?_ hle_sum
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) hsumfin]
    exact ENNReal.ofReal_ne_top
  have := MeasureTheory.ae_eventually_notMem hne_top
  filter_upwards [this] with ω hω
  filter_upwards [hω] with l hl
  exact not_le.mp hl

/-- Deterministic (pathwise) checkpoint-gap interpolation: the orthant potential at any stage
`n ≥ 1` is controlled by the potential at the largest perfect-square checkpoint `q ^ 2 ≤ n`
(where `q = Nat.sqrt n`), plus an explicit correction term that vanishes as `q → ∞`. This lets
almost-sure convergence obtained at the sparse checkpoints `q ^ 2` be transferred to the full
sequence. -/
lemma orthantPotential_checkpoint_gap_le {K : Type uK} [Fintype K] (x : ℕ → K → ℝ)
    {B : ℝ} (hB0 : 0 ≤ B) (hbound : ∀ k n, |x n k| ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    orthantPotential (averageVector x n)
      ≤ 2 * orthantPotential (averageVector x ((Nat.sqrt n) ^ 2))
        + 32 * (Fintype.card K : ℝ) * B ^ 2 / (Nat.sqrt n : ℝ) ^ 2 := by
  set q := Nat.sqrt n with hq_def
  have hq1 : 1 ≤ q := Nat.le_sqrt'.mpr (by simpa using hn)
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqRpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le zero_lt_one hqR1
  have hqle : q ^ 2 ≤ n := Nat.sqrt_le' n
  have hqlt : n < (q + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hexpand : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  rw [hexpand] at hqlt
  have hnle : n ≤ q ^ 2 + 2 * q := by omega
  have hnleR : (n:ℝ) ≤ (q:ℝ) ^ 2 + 2 * (q:ℝ) := by exact_mod_cast hnle
  have hgap : ∀ k : K,
      (averageVector x n k - averageVector x (q ^ 2) k) ^ 2
        ≤ (4 * B * (q:ℝ) / (n + 1)) ^ 2 := by
    intro k
    have h := abs_averageVector_sub_le x (B := B) (k := k) (fun t => hbound k t) hqle
    have hle4 : (2:ℝ) * B * ((n:ℝ) - (q:ℝ) ^ 2) / (n + 1) ≤ 4 * B * (q:ℝ) / (n + 1) := by
      have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
      rw [div_le_div_iff_of_pos_right hn1]
      nlinarith [hnleR, hB0]
    have habs_nonneg : (0:ℝ) ≤ 4 * B * (q:ℝ) / (n + 1) := by positivity
    have h' : |averageVector x n k - averageVector x (q ^ 2) k|
        ≤ 2 * B * ((n : ℝ) - (q : ℝ) ^ 2) / (n + 1) := by
      simpa using h
    have := h'.trans hle4
    calc (averageVector x n k - averageVector x (q ^ 2) k) ^ 2
        = |averageVector x n k - averageVector x (q ^ 2) k| ^ 2 := (sq_abs _).symm
      _ ≤ (4 * B * (q:ℝ) / (n + 1)) ^ 2 := by
          have habs_nonneg' := abs_nonneg (averageVector x n k - averageVector x (q ^ 2) k)
          nlinarith [this, habs_nonneg, habs_nonneg']
  have hqcard : (0:ℝ) ≤ (Fintype.card K : ℝ) := Nat.cast_nonneg _
  have hstep : orthantPotential (averageVector x n)
      ≤ 2 * orthantPotential (averageVector x (q ^ 2))
        + 2 * (∑ k : K, (4 * B * (q:ℝ) / (n + 1)) ^ 2) :=
    (orthantPotential_le_two_mul_add_two_mul_sq (averageVector x n) (averageVector x (q ^ 2))).trans
      (by
        have hsum_gap :
            (∑ k : K, (averageVector x n k - averageVector x (q ^ 2) k) ^ 2)
              ≤ ∑ _k : K, (4 * B * (q:ℝ) / (n + 1)) ^ 2 :=
          Finset.sum_le_sum fun k _ => hgap k
        nlinarith [hsum_gap])
  refine hstep.trans (by
    have hsum_eq : (∑ _k : K, (4 * B * (q:ℝ) / (n + 1)) ^ 2)
        = (Fintype.card K : ℝ) * (4 * B * (q:ℝ) / (n + 1)) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsum_eq]
    have hn1pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hcorrection : 2 * ((Fintype.card K : ℝ) * (4 * B * (q:ℝ) / (n + 1)) ^ 2)
        ≤ 32 * (Fintype.card K : ℝ) * B ^ 2 / (q:ℝ) ^ 2 := by
      have hqsq_pos : (0:ℝ) < (q:ℝ) ^ 2 := by positivity
      have hq_sq_le_n1 : (q : ℝ) ^ 2 ≤ (n : ℝ) + 1 := by
        have hqleR : (q : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hqle
        linarith
      have hratio_le_one : ((q : ℝ) ^ 2 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
        have hratio_nonneg : 0 ≤ (q : ℝ) ^ 2 / ((n : ℝ) + 1) := by positivity
        have hratio_le : (q : ℝ) ^ 2 / ((n : ℝ) + 1) ≤ 1 :=
          (div_le_one hn1pos).mpr hq_sq_le_n1
        nlinarith [hratio_nonneg, hratio_le]
      calc
        2 * ((Fintype.card K : ℝ) * (4 * B * (q:ℝ) / (n + 1)) ^ 2)
            = 32 * (Fintype.card K : ℝ) * B ^ 2 / (q:ℝ) ^ 2 *
                (((q : ℝ) ^ 2 / ((n : ℝ) + 1)) ^ 2) := by
              field_simp [ne_of_gt hqRpos, ne_of_gt hn1pos]
              ring
        _ ≤ 32 * (Fintype.card K : ℝ) * B ^ 2 / (q:ℝ) ^ 2 * 1 := by
              exact mul_le_mul_of_nonneg_left hratio_le_one (by positivity)
        _ = 32 * (Fintype.card K : ℝ) * B ^ 2 / (q:ℝ) ^ 2 := by ring
    linarith [hcorrection])

/-- Negative-orthant specialization of the almost-sure Blackwell criterion in
[MFoGT, Theorem 7.3.2]. The process is explicitly required to be adapted to
the filtration used for conditional expectations. The general closed-convex
version is `EconCSLib.Blackwell.blackwell_approach_closedConvex_ae`. -/
theorem blackwell_approach_negativeOrthant_ae {K : Type uK} [Fintype K]
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    [MeasureTheory.IsProbabilityMeasure P]
    (x y : ℕ → Ω → K → ℝ)
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hbounded : IsUniformlyBoundedVectorProcessAE P x)
    (hcondExp : IsConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellNegativeOrthantConditionAE P x y) :
    ApproachesNegativeOrthantAE P
      (fun n ω => averageVector (fun m k => x m ω k) n) := by
  obtain ⟨B, hB0, hBbound⟩ := exists_uniform_bound_ae hbounded
  have hcheck : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ l in Filter.atTop,
      orthantPotential (fun k => averageVector (fun m k' => x m ω k') ((l + 1) ^ 2) k)
        < 1 / (j + 1 : ℝ) :=
    MeasureTheory.ae_all_iff.mpr fun j =>
      ae_eventually_orthantPotential_checkpoint_lt hadapted hcondExp hcond hB0 hBbound
        (ε := 1 / (j + 1 : ℝ)) (by positivity)
  filter_upwards [hBbound, hcheck] with ω hωB hωcheck
  set M : ℝ := 32 * (Fintype.card K : ℝ) * B ^ 2 with hM_def
  have hMnonneg : 0 ≤ M := by rw [hM_def]; positivity
  have hDzero : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) ≤ ε := by
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_gt (4 / ε)
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hε4 : (4 : ℝ) < ((j : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp (by linarith)
    have hjbound : 1 / ((j : ℝ) + 1) < ε / 4 := by
      rw [div_lt_div_iff₀ hjpos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hε4]
    obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (hωcheck j)
    obtain ⟨Q2, hQ2⟩ := exists_nat_gt (2 * M / ε)
    have hQ2Rpos : (0 : ℝ) < (Q2 : ℝ) := lt_of_le_of_lt (by positivity) hQ2
    have hQ2pos : 0 < Q2 := by exact_mod_cast hQ2Rpos
    have hQ2nat : 1 ≤ Q2 := hQ2pos
    have hQ2R1 : (1 : ℝ) ≤ (Q2 : ℝ) := by exact_mod_cast hQ2nat
    have hQ2ε : (2 : ℝ) * M < (Q2 : ℝ) * ε := (div_lt_iff₀ hε).mp hQ2
    have hQ2half : M / (Q2 : ℝ) < ε / 2 := by
      rw [div_lt_div_iff₀ hQ2Rpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hQ2ε]
    set Q : ℕ := max (L + 1) Q2 with hQ_def
    have hQL : L + 1 ≤ Q := le_max_left _ _
    have hQQ2 : Q2 ≤ Q := le_max_right _ _
    have hQ1 : 1 ≤ Q := le_trans hQ2nat hQQ2
    refine ⟨Q ^ 2, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow 2 Q (by omega)) hn
    set q : ℕ := Nat.sqrt n with hq_def
    have hqQ : Q ≤ q := Nat.le_sqrt'.mpr hn
    have hqL : L + 1 ≤ q := le_trans hQL hqQ
    have hqQ2 : Q2 ≤ q := le_trans hQQ2 hqQ
    have hqR : (Q2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqQ2
    have hqRpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hQ2Rpos hqR
    have hqeq : q - 1 + 1 = q := by omega
    have hqle1 : L ≤ q - 1 := by omega
    have hDq2 : orthantPotential (fun k => averageVector (fun m k' => x m ω k') (q ^ 2) k)
        < 1 / ((j : ℝ) + 1) := by
      have := hL (q - 1) hqle1
      rwa [hqeq] at this
    have hDq2' : orthantPotential (fun k => averageVector (fun m k' => x m ω k') (q ^ 2) k)
        < ε / 4 := hDq2.trans hjbound
    have hsqle : (Q2 : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ hQ2Rpos.le hqR 2
    have hMq2 : M / (q : ℝ) ^ 2 ≤ M / (Q2 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hMnonneg (by positivity) hsqle
    have hQ2sq : M / (Q2 : ℝ) ^ 2 ≤ M / (Q2 : ℝ) :=
      div_le_div_of_nonneg_left hMnonneg hQ2Rpos (le_self_pow₀ hQ2R1 two_ne_zero)
    have hMbound : M / (q : ℝ) ^ 2 < ε / 2 := lt_of_le_of_lt (hMq2.trans hQ2sq) hQ2half
    have hgap := orthantPotential_checkpoint_gap_le (fun m k' => x m ω k') hB0 hωB hn1
    rw [← hq_def] at hgap
    rw [← hM_def] at hgap
    linarith [hgap, hDq2', hMbound]
  intro k ε hε
  obtain ⟨N, hN⟩ := hDzero (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hD := hN n hn
  have hposk : posPart (averageVector (fun m k' => x m ω k') n k) ^ 2
      ≤ orthantPotential (fun k => averageVector (fun m k' => x m ω k') n k) :=
    Finset.single_le_sum (fun k' _ => sq_nonneg (posPart (averageVector (fun m k'' => x m ω k'') n k')))
      (Finset.mem_univ k)
  have hsqle : posPart (averageVector (fun m k' => x m ω k') n k) ^ 2 ≤ ε ^ 2 :=
    hposk.trans hD
  have hroot := Real.sqrt_le_sqrt hsqle
  rwa [Real.sqrt_sq (posPart_nonneg _), Real.sqrt_sq hε.le] at hroot

/-! ### Randomized online strategies -/

/-- Indicator of the event that the realized action at stage `n` is `k`. -/
def actionIndicator {K : Type uK} [DecidableEq K]
    (play : ℕ → Ω → K) (n : ℕ) (k : K) : Ω → ℝ :=
  fun ω => if play n ω = k then 1 else 0

/-- The probability assigned by an external online strategy to action `k` after
the realized history before stage `n`. -/
def externalStrategyProbability {K : Type uK} [Fintype K]
    (σ : ExternalOnlineStrategy K) (play : ℕ → Ω → K)
    (payoff : ℕ → Ω → K → ℝ) (n : ℕ) (k : K) : Ω → ℝ :=
  fun ω =>
    (σ n (externalHistoryOf (fun t => play t ω) (fun t => payoff t ω) n)).val k

/-- The realized history before each stage is measurable with respect to the
filtration available at that stage. For actions, measurability is expressed via
the finitely many indicator events. -/
structure IsExternalHistoryAdapted {K : Type uK} [Fintype K] [DecidableEq K]
    (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (play : ℕ → Ω → K) (payoff : ℕ → Ω → K → ℝ) : Prop where
  /-- Past action indicators are measurable at the stage when they enter the
  strategy's history. -/
  playHistory :
    ∀ n : ℕ, ∀ t : Fin n, ∀ k : K,
      Measurable[ℱ n] (actionIndicator play t.val k)
  /-- Past payoff coordinates are measurable at the stage when they enter the
  strategy's history. -/
  payoffHistory :
    ∀ n : ℕ, ∀ t : Fin n, ∀ k : K,
      Measurable[ℱ n] (fun ω => payoff t.val ω k)

/-- A random play/payoff process is generated by an external online strategy if
the realized history is adapted, the strategy's prescribed mixed action is
measurable with respect to the current-stage information, and that prescribed
mixed action is the conditional law of the next realized action. -/
structure IsGeneratedByExternalStrategyAE {K : Type uK} [Fintype K] [DecidableEq K]
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (σ : ExternalOnlineStrategy K)
    (play : ℕ → Ω → K) (payoff : ℕ → Ω → K → ℝ) : Prop where
  /-- The realized finite history used by the strategy is nonanticipative. -/
  historyAdapted : IsExternalHistoryAdapted ℱ play payoff
  /-- The strategy's announced mixed action is measurable with respect to the
  current-stage information. This is stated explicitly because strategies may be
  arbitrary functions of real-valued payoff histories. -/
  strategyProbabilityMeasurable :
    ∀ n : ℕ, ∀ k : K,
      Measurable[ℱ n] (externalStrategyProbability σ play payoff n k)
  /-- Conditional probability identity for each action and stage. -/
  condProb :
    ∀ n : ℕ, ∀ k : K,
      externalStrategyProbability σ play payoff n k =ᵐ[P]
        MeasureTheory.condExp (ℱ n) P (actionIndicator play n k)
  /-- The payoff vector at stage `n` is measurable with respect to the
  pre-action information `ℱ n`. Thus the environment cannot react to the fresh
  randomization used for the stage-`n` action. The filtration may contain more
  information than the explicit history passed to `σ`; this field does not
  claim those two information sets are equal. -/
  payoffPredictable : ∀ n : ℕ, ∀ k : K, Measurable[ℱ n] (fun ω => payoff n ω k)

/-- A payoff process is bounded almost surely. -/
def IsBoundedPayoffProcessAE {K : Type uK}
    (P : MeasureTheory.Measure Ω) (payoff : ℕ → Ω → K → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsBoundedPayoffProcess fun n => payoff n ω

/-- No external regret almost surely. -/
def HasNoExternalRegretAE {K : Type uK}
    (P : MeasureTheory.Measure Ω)
    (play : ℕ → Ω → K) (payoff : ℕ → Ω → K → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    HasNoExternalRegret (fun n => play n ω) (fun n => payoff n ω)

/-- A strategy has robust no external regret if every bounded predictable
process with the prescribed conditional action law has no external regret
almost surely. This predicate does not assert existence of such a process. -/
def HasNoExternalRegretOnGeneratedProcessesAE
    {K : Type uK} [Fintype K] [DecidableEq K]
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (σ : ExternalOnlineStrategy K) : Prop :=
  ∀ play payoff,
    IsGeneratedByExternalStrategyAE P ℱ σ play payoff →
    IsBoundedPayoffProcessAE P payoff →
    HasNoExternalRegretAE P play payoff

/-! ### Shared machinery for the generated-process regret-matching proofs -/

omit mΩ in
/-- Summing `g k ω` weighted by the indicator that action `k` was realized at stage `n`
collapses to the value of `g` at the realized action. -/
lemma sum_mul_actionIndicator_eq_apply {K : Type uK} [Fintype K] [DecidableEq K]
    (play : ℕ → Ω → K) (n : ℕ) (g : K → Ω → ℝ) (ω : Ω) :
    ∑ k : K, g k ω * actionIndicator play n k ω = g (play n ω) ω := by
  have hrw : ∑ k : K, g k ω * actionIndicator play n k ω
      = ∑ k : K, if play n ω = k then g k ω else 0 :=
    Finset.sum_congr rfl fun k _ => by unfold actionIndicator; split <;> ring
  rw [hrw]
  exact Fintype.sum_ite_eq (play n ω) (fun k => g k ω)

/-- Conditional expectation replaces the next-action indicator by its
announced conditional probability when the remaining factor is measurable and
bounded. This is the common probabilistic step in [MFoGT, Propositions 7.3.4
and 7.3.7]. -/
lemma condExp_sum_mul_actionIndicator
    {K : Type uK} [Fintype K] [DecidableEq K]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {σ : ExternalOnlineStrategy K}
    {play : ℕ → Ω → K} {payoff : ℕ → Ω → K → ℝ}
    (hgen : IsGeneratedByExternalStrategyAE P ℱ σ play payoff)
    (n : ℕ) (f : K → Ω → ℝ) (C : ℝ)
    (hf_meas : ∀ k : K, StronglyMeasurable[ℱ (n + 1)] (f k))
    (hf_bound : ∀ k : K, ∀ᵐ ω ∂P, |f k ω| ≤ C) :
    MeasureTheory.condExp (ℱ (n + 1)) P
        (fun ω => ∑ k : K, f k ω * actionIndicator play (n + 1) k ω)
      =ᵐ[P] fun ω => ∑ k : K, f k ω * externalStrategyProbability σ play payoff (n + 1) k ω := by
  have hf_int : ∀ k : K, MeasureTheory.Integrable (f k) P :=
    fun k => integrable_of_stronglyMeasurable_abs_bound (ℱ.le (n + 1)) (hf_meas k) (hf_bound k)
  have hind_meas : ∀ k : K, StronglyMeasurable[mΩ] (actionIndicator play (n + 1) k) := fun k =>
    ((hgen.historyAdapted.playHistory (n + 2) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ k).mono
      (ℱ.le (n + 2)) le_rfl).stronglyMeasurable
  have hind_bound : ∀ k : K, ∀ᵐ _ω ∂P, |actionIndicator play (n + 1) k _ω| ≤ 1 := by
    intro k; filter_upwards with ω; unfold actionIndicator; split <;> norm_num
  have hind_int : ∀ k : K, MeasureTheory.Integrable (actionIndicator play (n + 1) k) P :=
    fun k => integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) (hind_meas k) (hind_bound k)
  have hcross_meas : ∀ k : K,
      StronglyMeasurable[mΩ] (fun ω => f k ω * actionIndicator play (n + 1) k ω) :=
    fun k => ((hf_meas k).mono (ℱ.le (n + 1))).mul (hind_meas k)
  have hcross_bound : ∀ k : K,
      ∀ᵐ ω ∂P, |f k ω * actionIndicator play (n + 1) k ω| ≤ max C 0 := by
    intro k
    filter_upwards [hf_bound k] with ω hω
    rw [abs_mul]
    have hind_le : |actionIndicator play (n + 1) k ω| ≤ 1 := by
      unfold actionIndicator; split <;> norm_num
    calc |f k ω| * |actionIndicator play (n + 1) k ω|
        ≤ max C 0 * 1 := mul_le_mul (hω.trans (le_max_left _ _)) hind_le (abs_nonneg _)
          (le_max_right _ _)
      _ = max C 0 := by ring
  have hcross_int : ∀ k : K,
      MeasureTheory.Integrable (fun ω => f k ω * actionIndicator play (n + 1) k ω) P :=
    fun k => integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) (hcross_meas k)
      (hcross_bound k)
  have hpullout : ∀ k : K,
      MeasureTheory.condExp (ℱ (n + 1)) P (fun ω => f k ω * actionIndicator play (n + 1) k ω)
        =ᵐ[P] fun ω => f k ω * externalStrategyProbability σ play payoff (n + 1) k ω := by
    intro k
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (hf_meas k)
      (hcross_int k) (hind_int k) (m := ℱ (n + 1))
    refine hpull.trans ?_
    filter_upwards [(hgen.condProb (n + 1) k).symm] with ω hω
    simp only [Pi.mul_apply] at hω ⊢
    rw [hω]
  have hfun_eq : (fun ω => ∑ k : K, f k ω * actionIndicator play (n + 1) k ω)
      = ∑ k : K, (fun ω => f k ω * actionIndicator play (n + 1) k ω) :=
    (Finset.sum_fn Finset.univ (fun k ω => f k ω * actionIndicator play (n + 1) k ω)).symm
  rw [hfun_eq]
  have hstep := MeasureTheory.condExp_finsetSum (μ := P) (s := Finset.univ)
    (f := fun k ω => f k ω * actionIndicator play (n + 1) k ω)
    (fun k _ => hcross_int k) (ℱ (n + 1))
  refine hstep.trans ?_
  filter_upwards [Finset.univ.eventually_all.mpr fun k (_ : k ∈ Finset.univ) => hpullout k]
    with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => hω k (Finset.mem_univ k)

/-! ### Generated-process no-external-regret theorem: MFoGT Proposition 7.3.4 -/

/-- Conditional process form of [MFoGT, Proposition 7.3.4]. Every bounded
predictable process generated by the rule `σ(hₙ) ∝ Rₙ⁺` has no external regret
almost surely. -/
theorem externalRegretMatchingStrategy_hasNoExternalRegretOnGeneratedProcessesAE
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ) :
    HasNoExternalRegretOnGeneratedProcessesAE P ℱ
      (externalRegretMatchingStrategy K) := by
  intro play payoff hgen hbdd
  set σ : ExternalOnlineStrategy K := externalRegretMatchingStrategy K with hσ_def
  set 𝒢 : MeasureTheory.Filtration ℕ mΩ :=
    { seq := fun n => ℱ (n + 1)
      mono' := fun n m hnm => ℱ.mono (by omega)
      le' := fun n => ℱ.le (n + 1) } with h𝒢_def
  set x : ℕ → Ω → K → ℝ := fun n ω k => externalRegretStage (play n ω) (payoff n ω) k with hx_def
  set y : ℕ → Ω → K → ℝ := fun n ω k =>
    ∑ ℓ : K, externalStrategyProbability σ play payoff n ℓ ω *
      externalRegretStage ℓ (payoff n ω) k with hy_def
  have hpayoff_pred : ∀ n : ℕ, ∀ k : K, Measurable[ℱ n] (fun ω => payoff n ω k) :=
    hgen.payoffPredictable
  have hpayoff_pred' : ∀ n : ℕ, ∀ k : K, Measurable[ℱ (n + 1)] (fun ω => payoff n ω k) :=
    fun n k => (hpayoff_pred n k).mono (ℱ.mono (Nat.le_succ n)) le_rfl
  have hplay_ind_meas : ∀ n : ℕ, ∀ ℓ : K, Measurable[ℱ (n + 1)] (actionIndicator play n ℓ) :=
    fun n ℓ => hgen.historyAdapted.playHistory (n + 1) ⟨n, Nat.lt_succ_self n⟩ ℓ
  have hplayed_meas : ∀ n : ℕ, Measurable[ℱ (n + 1)] (fun ω => payoff n ω (play n ω)) := by
    intro n
    have heq : (fun ω => payoff n ω (play n ω))
        = fun ω => ∑ ℓ : K, actionIndicator play n ℓ ω * payoff n ω ℓ := by
      funext ω
      rw [show (∑ ℓ : K, actionIndicator play n ℓ ω * payoff n ω ℓ)
          = ∑ ℓ : K, if play n ω = ℓ then payoff n ω ℓ else 0 from
          Finset.sum_congr rfl fun ℓ _ => by unfold actionIndicator; split <;> ring]
      exact (Fintype.sum_ite_eq (play n ω) (fun ℓ => payoff n ω ℓ)).symm
    rw [heq]
    exact Finset.measurable_sum Finset.univ
      (fun ℓ _ => (hplay_ind_meas n ℓ).mul (hpayoff_pred' n ℓ))
  have hadapted : MeasureTheory.Adapted 𝒢 x := by
    intro n
    show Measurable[ℱ (n + 1)] (fun ω k => payoff n ω k - payoff n ω (play n ω))
    letI : MeasurableSpace Ω := ℱ (n + 1)
    exact measurable_pi_lambda _ (fun k => (hpayoff_pred' n k).sub (hplayed_meas n))
  have hbounded : IsUniformlyBoundedVectorProcessAE P x := by
    intro k
    refine ⟨2, by norm_num, ?_⟩
    filter_upwards [hbdd] with ω hω n
    show |payoff n ω k - payoff n ω (play n ω)| ≤ 2
    rw [abs_le]
    constructor <;> [linarith [(hω n k).1, (hω n (play n ω)).2];
      linarith [(hω n k).2, (hω n (play n ω)).1]]
  have hcondExp : IsConditionalExpectationSequence P 𝒢 x y := by
    constructor
    · intro n k
      have hmeas : StronglyMeasurable[mΩ] (fun ω => x n ω k) :=
        (((measurable_pi_apply k).comp (hadapted n)).stronglyMeasurable).mono (𝒢.le n)
      have hbound : ∀ᵐ ω ∂P, |x n ω k| ≤ 2 := by
        filter_upwards [hbdd] with ω hω
        show |payoff n ω k - payoff n ω (play n ω)| ≤ 2
        rw [abs_le]
        constructor <;> [linarith [(hω n k).1, (hω n (play n ω)).2];
          linarith [(hω n k).2, (hω n (play n ω)).1]]
      exact integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) hmeas hbound
    · intro n k
      show (fun ω => y (n + 1) ω k)
          =ᵐ[P] MeasureTheory.condExp (ℱ (n + 1)) P (fun ω => x (n + 1) ω k)
      have hpayoffℓ_meas : ∀ ℓ : K, StronglyMeasurable[ℱ (n + 1)] (fun ω => payoff (n + 1) ω ℓ) :=
        fun ℓ => (hpayoff_pred (n + 1) ℓ).stronglyMeasurable
      have hpayoffℓ_bound : ∀ ℓ : K, ∀ᵐ ω ∂P, |payoff (n + 1) ω ℓ| ≤ 1 := by
        intro ℓ
        filter_upwards [hbdd] with ω hω
        rw [abs_le]
        exact ⟨(hω (n + 1) ℓ).1, (hω (n + 1) ℓ).2⟩
      have hpayoffℓ_int : ∀ ℓ : K, MeasureTheory.Integrable (fun ω => payoff (n + 1) ω ℓ) P :=
        fun ℓ => integrable_of_stronglyMeasurable_abs_bound (ℱ.le (n + 1))
          (hpayoffℓ_meas ℓ) (hpayoffℓ_bound ℓ)
      have hind_meas : ∀ ℓ : K, StronglyMeasurable[mΩ] (actionIndicator play (n + 1) ℓ) :=
        fun ℓ => ((hplay_ind_meas (n + 1) ℓ).mono (ℱ.le (n + 2)) le_rfl).stronglyMeasurable
      have hind_bound : ∀ ℓ : K, ∀ᵐ _ω ∂P, |actionIndicator play (n + 1) ℓ _ω| ≤ 1 := by
        intro ℓ
        filter_upwards with ω
        unfold actionIndicator
        split <;> norm_num
      have hind_int : ∀ ℓ : K, MeasureTheory.Integrable (actionIndicator play (n + 1) ℓ) P :=
        fun ℓ => integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ)
          (hind_meas ℓ) (hind_bound ℓ)
      have hcross_meas : ∀ ℓ : K,
          StronglyMeasurable[mΩ]
            (fun ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω) :=
        fun ℓ => ((hpayoffℓ_meas ℓ).mono (ℱ.le (n + 1))).mul (hind_meas ℓ)
      have hcross_bound : ∀ ℓ : K,
          ∀ᵐ ω ∂P, |payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω| ≤ 1 := by
        intro ℓ
        filter_upwards [hpayoffℓ_bound ℓ] with ω hω
        rw [abs_mul]
        have hind_le : |actionIndicator play (n + 1) ℓ ω| ≤ 1 := by
          unfold actionIndicator; split <;> norm_num
        calc |payoff (n + 1) ω ℓ| * |actionIndicator play (n + 1) ℓ ω|
            ≤ 1 * 1 := mul_le_mul hω hind_le (abs_nonneg _) (by norm_num)
          _ = 1 := by ring
      have hcross_int : ∀ ℓ : K,
          MeasureTheory.Integrable
            (fun ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω) P :=
        fun ℓ => integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ)
          (hcross_meas ℓ) (hcross_bound ℓ)
      have hpullout : ∀ ℓ : K,
          MeasureTheory.condExp (ℱ (n + 1)) P
              (fun ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)
            =ᵐ[P] fun ω => payoff (n + 1) ω ℓ *
              externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
        intro ℓ
        have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (hpayoffℓ_meas ℓ)
          (hcross_int ℓ) (hind_int ℓ) (m := ℱ (n + 1))
        refine hpull.trans ?_
        filter_upwards [(hgen.condProb (n + 1) ℓ).symm] with ω hω
        simp only [Pi.mul_apply] at hω ⊢
        rw [hω]
      have hfun_eq : (fun ω => ∑ ℓ : K, payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)
          = ∑ ℓ : K, (fun ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω) :=
        (Finset.sum_fn Finset.univ
          (fun ℓ ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)).symm
      have hsum_cond : MeasureTheory.condExp (ℱ (n + 1)) P
          (fun ω => ∑ ℓ : K, payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)
            =ᵐ[P] fun ω => ∑ ℓ : K,
              payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
        rw [hfun_eq]
        have hstep := MeasureTheory.condExp_finsetSum (μ := P) (s := Finset.univ)
          (f := fun ℓ ω => payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)
          (fun ℓ _ => hcross_int ℓ) (ℱ (n + 1))
        refine hstep.trans ?_
        filter_upwards [Finset.univ.eventually_all.mpr
          fun ℓ (_ : ℓ ∈ Finset.univ) => hpullout ℓ] with ω hω
        simp only [Finset.sum_apply]
        exact Finset.sum_congr rfl fun ℓ _ => hω ℓ (Finset.mem_univ ℓ)
      have hplayed_cond : MeasureTheory.condExp (ℱ (n + 1)) P
          (fun ω => payoff (n + 1) ω (play (n + 1) ω))
            =ᵐ[P] fun ω => ∑ ℓ : K,
              payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
        have heq : (fun ω => payoff (n + 1) ω (play (n + 1) ω))
            = fun ω => ∑ ℓ : K, payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω := by
          funext ω
          rw [show (∑ ℓ : K, payoff (n + 1) ω ℓ * actionIndicator play (n + 1) ℓ ω)
              = ∑ ℓ : K, if play (n + 1) ω = ℓ then payoff (n + 1) ω ℓ else 0 from
              Finset.sum_congr rfl fun ℓ _ => by unfold actionIndicator; split <;> ring]
          exact (Fintype.sum_ite_eq (play (n + 1) ω) (fun ℓ => payoff (n + 1) ω ℓ)).symm
        rw [heq]
        exact hsum_cond
      have hplayed_bound : ∀ᵐ ω ∂P, |payoff (n + 1) ω (play (n + 1) ω)| ≤ 1 := by
        filter_upwards [hbdd] with ω hω
        rw [abs_le]
        exact ⟨(hω (n + 1) (play (n + 1) ω)).1, (hω (n + 1) (play (n + 1) ω)).2⟩
      have hplayed_int : MeasureTheory.Integrable
          (fun ω => payoff (n + 1) ω (play (n + 1) ω)) P :=
        integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ)
          (((hplayed_meas (n + 1)).mono (ℱ.le (n + 2)) le_rfl).stronglyMeasurable)
          hplayed_bound
      have hpayoffk_cond : MeasureTheory.condExp (ℱ (n + 1)) P
          (fun ω => payoff (n + 1) ω k) =ᵐ[P] fun ω => payoff (n + 1) ω k :=
        MeasureTheory.condExp_of_aestronglyMeasurable' (ℱ.le (n + 1))
          (hpayoffℓ_meas k).aestronglyMeasurable (hpayoffℓ_int k)
      have hsub_cond : MeasureTheory.condExp (ℱ (n + 1)) P (fun ω => x (n + 1) ω k)
          =ᵐ[P] fun ω => payoff (n + 1) ω k -
            ∑ ℓ : K, payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
        have hsub := MeasureTheory.condExp_sub (hpayoffℓ_int k) hplayed_int (ℱ (n + 1))
        refine hsub.trans ?_
        filter_upwards [hpayoffk_cond, hplayed_cond] with ω hω1 hω2
        simp only [Pi.sub_apply]
        rw [hω1, hω2]
      have hy_eq : ∀ ω : Ω, y (n + 1) ω k
          = payoff (n + 1) ω k -
            ∑ ℓ : K, payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
        intro ω
        show (∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω *
            externalRegretStage ℓ (payoff (n + 1) ω) k) = _
        unfold externalRegretStage
        have hsum1 : ∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω = 1 :=
          (σ (n + 1) (externalHistoryOf (fun t => play t ω)
            (fun t => payoff t ω) (n + 1))).property.2
        calc (∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω *
              (payoff (n + 1) ω k - payoff (n + 1) ω ℓ))
            = (∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω) *
                payoff (n + 1) ω k
              - ∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω *
                payoff (n + 1) ω ℓ := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun ℓ _ => by ring
          _ = payoff (n + 1) ω k -
              ∑ ℓ : K, payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω := by
              rw [hsum1, one_mul]
              congr 1
              exact Finset.sum_congr rfl fun ℓ _ => by ring
      have hy_eq_fun : (fun ω => y (n + 1) ω k)
          = fun ω => payoff (n + 1) ω k -
            ∑ ℓ : K, payoff (n + 1) ω ℓ * externalStrategyProbability σ play payoff (n + 1) ℓ ω :=
        funext hy_eq
      rw [hy_eq_fun]
      exact hsub_cond.symm
  have hblackwell : BlackwellNegativeOrthantConditionAE P x y := by
    filter_upwards with ω
    intro n
    set r : K → ℝ := averageVector (fun m k => x m ω k) n with hr_def
    show ∑ k : K, vectorPosPart r k * (y (n + 1) ω k - negativeOrthantProjection r k) ≤ 0
    have hσeq : σ (n + 1) (externalHistoryOf (fun t => play t ω) (fun t => payoff t ω) (n + 1))
        = regretMatchingAction r := by
      show externalRegretMatchingStrategy K (n + 1)
          (fun t : Fin (n + 1) => play t.val ω, fun t : Fin (n + 1) => payoff t.val ω)
        = regretMatchingAction r
      exact externalRegretMatchingStrategy_eq_regretMatchingAction_averageExternalRegret
        (fun m => play m ω) (fun m => payoff m ω) n
    have hyeq' : ∀ k : K, y (n + 1) ω k
        = expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k := by
      intro k
      show (∑ ℓ : K, externalStrategyProbability σ play payoff (n + 1) ℓ ω *
          externalRegretStage ℓ (payoff (n + 1) ω) k)
        = expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k
      unfold expectedExternalRegret
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      congr 2
      show (σ (n + 1) (externalHistoryOf (fun t => play t ω)
          (fun t => payoff t ω) (n + 1))).val ℓ = (regretMatchingAction r).val ℓ
      rw [hσeq]
    have horth := expected_externalRegret_orthogonal (regretMatchingAction r) (payoff (n + 1) ω)
    by_cases hz : ∑ k : K, posPart (r k) = 0
    · have hvp0 : ∀ k : K, vectorPosPart r k = 0 := fun k =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => posPart_nonneg (r k))).mp hz k
          (Finset.mem_univ k)
      have hzero : ∑ k : K, vectorPosPart r k * (y (n + 1) ω k - negativeOrthantProjection r k)
          = 0 := Finset.sum_eq_zero fun k _ => by rw [hvp0 k]; ring
      linarith [hzero]
    · have hCpos : (0 : ℝ) < ∑ k : K, posPart (r k) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => posPart_nonneg _) (Ne.symm hz)
      have hval : ∀ k : K, (regretMatchingAction r).val k
          = vectorPosPart r k / ∑ k' : K, posPart (r k') := by
        intro k
        show (regretMatchingAction r).val k = _
        unfold regretMatchingAction
        rw [dif_neg hz]
        rfl
      have h1 := horth
      rw [show (∑ k : K, (regretMatchingAction r).val k *
            expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k)
          = (∑ k : K, vectorPosPart r k *
              expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k)
            / (∑ k' : K, posPart (r k')) from by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by rw [hval k]; ring] at h1
      have hCne : (∑ k' : K, posPart (r k') : ℝ) ≠ 0 := hCpos.ne'
      have h2 : ∑ k : K, vectorPosPart r k *
          expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k = 0 :=
        (div_eq_zero_iff.mp h1).resolve_right hCne
      have hkey : ∑ k : K, vectorPosPart r k * y (n + 1) ω k = 0 := by
        calc ∑ k : K, vectorPosPart r k * y (n + 1) ω k
            = ∑ k : K, vectorPosPart r k *
                expectedExternalRegret (regretMatchingAction r) (payoff (n + 1) ω) k :=
              Finset.sum_congr rfl fun k _ => by rw [hyeq' k]
          _ = 0 := h2
      have hkey2 : ∑ k : K, vectorPosPart r k * negativeOrthantProjection r k = 0 :=
        Finset.sum_eq_zero fun k _ => vectorPosPart_mul_negativeOrthantProjection_eq_zero r k
      have hsplit : ∑ k : K, vectorPosPart r k * (y (n + 1) ω k - negativeOrthantProjection r k)
          = ∑ k : K, vectorPosPart r k * y (n + 1) ω k
            - ∑ k : K, vectorPosPart r k * negativeOrthantProjection r k := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hsplit, hkey, hkey2]
      norm_num
  have happroach := blackwell_approach_negativeOrthant_ae P 𝒢 x y hadapted hbounded hcondExp
    hblackwell
  filter_upwards [happroach] with ω hω
  exact hω

end NoRegretProbability

end StrategicGame
