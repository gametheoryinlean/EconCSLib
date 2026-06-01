/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import Mathlib.Algebra.BigOperators.Field

/-!
# EconCSLib.Examples.StrategicGame.DiagonalGame

For a diagonal matrix with positive diagonal entries `a_i > 0`, the
zero-sum game has

$$
  \operatorname{val}(A) = \left(\sum_i a_i^{-1}\right)^{-1},
  \qquad
  p_i = \frac{a_i^{-1}}{\sum_k a_k^{-1}}.
$$

The same `p` is optimal for both players.

[MFoGT §2.8, Exercise 6].
-/

namespace EconCSLib.StrategicGame.Examples

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- Diagonal matrix game payoff: `A i j = a i` if `i = j`, else `0`. -/
def diagonalGame (a : I → ℝ) : MatrixGame I I ℝ where
  g i j := if i = j then a i else 0

@[simp] theorem diagonalGame_g_diag (a : I → ℝ) (i : I) :
    (diagonalGame a).g i i = a i := by simp [diagonalGame]

@[simp] theorem diagonalGame_g_off (a : I → ℝ) {i j : I} (h : i ≠ j) :
    (diagonalGame a).g i j = 0 := by simp [diagonalGame, h]

/-- The reciprocal-sum constant `c = (∑ a_k⁻¹)⁻¹`. -/
noncomputable def diagonalGameValue (a : I → ℝ) : ℝ := (∑ k, (a k)⁻¹)⁻¹

private theorem sum_inv_pos (a : I → ℝ) (hpos : ∀ i, 0 < a i) :
    0 < ∑ k, (a k)⁻¹ := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  apply Finset.sum_pos' (fun k _ => inv_nonneg.mpr (hpos k).le)
  exact ⟨i₀, Finset.mem_univ _, inv_pos.mpr (hpos i₀)⟩

theorem diagonalGameValue_pos (a : I → ℝ) (hpos : ∀ i, 0 < a i) :
    0 < diagonalGameValue a :=
  inv_pos.mpr (sum_inv_pos a hpos)

/-- Optimal mixed strategy `p_i = a_i⁻¹ / (∑ a_k⁻¹)`. -/
noncomputable def diagonalGameStrategy
    (a : I → ℝ) (hpos : ∀ i, 0 < a i) : stdSimplex ℝ I :=
  ⟨fun i => (a i)⁻¹ / (∑ k, (a k)⁻¹),
    fun i => div_nonneg (inv_nonneg.mpr (hpos i).le) (sum_inv_pos a hpos).le,
    by rw [← Finset.sum_div]; exact div_self (sum_inv_pos a hpos).ne'⟩

@[simp] theorem diagonalGameStrategy_val (a : I → ℝ) (hpos : ∀ i, 0 < a i) (i : I) :
    (diagonalGameStrategy a hpos).val i = (a i)⁻¹ / (∑ k, (a k)⁻¹) := rfl

/-- Player 1 playing `p` guarantees value `c` against every pure column. -/
theorem diagonalGame_row_guarantee (a : I → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ j, diagonalGameValue a
        ≤ (diagonalGame a).Ej (diagonalGameStrategy a hpos) j := by
  intro j
  show diagonalGameValue a ≤ ∑ i, (diagonalGameStrategy a hpos).val i * (diagonalGame a).g i j
  have hcollapse : (∑ i, (diagonalGameStrategy a hpos).val i * (diagonalGame a).g i j)
      = (diagonalGameStrategy a hpos).val j * a j := by
    have hsum_eq : ∀ i,
        (diagonalGameStrategy a hpos).val i * (diagonalGame a).g i j
          = if i = j then (diagonalGameStrategy a hpos).val j * a j else 0 := by
      intro i
      by_cases h : i = j
      · subst h; simp
      · rw [diagonalGame_g_off a h, mul_zero, if_neg h]
    rw [Finset.sum_congr rfl (fun i _ => hsum_eq i), Fintype.sum_ite_eq']
  rw [hcollapse]
  show (∑ k, (a k)⁻¹)⁻¹ ≤ ((a j)⁻¹ / (∑ k, (a k)⁻¹)) * a j
  rw [div_mul_eq_mul_div, inv_mul_cancel₀ (hpos j).ne', one_div]

/-- Player 2 playing `p` caps payoff at `c` against every pure row. -/
theorem diagonalGame_column_guarantee (a : I → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ i, (diagonalGame a).Ei i (diagonalGameStrategy a hpos)
        ≤ diagonalGameValue a := by
  intro i
  show ∑ j, (diagonalGameStrategy a hpos).val j * (diagonalGame a).g i j
    ≤ diagonalGameValue a
  have hcollapse : (∑ j, (diagonalGameStrategy a hpos).val j * (diagonalGame a).g i j)
      = (diagonalGameStrategy a hpos).val i * a i := by
    have hsum_eq : ∀ j,
        (diagonalGameStrategy a hpos).val j * (diagonalGame a).g i j
          = if i = j then (diagonalGameStrategy a hpos).val i * a i else 0 := by
      intro j
      by_cases h : i = j
      · subst h; simp
      · rw [diagonalGame_g_off a h, mul_zero, if_neg h]
    rw [Finset.sum_congr rfl (fun j _ => hsum_eq j), Fintype.sum_ite_eq]
  rw [hcollapse]
  show ((a i)⁻¹ / (∑ k, (a k)⁻¹)) * a i ≤ (∑ k, (a k)⁻¹)⁻¹
  rw [div_mul_eq_mul_div, inv_mul_cancel₀ (hpos i).ne', one_div]

/-- **Diagonal matrix game value** [MFoGT Ex. 2.8.6]. -/
theorem diagonalGame_value (a : I → ℝ) (hpos : ∀ i, 0 < a i) :
    (diagonalGame a).value = diagonalGameValue a := by
  symm
  apply (diagonalGame a).common_guarantee_eq_value
  · exact ⟨diagonalGameStrategy a hpos, diagonalGame_row_guarantee a hpos⟩
  · exact ⟨diagonalGameStrategy a hpos, diagonalGame_column_guarantee a hpos⟩

end EconCSLib.StrategicGame.Examples
