/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Minimax.Loomis

/-!
# EconCSLib.Math.LinearAlgebra.PerronFrobenius

Formalises **Perron-Frobenius** for strictly positive square matrices
[MFoGT, Section 2.8, Exercise 1(2)] over `ℝ` as an application of the
general-`B` Loomis theorem.

For any `M : Fin n → Fin n → ℝ` with `M i j > 0` for every `i, j`, there
exist `x, y ∈ Δ(Fin n)` and `λ > 0` such that
* `x` and `y` have **strictly positive components**;
* `x M = λ · x` (so `x` is a left eigenvector at eigenvalue `λ`);
* `M y = λ · y` (so `y` is a right eigenvector at the same `λ`).

`λ = 1/v` where `v` is the Loomis value of `(I, M)` (identity vs. `M`).

## Proof strategy (per blueprint)

Apply `Loomis.loomis_theorem` with `A := I` (identity) and `B := M`.
Loomis produces `(x, y, v)` with `v · (xM)_j ≤ x_j` and `y_i ≤ v · (My)_i`.

1. **v > 0**: from any `y i₀ > 0` (some such i₀ exists since `∑ y i = 1`),
   combine with `(My)_{i₀} > 0` (since `M > 0` and `y ≥ 0` with full
   support… wait, just need `(My)_i > 0`).
2. **x > 0 strictly**: `x_j ≥ v · (xM)_j > 0`.
3. **Tight inner product**: `⟨x, y⟩ = v · ⟨x, My⟩` (sandwich is tight).
4. **y > 0 strictly**: from tightness on `(2)` weighted by `x > 0`, every
   `y_i = v · (My)_i > 0`.
5. **Eigenvector**: with `y > 0` strict, tightness on `(1)` gives
   `x_j = v · (xM)_j` for all j, i.e., `xM = (1/v) · x`.

## Blueprint

* `docs/knowledge/nodes/zero_sum/perron_frobenius_positive_matrix.md`
-/

open Finset BigOperators Loomis

set_option linter.unusedSectionVars false

namespace EconCSLib.LinearAlgebra

variable {n : ℕ} [NeZero n]

/-! ### Identity matrix and its `wsum` -/

/-- The identity matrix on `Fin n`. -/
private def idMat : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0

private theorem xA_idMat (x : stdSimplex ℝ (Fin n)) (j : Fin n) :
    Loomis.xA idMat x j = x.val j := by
  classical
  show ∑ i, x.val i * (if i = j then (1 : ℝ) else 0) = x.val j
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']

private theorem Ay_idMat (y : stdSimplex ℝ (Fin n)) (i : Fin n) :
    Loomis.Ay idMat y i = y.val i := by
  classical
  show ∑ j, y.val j * (if i = j then (1 : ℝ) else 0) = y.val i
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

/-! ### Perron-Frobenius theorem -/

/-- **Perron-Frobenius for positive matrices** [MFoGT, Section 2.8,
Exercise 1(2)]. A square matrix with strictly positive entries has a
strictly positive eigenvalue `λ > 0` with **both** a strictly positive
left eigenvector `x` and a strictly positive right eigenvector `y` (each
a probability distribution on `Fin n`). -/
theorem perron_frobenius (M : Fin n → Fin n → ℝ) (hM_pos : ∀ i j, 0 < M i j) :
    ∃ (x y : stdSimplex ℝ (Fin n)) (lam : ℝ),
      0 < lam ∧
      (∀ i, 0 < x.val i) ∧
      (∀ i, 0 < y.val i) ∧
      (∀ j, wsum x (fun i => M i j) = lam * x.val j) ∧
      (∀ i, wsum y (M i) = lam * y.val i) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  -- Apply Loomis with A = identity, B = M.
  have hM_isPos : Loomis.IsPositive M := hM_pos
  obtain ⟨x, y, v, hx_raw, hy_raw⟩ :=
    Loomis.loomis_theorem idMat M hM_isPos
  -- Substitute the identity-matrix wsum values.
  have hx_ineq : ∀ j, v * Loomis.xB M x j ≤ x.val j := by
    intro j
    have h := hx_raw j
    rw [xA_idMat] at h
    exact h
  have hy_ineq : ∀ i, y.val i ≤ v * Loomis.By M y i := by
    intro i
    have h := hy_raw i
    rw [Ay_idMat] at h
    exact h
  -- Step 1: v > 0.
  have hy_sum : (∑ i, y.val i) = 1 := y.property.2
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < y.val i₀ := by
    by_contra hall
    push_neg at hall
    have hzero : ∀ i, y.val i = 0 := fun i => le_antisymm (hall i) (y.property.1 i)
    have hsum : (∑ i, y.val i) = 0 := by simp_rw [hzero]; simp
    linarith
  have hBy_pos₀ : 0 < Loomis.By M y i₀ := Loomis.By_pos hM_isPos y i₀
  have hv_pos : 0 < v := by
    have h := hy_ineq i₀
    by_contra hv_neg
    push_neg at hv_neg
    have : v * Loomis.By M y i₀ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hv_neg hBy_pos₀.le
    linarith
  -- Step 2: x is strictly positive.
  have hx_strict : ∀ j, 0 < x.val j := by
    intro j
    have hxB : 0 < Loomis.xB M x j := Loomis.xB_pos hM_isPos x j
    calc 0 < v * Loomis.xB M x j := mul_pos hv_pos hxB
      _ ≤ x.val j := hx_ineq j
  -- Step 3: Tight inner product. Weight (1) by y and (2) by x; bilinearity
  -- of M makes the bounds match exactly.
  have hcomm : (∑ j, Loomis.xB M x j * y.val j)
      = ∑ i, x.val i * Loomis.By M y i := by
    -- ∑_j (xM)_j · y_j = ∑_j ∑_i x_i M_ij y_j = ∑_i ∑_j x_i M_ij y_j
    --                  = ∑_i x_i · (My)_i
    show (∑ j, (∑ i, x.val i * M i j) * y.val j)
        = ∑ i, x.val i * (∑ j, y.val j * M i j)
    have h1 : (∑ j, (∑ i, x.val i * M i j) * y.val j)
        = ∑ j, ∑ i, x.val i * M i j * y.val j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
    have h2 : (∑ j, ∑ i, x.val i * M i j * y.val j)
        = ∑ i, ∑ j, x.val i * M i j * y.val j := Finset.sum_comm
    have h3 : (∑ i, ∑ j, x.val i * M i j * y.val j)
        = ∑ i, x.val i * (∑ j, y.val j * M i j) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h1, h2, h3]
  -- Lower bound on ⟨x, y⟩ via (1):
  have hxy_lower : v * (∑ j, Loomis.xB M x j * y.val j) ≤ ∑ j, x.val j * y.val j := by
    rw [show v * (∑ j, Loomis.xB M x j * y.val j)
        = ∑ j, v * (Loomis.xB M x j * y.val j) from Finset.mul_sum _ _ _]
    apply Finset.sum_le_sum
    intro j _
    have : v * Loomis.xB M x j ≤ x.val j := hx_ineq j
    have hyj : 0 ≤ y.val j := y.property.1 j
    nlinarith
  -- Upper bound on ⟨x, y⟩ via (2) (weighted by x):
  have hxy_upper : (∑ i, x.val i * y.val i) ≤ v * (∑ i, x.val i * Loomis.By M y i) := by
    rw [show v * (∑ i, x.val i * Loomis.By M y i)
        = ∑ i, v * (x.val i * Loomis.By M y i) from Finset.mul_sum _ _ _]
    apply Finset.sum_le_sum
    intro i _
    have : y.val i ≤ v * Loomis.By M y i := hy_ineq i
    have hxi : 0 ≤ x.val i := x.property.1 i
    nlinarith
  -- ⟨x, y⟩ symmetry
  have hxy_swap : (∑ j, x.val j * y.val j) = ∑ i, x.val i * y.val i := rfl
  -- Combine: ⟨x, y⟩ ≥ v · ⟨xM, y⟩ = v · ⟨x, My⟩ ≥ ⟨x, y⟩.
  have hxy_tight : (∑ i, x.val i * y.val i)
      = v * (∑ j, Loomis.xB M x j * y.val j) := by
    have hcomm_mul : v * (∑ j, Loomis.xB M x j * y.val j)
        = v * (∑ i, x.val i * Loomis.By M y i) := by rw [hcomm]
    -- hxy_lower : v · ⟨xM, y⟩ ≤ ⟨x, y⟩
    -- hxy_upper : ⟨x, y⟩ ≤ v · ⟨x, My⟩ = v · ⟨xM, y⟩
    linarith [hxy_lower, hxy_upper, hcomm_mul]
  -- Step 4: y_i = v * (My)_i for all i (from x > 0 strictness on (2)).
  have hy_eq : ∀ i, y.val i = v * Loomis.By M y i := by
    intro i
    -- ∑_i x_i · ((v · By y)_i - y_i) ≥ 0 per term, sum = 0, x_i > 0, so each = 0.
    have hsum_zero :
        (∑ i, x.val i * (v * Loomis.By M y i - y.val i)) = 0 := by
      have hrw : (∑ i, x.val i * (v * Loomis.By M y i - y.val i))
          = (v * ∑ i, x.val i * Loomis.By M y i)
            - (∑ i, x.val i * y.val i) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [hrw]
      -- v · ⟨x, My⟩ = ⟨x, y⟩ (= ⟨x, y⟩ as above)
      have : v * (∑ i, x.val i * Loomis.By M y i)
          = ∑ i, x.val i * y.val i := by
        rw [← hcomm]; linarith
      linarith
    -- Each summand is nonneg, x_i > 0, so each (v · By y i - y_i) = 0.
    have hnn : ∀ i ∈ Finset.univ,
        0 ≤ x.val i * (v * Loomis.By M y i - y.val i) := by
      intro i _
      have h_diff : 0 ≤ v * Loomis.By M y i - y.val i := by linarith [hy_ineq i]
      exact mul_nonneg (hx_strict i).le h_diff
    have h_each : ∀ i ∈ Finset.univ,
        x.val i * (v * Loomis.By M y i - y.val i) = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_zero i hi
    have hi_term := h_each i (Finset.mem_univ _)
    -- x_i > 0 forces v · By y i - y_i = 0
    have hx_i_ne : x.val i ≠ 0 := (hx_strict i).ne'
    have : v * Loomis.By M y i - y.val i = 0 := by
      have := hi_term
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx_i_ne
      · linarith
    linarith
  -- Step 5: y > 0 strict (from y_i = v * (My)_i > 0).
  have hy_strict : ∀ i, 0 < y.val i := by
    intro i
    rw [hy_eq i]
    exact mul_pos hv_pos (Loomis.By_pos hM_isPos y i)
  -- Step 6: x_j = v * (xM)_j for all j (from y > 0 strictness on (1)).
  have hx_eq : ∀ j, x.val j = v * Loomis.xB M x j := by
    intro j
    -- Same argument as Step 4, dual.
    have hsum_zero :
        (∑ j, y.val j * (x.val j - v * Loomis.xB M x j)) = 0 := by
      have hrw : (∑ j, y.val j * (x.val j - v * Loomis.xB M x j))
          = (∑ j, y.val j * x.val j)
            - (v * ∑ j, Loomis.xB M x j * y.val j) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [hrw]
      have hcomm_xy : (∑ j, y.val j * x.val j) = ∑ i, x.val i * y.val i := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [hcomm_xy]
      linarith
    have hnn : ∀ j ∈ Finset.univ,
        0 ≤ y.val j * (x.val j - v * Loomis.xB M x j) := by
      intro j _
      have h_diff : 0 ≤ x.val j - v * Loomis.xB M x j := by linarith [hx_ineq j]
      exact mul_nonneg (hy_strict j).le h_diff
    have h_each : ∀ j ∈ Finset.univ,
        y.val j * (x.val j - v * Loomis.xB M x j) = 0 := by
      intro j hj
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_zero j hj
    have hi_term := h_each j (Finset.mem_univ _)
    have hy_j_ne : y.val j ≠ 0 := (hy_strict j).ne'
    have : x.val j - v * Loomis.xB M x j = 0 := by
      rcases mul_eq_zero.mp hi_term with h | h
      · exact absurd h hy_j_ne
      · linarith
    linarith
  -- Package: lam := 1/v.
  refine ⟨x, y, 1/v, ?_, hx_strict, hy_strict, ?_, ?_⟩
  · exact one_div_pos.mpr hv_pos
  · intro j
    have h := hx_eq j
    -- xM j = (1/v) * x_j follows from x_j = v * xM_j
    show Loomis.xB M x j = 1/v * x.val j
    have hv_ne : v ≠ 0 := hv_pos.ne'
    field_simp
    linarith
  · intro i
    have h := hy_eq i
    show Loomis.By M y i = 1/v * y.val i
    have hv_ne : v ≠ 0 := hv_pos.ne'
    field_simp
    linarith

end EconCSLib.LinearAlgebra
