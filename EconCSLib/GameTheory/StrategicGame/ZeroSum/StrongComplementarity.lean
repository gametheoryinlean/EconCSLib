/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.LinearProgramming.StrongComplementarity
import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.StrongComplementarity

Formalises **matrix-game strong complementarity** [MFoGT Prop. 2.4.1(c)]:
for a finite zero-sum matrix game `A : I → J → ℝ`, there exists an
optimal pair `(xx*, yy*) ∈ X(A) × Y(A)` such that

* `xx*_i > 0 ⟺ A.Ei i yy* = A.value`;
* `yy*_j > 0 ⟺ A.Ej xx* j = A.value`.

The forward direction is `support_complementarity_row/column` and holds
for every optimal pair. The reverse direction comes from LP strong CS
(`EconCSLib.LinearProgramming.exists_strong_complementary_pair`)
applied to the shifted matrix-game LP.

## Proof outline

1. **Shift**: define `K` so `A' i j := A.g i j + K > 0` for every `i, j`.
   The shifted value is `v' := A.value + K > 0`.
2. **LP setup**: the row LP for the shifted game is
   `min ∑ x'_i` subject to `(A'ᵀ x')_j ≥ 1` and `x' ≥ 0`. Optimal `x'`
   rescales to `xx = x' · v'` (a mixed strategy).
3. **Optimal LP pair**: from a matrix-game optimal pair `(xx₀, yy₀)`
   (existence via `MatrixGame.exists_mixed_nash_equilibrium`), set
   `x'₀ := xx₀ / v'`, `u'₀ := yy₀ / v'`. Both have LP objective `1/v'`.
4. **Apply LP strong CS**: gives a strong-CS optimal pair `(x'*, u'*)`.
5. **Rescale and biconditional**: `xx* := x'* · v'`, `yy* := u'* · v'`.
   The LP strict CS conditions translate to the matrix-game biconditional
   via `(A'ᵀ xx*)_j = A.Ej xx* j + K` and `v' = A.value + K`. Specifically:
   * `(Ax* - b)_j > 0 ⟺ u'*_j = 0` becomes
     `A.Ej xx* j > A.value ⟺ yy*_j = 0`, equivalently
     `yy*_j > 0 ⟺ A.Ej xx* j = A.value` (with weak duality giving `≤ A.value`).
   * Symmetric for rows.

The LP theorem indexes primal variables by `Fin n`; we bridge to
`Fintype I` via `Fintype.equivFin I` (a `Fintype.sum_equiv` adapter).
The index types are constrained to `Type` (= `Type 0`) so the
universe inference for `Fintype.sum_equiv` matches `ℝ : Type 0`.

## Blueprint

* `docs/knowledge/nodes/zero_sum/strong_complementarity.md`
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace MatrixGame

variable {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
variable [DecidableEq I] [DecidableEq J]
variable (A : MatrixGame I J ℝ)

/-- **Matrix-game strong complementarity** [MFoGT Prop. 2.4.1(c)].

There exists an optimal pair `(xx, yy) ∈ X(A) × Y(A)` such that for every
row `i`, `xx_i > 0 ↔ A.Ei i yy = A.value`, and for every column `j`,
`yy_j > 0 ↔ A.Ej xx j = A.value`.

The forward direction is `support_complementarity_row/column`. The
reverse direction comes from LP strong complementarity
(`EconCSLib.LinearProgramming.exists_strong_complementary_pair`)
applied to the shifted matrix-game LP. See module docstring for the
detailed proof outline. -/
theorem exists_strong_complementary_pair :
    ∃ (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J),
      xx ∈ A.optimalRowStrategies ∧ yy ∈ A.optimalColumnStrategies ∧
      (∀ i, 0 < xx.val i ↔ A.Ei i yy = A.value) ∧
      (∀ j, 0 < yy.val j ↔ A.Ej xx j = A.value) := by
  classical
  -- ===== Step 1: Shift constant K and shifted value v'. =====
  set Kmax : ℝ := Finset.sup' (Finset.univ : Finset (I × J))
      ⟨⟨Classical.arbitrary I, Classical.arbitrary J⟩, Finset.mem_univ _⟩
      (fun p => |A.g p.1 p.2|) with hKmax_def
  set K : ℝ := 1 + |A.value| + Kmax with hK_def
  have hKmax_ge : ∀ i j, |A.g i j| ≤ Kmax := fun i j =>
    Finset.le_sup' (fun p => |A.g p.1 p.2|) (Finset.mem_univ (i, j))
  have hA'_pos : ∀ i j, 0 < A.g i j + K := fun i j => by
    have h := hKmax_ge i j
    have h2 : -A.g i j ≤ |A.g i j| := neg_le_abs _
    have h3 : 0 ≤ |A.value| := abs_nonneg _
    linarith
  set v' : ℝ := A.value + K with hv'_def
  have hv'_pos : 0 < v' := by
    have habs_v : -A.value ≤ |A.value| := neg_le_abs _
    have hKmax_nn : 0 ≤ Kmax := le_trans (abs_nonneg _)
      (hKmax_ge (Classical.arbitrary I) (Classical.arbitrary J))
    rw [hv'_def, hK_def]; linarith
  have hv'_ne : v' ≠ 0 := hv'_pos.ne'
  -- ===== Step 2: Shifted-payoff identities. =====
  have hA'_Ej : ∀ (xx : stdSimplex ℝ I) (j : J),
      ∑ i, (A.g i j + K) * xx.val i = A.Ej xx j + K := by
    intro xx j
    have hEj_eq : A.Ej xx j = ∑ i, A.g i j * xx.val i := by
      show wsum xx (fun i => A.g i j) = ∑ i, A.g i j * xx.val i
      refine Finset.sum_congr rfl (fun i _ => ?_); exact mul_comm _ _
    rw [show (∑ i, (A.g i j + K) * xx.val i)
          = (∑ i, A.g i j * xx.val i) + K * (∑ i, xx.val i) from by
      rw [show (∑ i, (A.g i j + K) * xx.val i)
            = ∑ i, (A.g i j * xx.val i + K * xx.val i) from
            Finset.sum_congr rfl (fun i _ => by ring)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]]
    rw [xx.property.2, mul_one, hEj_eq]
  have hA'_Ei : ∀ (yy : stdSimplex ℝ J) (i : I),
      ∑ j, (A.g i j + K) * yy.val j = A.Ei i yy + K := by
    intro yy i
    have hEi_eq : A.Ei i yy = ∑ j, A.g i j * yy.val j := by
      show wsum yy (A.g i) = ∑ j, A.g i j * yy.val j
      refine Finset.sum_congr rfl (fun j _ => ?_); exact mul_comm _ _
    rw [show (∑ j, (A.g i j + K) * yy.val j)
          = (∑ j, A.g i j * yy.val j) + K * (∑ j, yy.val j) from by
      rw [show (∑ j, (A.g i j + K) * yy.val j)
            = ∑ j, (A.g i j * yy.val j + K * yy.val j) from
            Finset.sum_congr rfl (fun j _ => by ring)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]]
    rw [yy.property.2, mul_one, hEi_eq]
  -- ===== Step 3: Matrix-game optimal pair via existing infrastructure. =====
  obtain ⟨xx₀, yy₀, hxx₀_row, hyy₀_col⟩ : ∃ xx yy,
      xx ∈ A.optimalRowStrategies ∧ yy ∈ A.optimalColumnStrategies := by
    obtain ⟨xx, yy, hnash⟩ := A.exists_mixed_nash_equilibrium
    obtain ⟨h1, h2⟩ := (A.optimal_pairs_iff_saddle_point xx yy).mpr hnash
    exact ⟨xx, yy, h1, h2⟩
  have hxx₀_Ej : ∀ j, A.value ≤ A.Ej xx₀ j := by
    intro j
    have h := (A.mem_optimalRowStrategies_iff_E_ge xx₀).mp hxx₀_row (stdSimplex.pure j)
    have heq : A.E xx₀ (stdSimplex.pure j) = A.Ej xx₀ j := by
      show wsum xx₀ (fun i => wsum (stdSimplex.pure j) (A.g i))
        = wsum xx₀ (fun i => A.g i j)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show xx₀.val i * wsum (stdSimplex.pure j) (A.g i) = xx₀.val i * A.g i j
      rw [wsum_pure_apply]
    linarith
  have hyy₀_Ei : ∀ i, A.Ei i yy₀ ≤ A.value := by
    intro i
    have h := (A.mem_optimalColumnStrategies_iff_E_le yy₀).mp hyy₀_col (stdSimplex.pure i)
    have heq : A.E (stdSimplex.pure i) yy₀ = A.Ei i yy₀ := by
      show wsum (stdSimplex.pure i) (fun i' => wsum yy₀ (A.g i')) = wsum yy₀ (A.g i)
      rw [wsum_pure_apply]
    linarith
  -- ===== Step 4: I ≃ Fin (card I), setup LP. =====
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  set n : ℕ := Fintype.card I with hn_def
  let M : J → Fin n → ℝ := fun j k => A.g (e.symm k) j + K
  let bvec : J → ℝ := fun _ => 1
  let cvec : Fin n → ℝ := fun _ => 1
  let x'₀_fin : Fin n → ℝ := fun k => xx₀.val (e.symm k) / v'
  let u'₀ : J → ℝ := fun j => yy₀.val j / v'
  -- Sum-equivalence helper: ∑ k : Fin n, f (e.symm k) = ∑ i : I, f i.
  have hsum_eq : ∀ (f : I → ℝ), (∑ k, f (e.symm k)) = ∑ i, f i := by
    intro f
    exact Fintype.sum_equiv e.symm (fun k => f (e.symm k)) f (fun k => rfl)
  -- LP primal feasibility for x'₀_fin.
  have hx'₀_feas : ∀ j, bvec j ≤ ∑ k, M j k * x'₀_fin k := by
    intro j
    show (1 : ℝ) ≤ ∑ k, (A.g (e.symm k) j + K) * (xx₀.val (e.symm k) / v')
    rw [show (∑ k, (A.g (e.symm k) j + K) * (xx₀.val (e.symm k) / v'))
          = (∑ i, (A.g i j + K) * (xx₀.val i / v')) from
      hsum_eq (fun i => (A.g i j + K) * (xx₀.val i / v'))]
    rw [show (∑ i, (A.g i j + K) * (xx₀.val i / v'))
          = (∑ i, (A.g i j + K) * xx₀.val i) / v' from by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
    rw [hA'_Ej xx₀ j, le_div_iff₀ hv'_pos, one_mul, hv'_def]
    linarith [hxx₀_Ej j]
  have hx'₀_nn : ∀ k, 0 ≤ x'₀_fin k := fun k =>
    div_nonneg (xx₀.property.1 (e.symm k)) hv'_pos.le
  have hx'₀_val : ∑ k, cvec k * x'₀_fin k = 1 / v' := by
    show ∑ k, (1 : ℝ) * (xx₀.val (e.symm k) / v') = 1 / v'
    rw [show (∑ k, (1 : ℝ) * (xx₀.val (e.symm k) / v'))
          = (∑ i, (1 : ℝ) * (xx₀.val i / v')) from
      hsum_eq (fun i => (1 : ℝ) * (xx₀.val i / v'))]
    rw [show (∑ i, (1 : ℝ) * (xx₀.val i / v')) = (∑ i, xx₀.val i) / v' from by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
    rw [xx₀.property.2]
  have hu'₀_du : EconCSLib.LinearProgramming.DualFeasible M cvec u'₀ := by
    refine ⟨fun j => div_nonneg (yy₀.property.1 j) hv'_pos.le, ?_⟩
    intro k
    show (∑ j, u'₀ j * M j k) ≤ cvec k
    show (∑ j, yy₀.val j / v' * (A.g (e.symm k) j + K)) ≤ 1
    rw [show (∑ j, yy₀.val j / v' * (A.g (e.symm k) j + K))
        = (∑ j, (A.g (e.symm k) j + K) * yy₀.val j) / v' from by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun j _ => ?_); ring]
    rw [hA'_Ei yy₀ (e.symm k), div_le_iff₀ hv'_pos, one_mul, hv'_def]
    linarith [hyy₀_Ei (e.symm k)]
  have hu'₀_val : ∑ j, u'₀ j * bvec j = 1 / v' := by
    show ∑ j, yy₀.val j / v' * (1 : ℝ) = 1 / v'
    rw [show (∑ j, yy₀.val j / v' * (1 : ℝ)) = (∑ j, yy₀.val j) / v' from by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun j _ => ?_); ring]
    rw [yy₀.property.2]
  have hN_pos : (0 : ℝ) < ((Fintype.card J + n : ℕ) : ℝ) := by
    have : 0 < Fintype.card J + n := by
      have : 0 < Fintype.card J := Fintype.card_pos; omega
    exact_mod_cast this
  -- ===== Step 5: Apply LP strong CS. =====
  obtain ⟨x'_star, u'_star, hx_feas_str, hx_nn_str, hu_du_str, hcx_str, hub_str,
          hrow_str, hcol_str⟩ :=
    EconCSLib.LinearProgramming.exists_strong_complementary_pair
      M bvec cvec (1/v') hN_pos
      hx'₀_feas hx'₀_nn hx'₀_val
      hu'₀_du hu'₀_val
  -- ===== Step 6: Sum identities for the strong-pair. =====
  have hx'_star_sum_eq : ∑ k, x'_star k = 1 / v' := by
    have h1 : (∑ k, cvec k * x'_star k) = ∑ k, x'_star k :=
      Finset.sum_congr rfl (fun k _ => by show (1 : ℝ) * _ = _; ring)
    linarith [h1, hcx_str]
  have hu'_star_sum_eq : ∑ j, u'_star j = 1 / v' := by
    have h1 : (∑ j, u'_star j * bvec j) = ∑ j, u'_star j :=
      Finset.sum_congr rfl (fun j _ => by show _ * (1 : ℝ) = _; ring)
    linarith [h1, hub_str]
  -- xx_star, yy_star as mixed strategies.
  have hxx_star_sum : ∑ i, x'_star (e i) * v' = 1 := by
    rw [← Finset.sum_mul]
    rw [show (∑ i, x'_star (e i)) = ∑ k, x'_star k from
      Fintype.sum_equiv e _ _ (fun _ => rfl)]
    rw [hx'_star_sum_eq]; field_simp
  have hyy_star_sum : ∑ j, u'_star j * v' = 1 := by
    rw [← Finset.sum_mul]
    rw [hu'_star_sum_eq]; field_simp
  let xx_star : stdSimplex ℝ I :=
    ⟨fun i => x'_star (e i) * v',
     fun i => mul_nonneg (hx_nn_str (e i)) hv'_pos.le,
     hxx_star_sum⟩
  let yy_star : stdSimplex ℝ J :=
    ⟨fun j => u'_star j * v',
     fun j => mul_nonneg (hu_du_str.1 j) hv'_pos.le,
     hyy_star_sum⟩
  -- ===== Step 7: Verify xx_star, yy_star are optimal. =====
  have hxx_star_Ej : ∀ j, A.value ≤ A.Ej xx_star j := by
    intro j
    have h := hx_feas_str j
    have hconv : ∑ k, M j k * x'_star k = ∑ i, (A.g i j + K) * x'_star (e i) := by
      show ∑ k, (A.g (e.symm k) j + K) * x'_star k
         = ∑ i, (A.g i j + K) * x'_star (e i)
      rw [show (∑ k, (A.g (e.symm k) j + K) * x'_star k)
            = ∑ k, (fun i => (A.g i j + K) * x'_star (e i)) (e.symm k) from by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        show (A.g (e.symm k) j + K) * x'_star k
           = (A.g (e.symm k) j + K) * x'_star (e (e.symm k))
        rw [Equiv.apply_symm_apply]]
      exact hsum_eq (fun i => (A.g i j + K) * x'_star (e i))
    rw [hconv] at h
    have h2 : v' ≤ ∑ i, (A.g i j + K) * (x'_star (e i) * v') := by
      rw [show (∑ i, (A.g i j + K) * (x'_star (e i) * v'))
          = (∑ i, (A.g i j + K) * x'_star (e i)) * v' from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
      have := mul_le_mul_of_nonneg_right h hv'_pos.le
      linarith [this]
    rw [hA'_Ej xx_star j, hv'_def] at h2
    show A.value ≤ wsum xx_star (fun i => A.g i j)
    have : A.Ej xx_star j ≥ A.value := by linarith
    exact this
  have hyy_star_Ei : ∀ i, A.Ei i yy_star ≤ A.value := by
    intro i
    have h := hu_du_str.2 (e i)
    have hh : ∑ j, u'_star j * (A.g i j + K) ≤ 1 := by
      convert h using 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show u'_star j * (A.g i j + K) = u'_star j * (A.g (e.symm (e i)) j + K)
      rw [Equiv.symm_apply_apply]
    have h2 : ∑ j, (A.g i j + K) * (u'_star j * v') ≤ v' := by
      rw [show (∑ j, (A.g i j + K) * (u'_star j * v'))
          = (∑ j, u'_star j * (A.g i j + K)) * v' from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => ?_); ring]
      have := mul_le_mul_of_nonneg_right hh hv'_pos.le
      linarith [this]
    rw [hA'_Ei yy_star i, hv'_def] at h2
    show wsum yy_star (A.g i) ≤ A.value
    have : A.Ei i yy_star ≤ A.value := by linarith
    exact this
  have hxx_star_row : xx_star ∈ A.optimalRowStrategies := by
    rw [A.mem_optimalRowStrategies_iff_E_ge]
    intro y'
    have heq : A.E xx_star y' = wsum y' (fun j => A.Ej xx_star j) := by
      show wsum xx_star (fun i => wsum y' (A.g i))
        = wsum y' (fun j => wsum xx_star (fun i => A.g i j))
      exact wsum_wsum_comm xx_star y' A.g
    rw [heq]
    calc A.value = wsum y' (fun _ => A.value) := (wsum_const y' A.value).symm
      _ ≤ wsum y' (fun j => A.Ej xx_star j) := wsum_le_wsum y' hxx_star_Ej
  have hyy_star_col : yy_star ∈ A.optimalColumnStrategies := by
    rw [A.mem_optimalColumnStrategies_iff_E_le]
    intro x'
    have heq : A.E x' yy_star = wsum x' (fun i => A.Ei i yy_star) := rfl
    rw [heq]
    calc wsum x' (fun i => A.Ei i yy_star)
        ≤ wsum x' (fun _ => A.value) := wsum_le_wsum x' hyy_star_Ei
      _ = A.value := wsum_const x' A.value
  refine ⟨xx_star, yy_star, hxx_star_row, hyy_star_col, ?_, ?_⟩
  · -- Row biconditional: ∀ i, 0 < xx_star.val i ↔ A.Ei i yy_star = A.value.
    intro i
    refine ⟨fun h => A.support_complementarity_row xx_star yy_star
              hxx_star_row hyy_star_col h, ?_⟩
    intro hbr
    by_contra hxx_zero
    push_neg at hxx_zero
    have hxx_zero_eq : xx_star.val i = 0 :=
      le_antisymm hxx_zero (mul_nonneg (hx_nn_str (e i)) hv'_pos.le)
    have hx'_zero : x'_star (e i) = 0 := by
      have : x'_star (e i) * v' = 0 := hxx_zero_eq
      exact (mul_eq_zero.mp this).resolve_right hv'_ne
    have hcol := hcol_str (e i)
    rw [hx'_zero, zero_add] at hcol
    have hsum_simp : ∑ j, u'_star j * M j (e i) = ∑ j, u'_star j * (A.g i j + K) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show u'_star j * (A.g (e.symm (e i)) j + K) = u'_star j * (A.g i j + K)
      rw [Equiv.symm_apply_apply]
    rw [hsum_simp] at hcol
    have hkey : (∑ j, u'_star j * (A.g i j + K)) * v' = v' := by
      have h_mul : ∑ j, (A.g i j + K) * (u'_star j * v')
                = (∑ j, u'_star j * (A.g i j + K)) * v' := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
      have heq : ∑ j, (A.g i j + K) * (u'_star j * v') = A.Ei i yy_star + K :=
        hA'_Ei yy_star i
      rw [hbr, hv'_def] at heq
      linarith [h_mul]
    have hsum_eq_one : ∑ j, u'_star j * (A.g i j + K) = 1 := by
      have := hkey
      field_simp at this
      exact this
    rw [hsum_eq_one] at hcol
    have hcvec : cvec (e i) = 1 := rfl
    rw [hcvec] at hcol
    linarith
  · -- Column biconditional: ∀ j, 0 < yy_star.val j ↔ A.Ej xx_star j = A.value.
    intro j
    refine ⟨fun h => A.support_complementarity_column xx_star yy_star
              hxx_star_row hyy_star_col h, ?_⟩
    intro hbr
    by_contra hyy_zero
    push_neg at hyy_zero
    have hyy_zero_eq : yy_star.val j = 0 :=
      le_antisymm hyy_zero (mul_nonneg (hu_du_str.1 j) hv'_pos.le)
    have hu'_zero : u'_star j = 0 := by
      have : u'_star j * v' = 0 := hyy_zero_eq
      exact (mul_eq_zero.mp this).resolve_right hv'_ne
    have hrow := hrow_str j
    rw [hu'_zero, add_zero] at hrow
    have hconv : ∑ k, M j k * x'_star k = ∑ i, (A.g i j + K) * x'_star (e i) := by
      show ∑ k, (A.g (e.symm k) j + K) * x'_star k
         = ∑ i, (A.g i j + K) * x'_star (e i)
      rw [show (∑ k, (A.g (e.symm k) j + K) * x'_star k)
            = ∑ k, (fun i => (A.g i j + K) * x'_star (e i)) (e.symm k) from by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        show (A.g (e.symm k) j + K) * x'_star k
           = (A.g (e.symm k) j + K) * x'_star (e (e.symm k))
        rw [Equiv.apply_symm_apply]]
      exact hsum_eq (fun i => (A.g i j + K) * x'_star (e i))
    rw [hconv] at hrow
    -- hrow : 0 < (∑ i, (A.g i j + K) * x'_star (e i)) - bvec j
    have hkey : (∑ i, (A.g i j + K) * x'_star (e i)) * v' = A.Ej xx_star j + K := by
      have hsumv : ∑ i, (A.g i j + K) * (x'_star (e i) * v')
                = (∑ i, (A.g i j + K) * x'_star (e i)) * v' := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => ?_); ring
      have heq := hA'_Ej xx_star j
      linarith [heq, hsumv]
    have hsum_eq_one : ∑ i, (A.g i j + K) * x'_star (e i) = 1 := by
      have h := hkey
      rw [hbr, ← hv'_def] at h
      -- h : (∑ ...) * v' = v'
      have hh : (∑ i, (A.g i j + K) * x'_star (e i)) * v' = 1 * v' := by rw [h, one_mul]
      exact mul_right_cancel₀ hv'_ne hh
    rw [hsum_eq_one] at hrow
    have hbvec : bvec j = 1 := rfl
    rw [hbvec] at hrow
    linarith

end MatrixGame
