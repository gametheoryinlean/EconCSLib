/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.Antisymmetric

For a square matrix `B : I → I → ℝ` with `B = -Bᵀ` (i.e. `B i j = -B j i`),
the matrix game `B` has value `0` [MFoGT §2.8, Exercise 10(1)].

Equivalently, there exists `x ∈ Δ(I)` such that `(Bx)_i ≤ 0` for every `i`.

## Proof

By the minimax theorem the game has a value `v`. From `B = -Bᵀ`, every
mixed `z` satisfies `zᵀ B z = 0`. Hence for the optimal `xx`:
`∑ j, xx_j · Ej xx j = xxᵀ B xx = 0`, but each `Ej xx j ≥ value`, so
`value ≤ 0`. Symmetrically `value ≥ 0`.
-/

namespace EconCSLib.StrategicGame

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- A square matrix is **antisymmetric** if `B i j = -B j i` for all `i, j`. -/
def IsAntisymmetric (B : I → I → ℝ) : Prop := ∀ i j, B i j = -B j i

/-- An antisymmetric matrix has zero diagonal. -/
theorem IsAntisymmetric.diag_zero {B : I → I → ℝ} (hB : IsAntisymmetric B) (i : I) :
    B i i = 0 := by
  have := hB i i; linarith

/-- For any vector `z`, `∑_{i,j} z_i B_{ij} z_j = 0`. -/
theorem IsAntisymmetric.quadform_zero {B : I → I → ℝ} (hB : IsAntisymmetric B)
    (z : I → ℝ) : ∑ i, ∑ j, z i * B i j * z j = 0 := by
  -- Strategy: set S = LHS, compute T = ∑_i ∑_j z_j B_ji z_i in two ways.
  -- (1) T = S by sum_comm + alpha-rename + ring.
  -- (2) T = -S by antisymmetry B_ji = -B_ij.
  -- Conclude 2 * S = 0.
  set S : ℝ := ∑ i, ∑ j, z i * B i j * z j with hS_def
  have hT_eq_S : (∑ i, ∑ j, z j * B j i * z i) = S := by
    rw [hS_def, Finset.sum_comm]
  have hT_eq_negS : (∑ i, ∑ j, z j * B j i * z i) = -S := by
    have step1 : (∑ i, ∑ j, z j * B j i * z i) = ∑ i, ∑ j, -(z i * B i j * z j) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hB j i]; ring
    rw [step1]
    rw [show (∑ i, ∑ j, -(z i * B i j * z j))
          = ∑ i, -(∑ j, z i * B i j * z j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_neg_distrib _)]
    rw [Finset.sum_neg_distrib]
  linarith [hT_eq_S, hT_eq_negS]

/-- `xᵀ B x = 0` for any mixed strategy `x` (when `B` is antisymmetric),
where `xᵀ B x = ∑ i, xx_i * (∑ j, B_ij * xx_j)`. -/
private theorem antisymmetric_self_pairing_zero {B : I → I → ℝ}
    (hB : IsAntisymmetric B) (x : stdSimplex ℝ I) :
    ∑ i, x.val i * (∑ j, B i j * x.val j) = 0 := by
  have hsplit : (∑ i, x.val i * (∑ j, B i j * x.val j))
              = ∑ i, ∑ j, x.val i * B i j * x.val j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hsplit]
  exact hB.quadform_zero x.val

/-- **Antisymmetric matrix game has value 0** [MFoGT §2.8, Ex. 10(1)]. -/
theorem MatrixGame.antisymmetric_value_zero {B : I → I → ℝ}
    (hB : IsAntisymmetric B) : (⟨B⟩ : MatrixGame I I ℝ).value = 0 := by
  classical
  set game : MatrixGame I I ℝ := ⟨B⟩
  obtain ⟨xx, yy, hxx_row, hyy_col⟩ : ∃ xx yy,
      xx ∈ game.optimalRowStrategies ∧ yy ∈ game.optimalColumnStrategies := by
    obtain ⟨xx, yy, hnash⟩ := game.exists_mixed_nash_equilibrium
    obtain ⟨h1, h2⟩ := (game.optimal_pairs_iff_saddle_point xx yy).mpr hnash
    exact ⟨xx, yy, h1, h2⟩
  have hxx_Ej : ∀ j, game.value ≤ game.Ej xx j := by
    intro j
    have h := (game.mem_optimalRowStrategies_iff_E_ge xx).mp hxx_row (stdSimplex.pure j)
    have heq : game.E xx (stdSimplex.pure j) = game.Ej xx j := by
      show wsum xx (fun i => wsum (stdSimplex.pure j) (game.g i))
        = wsum xx (fun i => game.g i j)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show xx.val i * wsum (stdSimplex.pure j) (game.g i) = xx.val i * game.g i j
      rw [wsum_pure_apply]
    linarith
  have hyy_Ei : ∀ i, game.Ei i yy ≤ game.value := by
    intro i
    have h := (game.mem_optimalColumnStrategies_iff_E_le yy).mp hyy_col (stdSimplex.pure i)
    have heq : game.E (stdSimplex.pure i) yy = game.Ei i yy := by
      show wsum (stdSimplex.pure i) (fun i' => wsum yy (game.g i')) = wsum yy (game.g i)
      rw [wsum_pure_apply]
    linarith
  -- xxᵀ B xx = ∑ j, xx_j * Ej xx j = 0.
  have hxx_pairing : ∑ j, xx.val j * game.Ej xx j = 0 := by
    have hself := antisymmetric_self_pairing_zero hB xx
    have hrewrite : ∑ i, xx.val i * (∑ j, B i j * xx.val j)
                  = ∑ j, xx.val j * game.Ej xx j := by
      show ∑ i, xx.val i * (∑ j, B i j * xx.val j)
        = ∑ j, xx.val j * wsum xx (fun i => B i j)
      rw [show (∑ i, xx.val i * (∑ j, B i j * xx.val j))
            = ∑ i, ∑ j, xx.val i * B i j * xx.val j from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_); ring]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show ∑ i, xx.val i * B i j * xx.val j = xx.val j * wsum xx (fun i => B i j)
      rw [show (wsum xx (fun i => B i j)) = ∑ i, xx.val i * B i j from rfl]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    linarith [hrewrite ▸ hself]
  have hval_le_zero : game.value ≤ 0 := by
    have hbound : ∑ j, xx.val j * game.value ≤ ∑ j, xx.val j * game.Ej xx j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxx_Ej j) (xx.property.1 j))
    rw [← Finset.sum_mul, xx.property.2, one_mul] at hbound
    linarith
  have hyy_pairing : ∑ i, yy.val i * game.Ei i yy = 0 := by
    have hself := antisymmetric_self_pairing_zero hB yy
    have hrewrite : ∑ i, yy.val i * (∑ j, B i j * yy.val j)
                  = ∑ i, yy.val i * game.Ei i yy := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show yy.val i * (∑ j, B i j * yy.val j) = yy.val i * wsum yy (fun j => B i j)
      congr 1
      show ∑ j, B i j * yy.val j = wsum yy (fun j => B i j)
      show ∑ j, B i j * yy.val j = ∑ j, yy.val j * B i j
      refine Finset.sum_congr rfl (fun j _ => ?_); ring
    linarith [hrewrite ▸ hself]
  have hval_ge_zero : 0 ≤ game.value := by
    have hbound : ∑ i, yy.val i * game.Ei i yy ≤ ∑ i, yy.val i * game.value :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hyy_Ei i) (yy.property.1 i))
    rw [← Finset.sum_mul, yy.property.2, one_mul] at hbound
    linarith
  linarith

/-- An antisymmetric matrix game admits an optimal column strategy `y*`
with `(B y*)_i ≤ 0` for every `i`. -/
theorem MatrixGame.antisymmetric_exists_optimal_strategy {B : I → I → ℝ}
    (hB : IsAntisymmetric B) :
    ∃ y : stdSimplex ℝ I, ∀ i, ∑ j, B i j * y.val j ≤ 0 := by
  classical
  set game : MatrixGame I I ℝ := ⟨B⟩
  obtain ⟨xx, yy, _hxx_row, hyy_col⟩ : ∃ xx yy,
      xx ∈ game.optimalRowStrategies ∧ yy ∈ game.optimalColumnStrategies := by
    obtain ⟨xx, yy, hnash⟩ := game.exists_mixed_nash_equilibrium
    obtain ⟨h1, h2⟩ := (game.optimal_pairs_iff_saddle_point xx yy).mpr hnash
    exact ⟨xx, yy, h1, h2⟩
  have hyy_Ei : ∀ i, game.Ei i yy ≤ game.value := by
    intro i
    have h := (game.mem_optimalColumnStrategies_iff_E_le yy).mp hyy_col (stdSimplex.pure i)
    have heq : game.E (stdSimplex.pure i) yy = game.Ei i yy := by
      show wsum (stdSimplex.pure i) (fun i' => wsum yy (game.g i')) = wsum yy (game.g i)
      rw [wsum_pure_apply]
    linarith
  refine ⟨yy, fun i => ?_⟩
  have h := hyy_Ei i
  rw [MatrixGame.antisymmetric_value_zero hB] at h
  show ∑ j, B i j * yy.val j ≤ 0
  have hcomm : (∑ j, B i j * yy.val j) = ∑ j, yy.val j * B i j := by
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hcomm]; exact h

end EconCSLib.StrategicGame
