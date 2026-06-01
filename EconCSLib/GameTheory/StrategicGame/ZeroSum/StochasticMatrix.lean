/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import Mathlib.Algebra.BigOperators.Field

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix

Formalises **[MFoGT Cor. 2.5.2]**: every finite stochastic matrix has an
invariant distribution. Proven via the matrix game with payoff `B := A − I`:
its value is `0`, and any row-optimal strategy `x*` is a left eigenvector
of `A` (i.e. `x* A = x*`).

## Main results

* `IsStochasticMatrix` — predicate for a row-stochastic matrix.
* `uniformDist` — uniform mixed strategy on a finite nonempty type.
* `MatrixGame.exists_invariant_distribution` — every stochastic matrix
  admits an invariant distribution.

## Blueprint

* `docs/knowledge/nodes/zero_sum/stochastic_matrix_invariant_distribution.md`
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace EconCSLib.StrategicGame

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- A finite (row-)**stochastic matrix**: entries are non-negative and each
row sums to `1`. -/
structure IsStochasticMatrix (A : I → I → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  rowSum : ∀ i, ∑ j, A i j = 1

namespace IsStochasticMatrix

variable {A : I → I → ℝ}

/-- The total mass after one application of a stochastic matrix to a
probability vector equals the initial mass: `∑_j (xA)_j = ∑_i x_i`. -/
theorem total_mass_preserved (hA : IsStochasticMatrix A) (x : I → ℝ) :
    ∑ j, ∑ i, x i * A i j = ∑ i, x i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum, hA.rowSum, mul_one]

end IsStochasticMatrix

/-- Uniform mixed strategy on a finite nonempty index type. -/
noncomputable def uniformDist : stdSimplex ℝ I :=
  ⟨fun _ => (1 : ℝ) / (Fintype.card I : ℝ),
    fun _ => by
      have : (0 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Nat.zero_le _
      exact div_nonneg (by norm_num) this,
    by
      have hcard_pos : 0 < (Fintype.card I : ℝ) := by
        exact_mod_cast Fintype.card_pos
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp⟩

@[simp] theorem uniformDist_val (i : I) :
    (uniformDist (I := I)).val i = (1 : ℝ) / (Fintype.card I : ℝ) := rfl

/-! ### The displacement matrix `B = A − I` -/

namespace MatrixGame

/-- The displacement matrix `B i j := A i j − [i = j]` of a stochastic
matrix `A`. The corresponding matrix game has value `0`. -/
private def disp (A : I → I → ℝ) : I → I → ℝ :=
  fun i j => A i j - (if i = j then 1 else 0)

/-- Column-side payoff under `disp A`: `Ej x j = (xA)_j − x_j`. -/
private theorem disp_Ej (A : I → I → ℝ) (x : stdSimplex ℝ I) (j : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ej x j
      = (∑ i, x.val i * A i j) - x.val j := by
  show wsum x (fun i => disp A i j) = (∑ i, x.val i * A i j) - x.val j
  show (∑ i, x.val i * (A i j - if i = j then 1 else 0))
      = (∑ i, x.val i * A i j) - x.val j
  rw [show (∑ i, x.val i * (A i j - if i = j then 1 else 0))
        = (∑ i, x.val i * A i j) - (∑ i, x.val i * (if i = j then 1 else 0)) from by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun i _ => ?_); ring]
  congr 1
  show ∑ i, x.val i * (if i = j then (1 : ℝ) else 0) = x.val j
  simp [Fintype.sum_ite_eq', mul_ite]

/-- Row-side payoff under `disp A`: `Ei i y = (Ay)_i − y_i`. -/
private theorem disp_Ei (A : I → I → ℝ) (y : stdSimplex ℝ I) (i : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ei i y
      = (∑ j, A i j * y.val j) - y.val i := by
  show wsum y (fun j => disp A i j) = (∑ j, A i j * y.val j) - y.val i
  show (∑ j, y.val j * (A i j - if i = j then 1 else 0))
      = (∑ j, A i j * y.val j) - y.val i
  rw [show (∑ j, y.val j * (A i j - if i = j then 1 else 0))
        = (∑ j, y.val j * A i j) - (∑ j, y.val j * (if i = j then 1 else 0)) from by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun j _ => ?_); ring]
  rw [show (∑ j, y.val j * A i j) = ∑ j, A i j * y.val j from
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)]
  congr 1
  show ∑ j, y.val j * (if i = j then (1 : ℝ) else 0) = y.val i
  simp [Fintype.sum_ite_eq, mul_ite]

/-- Under the uniform distribution, the column-side payoff under `disp A`
is zero (when `A` is stochastic). -/
private theorem disp_Ei_uniform (A : I → I → ℝ) (hA : IsStochasticMatrix A) (i : I) :
    (⟨disp A⟩ : MatrixGame I I ℝ).Ei i (uniformDist : stdSimplex ℝ I) = 0 := by
  rw [disp_Ei A uniformDist i]
  simp only [uniformDist_val]
  -- ∑ j, A i j * (1/n) - 1/n = (1/n)·(∑ A i j) - 1/n = 1/n - 1/n = 0.
  have hcard_pos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hne : (Fintype.card I : ℝ) ≠ 0 := hcard_pos.ne'
  have hsum : (∑ j, A i j * (1 / (Fintype.card I : ℝ)))
            = (∑ j, A i j) / (Fintype.card I : ℝ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hsum, hA.rowSum]; ring

/-- For any column-player strategy `y`, picking the index where `y` is
minimal gives a non-negative row payoff under `disp A`. -/
private theorem disp_Ei_argmin_nonneg (A : I → I → ℝ) (hA : IsStochasticMatrix A)
    (y : stdSimplex ℝ I) :
    ∃ i, 0 ≤ (⟨disp A⟩ : MatrixGame I I ℝ).Ei i y := by
  -- Pick i₀ = argmin_j y.val j.
  obtain ⟨i₀, _, hi_min⟩ := Finset.exists_min_image Finset.univ y.val Finset.univ_nonempty
  -- hi_min : ∀ i ∈ univ, y.val i₀ ≤ y.val i.
  refine ⟨i₀, ?_⟩
  rw [disp_Ei A y i₀]
  -- (Ay)_{i₀} ≥ y_{i₀} via A_{i₀,j} ≥ 0, y_j ≥ y_{i₀}, ∑ A_{i₀,j} = 1.
  have hAy_ge : ∑ j, A i₀ j * y.val j ≥ y.val i₀ := by
    have hge : ∀ j, A i₀ j * y.val i₀ ≤ A i₀ j * y.val j := fun j =>
      mul_le_mul_of_nonneg_left (hi_min j (Finset.mem_univ _)) (hA.nonneg i₀ j)
    calc y.val i₀
        = (∑ j, A i₀ j) * y.val i₀ := by rw [hA.rowSum i₀, one_mul]
      _ = ∑ j, A i₀ j * y.val i₀ := by rw [Finset.sum_mul]
      _ ≤ ∑ j, A i₀ j * y.val j := Finset.sum_le_sum (fun j _ => hge j)
  linarith

/-! ### Value of the displacement game is zero -/

/-- The `disp A` matrix game's value is at most `0`. -/
private theorem disp_value_le_zero (A : I → I → ℝ) (hA : IsStochasticMatrix A) :
    (⟨disp A⟩ : MatrixGame I I ℝ).value ≤ 0 := by
  -- value = minimax ≤ guarantee_II uniform = 0.
  set game : MatrixGame I I ℝ := ⟨disp A⟩
  rw [game.value_eq_minimax]
  have hguarII : game.guarantee_II uniformDist = 0 := by
    show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => game.Ei i uniformDist) = 0
    have hall : ∀ i, game.Ei i (uniformDist : stdSimplex ℝ I) = 0 :=
      disp_Ei_uniform A hA
    rw [show (fun i => game.Ei i (uniformDist : stdSimplex ℝ I)) = fun _ => (0 : ℝ) from
      funext hall]
    simp
  -- minimax ≤ guarantee_II uniform via ciInf_le.
  have hbdd : BddBelow (Set.range (fun y : stdSimplex ℝ I => game.guarantee_II y)) := by
    obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow game.g
    exact ⟨C, by rintro r ⟨y, rfl⟩; exact hC y⟩
  have hle : game.minimax ≤ game.guarantee_II uniformDist := ciInf_le hbdd uniformDist
  linarith

/-- The `disp A` matrix game's value is at least `0`. -/
private theorem disp_value_ge_zero (A : I → I → ℝ) (hA : IsStochasticMatrix A) :
    0 ≤ (⟨disp A⟩ : MatrixGame I I ℝ).value := by
  -- value = minimax = ⨅_y guarantee_II y ≥ 0, since ∀ y, guarantee_II y ≥ 0 (argmin row).
  set game : MatrixGame I I ℝ := ⟨disp A⟩
  rw [game.value_eq_minimax]
  apply le_ciInf
  intro y
  obtain ⟨i₀, hi₀⟩ := disp_Ei_argmin_nonneg A hA y
  have hle : game.Ei i₀ y ≤ game.guarantee_II y := by
    show game.Ei i₀ y ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun i => game.Ei i y)
    exact Finset.le_sup' (fun i => game.Ei i y) (Finset.mem_univ _)
  linarith

/-- **The value of the displacement game is zero.** -/
private theorem disp_value_eq_zero (A : I → I → ℝ) (hA : IsStochasticMatrix A) :
    (⟨disp A⟩ : MatrixGame I I ℝ).value = 0 :=
  le_antisymm (disp_value_le_zero A hA) (disp_value_ge_zero A hA)

/-! ### Main theorem: existence of an invariant distribution -/

/-- **Every finite stochastic matrix has an invariant distribution**
[MFoGT Cor. 2.5.2]. -/
theorem exists_invariant_distribution (A : I → I → ℝ) (hA : IsStochasticMatrix A) :
    ∃ x : stdSimplex ℝ I, ∀ j, ∑ i, x.val i * A i j = x.val j := by
  -- Get a Nash-equilibrium pair for the displacement game.
  set game : MatrixGame I I ℝ := ⟨disp A⟩
  obtain ⟨x_star, y_star, hxx, hyy⟩ : ∃ xx yy,
      xx ∈ game.optimalRowStrategies ∧ yy ∈ game.optimalColumnStrategies := by
    obtain ⟨xx, yy, hnash⟩ := game.exists_mixed_nash_equilibrium
    obtain ⟨h1, h2⟩ := (game.optimal_pairs_iff_saddle_point xx yy).mpr hnash
    exact ⟨xx, yy, h1, h2⟩
  -- x_star secures the value against every column.
  have hxx_ge : ∀ j, game.Ej x_star j ≥ game.value := by
    intro j
    have h := (game.mem_optimalRowStrategies_iff_E_ge x_star).mp hxx (stdSimplex.pure j)
    have heq : game.E x_star (stdSimplex.pure j) = game.Ej x_star j := by
      show wsum x_star (fun i => wsum (stdSimplex.pure j) (game.g i))
        = wsum x_star (fun i => game.g i j)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show x_star.val i * wsum (stdSimplex.pure j) (game.g i) = x_star.val i * game.g i j
      rw [wsum_pure_apply]
    linarith
  -- value = 0, so game.Ej x_star j ≥ 0 = (x* A)_j − x*_j.
  have hval := disp_value_eq_zero A hA
  have hxx_nn : ∀ j, (∑ i, x_star.val i * A i j) - x_star.val j ≥ 0 := by
    intro j
    have h := hxx_ge j
    rw [hval] at h
    rw [disp_Ej A x_star j] at h
    exact h
  -- Sum: ∑ j ((x* A)_j − x*_j) = 0.
  have hsum : ∑ j, ((∑ i, x_star.val i * A i j) - x_star.val j) = 0 := by
    rw [Finset.sum_sub_distrib, hA.total_mass_preserved x_star.val, x_star.property.2]
    ring
  -- Each term ≥ 0 and sum = 0 ⇒ each = 0.
  refine ⟨x_star, fun j => ?_⟩
  have hzero_term : (∑ i, x_star.val i * A i j) - x_star.val j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hxx_nn j)).mp hsum j (Finset.mem_univ _)
  linarith

end MatrixGame

end EconCSLib.StrategicGame
