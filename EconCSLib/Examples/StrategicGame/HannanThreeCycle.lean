/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NoRegret.EmpiricalDistribution
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Hannan consistency does not imply internal consistency

This module formalizes the three-action zero-sum game in
[MFoGT, Example 7.3.14]. The distribution assigning mass `1/3` to each
diagonal action pair lies in both players' Hannan sets and has payoff equal to
the value, but violates a row-player internal-regret inequality.
-/

open Finset BigOperators

namespace StrategicGame.Examples

/-- The cyclic antisymmetric payoff matrix from MFoGT Example 7.3.14. -/
def hannanThreeCyclePayoff : Fin 3 → Fin 3 → ℝ :=
  !![0, 1, -1; -1, 0, 1; 1, -1, 0]

@[simp] theorem hannanThreeCyclePayoff_00 : hannanThreeCyclePayoff 0 0 = 0 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_01 : hannanThreeCyclePayoff 0 1 = 1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_02 : hannanThreeCyclePayoff 0 2 = -1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_10 : hannanThreeCyclePayoff 1 0 = -1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_11 : hannanThreeCyclePayoff 1 1 = 0 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_12 : hannanThreeCyclePayoff 1 2 = 1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_20 : hannanThreeCyclePayoff 2 0 = 1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_21 : hannanThreeCyclePayoff 2 1 = -1 := by
  simp [hannanThreeCyclePayoff]
@[simp] theorem hannanThreeCyclePayoff_22 : hannanThreeCyclePayoff 2 2 = 0 := by
  simp [hannanThreeCyclePayoff]

/-- The example distribution: probability `1/3` on each diagonal pair. -/
noncomputable def hannanThreeCycleDiagonal :
    JointDistribution (Fin 3) (Fin 3) where
  val s := if s.1 = s.2 then (1 : ℝ) / 3 else 0
  property := by
    constructor
    · intro s
      by_cases h : s.1 = s.2 <;> simp [h]
    · rw [Fintype.sum_prod_type, Fin.sum_univ_three]
      simp only [Fin.sum_univ_three]
      simp
      norm_num

@[simp] theorem hannanThreeCycleDiagonal_val (i j : Fin 3) :
    hannanThreeCycleDiagonal.val (i, j) = if i = j then (1 : ℝ) / 3 else 0 := rfl

/-- The diagonal distribution has zero expected payoff. -/
theorem hannanThreeCycleDiagonal_payoff :
    jointPayoff hannanThreeCyclePayoff hannanThreeCycleDiagonal = 0 := by
  unfold jointPayoff
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [Fin.sum_univ_three]
  simp

/-- The row player satisfies every Hannan inequality at the diagonal
distribution. -/
theorem hannanThreeCycleDiagonal_mem_rowHannan :
    hannanThreeCycleDiagonal ∈ HannanSet hannanThreeCyclePayoff := by
  intro k
  fin_cases k <;>
    simp [payoffAgainstOpponentMarginal, hannanThreeCycleDiagonal_payoff,
      Fin.sum_univ_three]

/-- The minimizing column player also satisfies every Hannan inequality at the
diagonal distribution. -/
theorem hannanThreeCycleDiagonal_mem_columnHannan :
    hannanThreeCycleDiagonal ∈ ColumnHannanSet hannanThreeCyclePayoff := by
  intro l
  fin_cases l <;>
    simp [payoffAgainstPlayerMarginal, hannanThreeCycleDiagonal_payoff,
      Fin.sum_univ_three]

/-- The generic two-Hannan-set theorem identifies the value and optimal
marginals in the concrete example. -/
theorem hannanThreeCycleDiagonal_marginals_optimal_and_payoff_eq_value :
    jointFirstMarginal hannanThreeCycleDiagonal ∈
        (⟨hannanThreeCyclePayoff⟩ : MatrixGame (Fin 3) (Fin 3) ℝ).optimalRowStrategies ∧
      jointSecondMarginal hannanThreeCycleDiagonal ∈
        (⟨hannanThreeCyclePayoff⟩ : MatrixGame (Fin 3) (Fin 3) ℝ).optimalColumnStrategies ∧
      (⟨hannanThreeCyclePayoff⟩ : MatrixGame (Fin 3) (Fin 3) ℝ).E
          (jointFirstMarginal hannanThreeCycleDiagonal)
          (jointSecondMarginal hannanThreeCycleDiagonal) =
        jointPayoff hannanThreeCyclePayoff hannanThreeCycleDiagonal ∧
      jointPayoff hannanThreeCyclePayoff hannanThreeCycleDiagonal =
        (⟨hannanThreeCyclePayoff⟩ : MatrixGame (Fin 3) (Fin 3) ℝ).value :=
  hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value
    hannanThreeCyclePayoff hannanThreeCycleDiagonal
    hannanThreeCycleDiagonal_mem_rowHannan
    hannanThreeCycleDiagonal_mem_columnHannan

/-- The example is not internally consistent for the row player: replacing
announced/played row `0` by row `2` gains `1/3`. -/
theorem hannanThreeCycleDiagonal_comparisonGain_zero_two :
    comparisonGain hannanThreeCyclePayoff hannanThreeCycleDiagonal 0 2 = 1 / 3 := by
  simp [comparisonGain]

/-- Consequently the example distribution is outside the row player's
no-comparison-regret set, despite satisfying both Hannan conditions. -/
theorem hannanThreeCycleDiagonal_not_mem_noCRegretSet :
    hannanThreeCycleDiagonal ∉ NoCRegretSet hannanThreeCyclePayoff := by
  intro h
  have hle := h (0 : Fin 3) (2 : Fin 3)
  rw [hannanThreeCycleDiagonal_comparisonGain_zero_two] at hle
  norm_num at hle

end StrategicGame.Examples
