/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# EconCSLib.Examples.StrategicGame.ThreeByTwo

[MFoGT §2.8, Exercise 5]:

```
        L     R
T   [   3    -1  ]
M   [   0     0  ]
B   [  -2     1  ]
```

The middle row `M` is strictly dominated by `0.49 · T + 0.51 · B`, so the
game reduces to the 2×2 sub-game on `{T, B}`, which has value `1/7`.

* Value: `val(A) = 1/7`.
* Row optimum: `x* = (3/7, 0, 4/7)`.
* Column optimum: `y* = (2/7, 5/7)`.
-/

namespace EconCSLib.StrategicGame.Examples

/-- The 3×2 worked example matrix. -/
def threeByTwoExample : MatrixGame (Fin 3) (Fin 2) ℝ where
  g := !![3, -1; 0, 0; -2, 1]

@[simp] theorem threeByTwoExample_g_00 : threeByTwoExample.g 0 0 = 3 := by
  simp [threeByTwoExample]
@[simp] theorem threeByTwoExample_g_01 : threeByTwoExample.g 0 1 = -1 := by
  simp [threeByTwoExample]
@[simp] theorem threeByTwoExample_g_10 : threeByTwoExample.g 1 0 = 0 := by
  simp [threeByTwoExample]
@[simp] theorem threeByTwoExample_g_11 : threeByTwoExample.g 1 1 = 0 := by
  simp [threeByTwoExample]
@[simp] theorem threeByTwoExample_g_20 : threeByTwoExample.g 2 0 = -2 := by
  simp [threeByTwoExample]
@[simp] theorem threeByTwoExample_g_21 : threeByTwoExample.g 2 1 = 1 := by
  simp [threeByTwoExample]

/-- Row player's optimal strategy `(3/7, 0, 4/7)`. -/
noncomputable def threeByTwoRowOpt : stdSimplex ℝ (Fin 3) :=
  ⟨![3 / 7, 0, 4 / 7],
    fun i => by fin_cases i <;> norm_num,
    by rw [Fin.sum_univ_three]; show (3 : ℝ) / 7 + 0 + 4 / 7 = 1; norm_num⟩

@[simp] theorem threeByTwoRowOpt_val_0 : threeByTwoRowOpt.val 0 = 3 / 7 := by
  simp [threeByTwoRowOpt]
@[simp] theorem threeByTwoRowOpt_val_1 : threeByTwoRowOpt.val 1 = 0 := by
  simp [threeByTwoRowOpt]
@[simp] theorem threeByTwoRowOpt_val_2 : threeByTwoRowOpt.val 2 = 4 / 7 := by
  simp [threeByTwoRowOpt]

/-- Column player's optimal strategy `(2/7, 5/7)`. -/
noncomputable def threeByTwoColOpt : stdSimplex ℝ (Fin 2) :=
  ⟨![2 / 7, 5 / 7],
    fun j => by fin_cases j <;> norm_num,
    by rw [Fin.sum_univ_two]; show (2 : ℝ) / 7 + 5 / 7 = 1; norm_num⟩

@[simp] theorem threeByTwoColOpt_val_0 : threeByTwoColOpt.val 0 = 2 / 7 := by
  simp [threeByTwoColOpt]
@[simp] theorem threeByTwoColOpt_val_1 : threeByTwoColOpt.val 1 = 5 / 7 := by
  simp [threeByTwoColOpt]

/-- Player 1's optimal strategy guarantees `1/7` against either column. -/
theorem threeByTwo_row_guarantee :
    ∀ j, (1 : ℝ) / 7 ≤ threeByTwoExample.Ej threeByTwoRowOpt j := by
  intro j
  show (1 : ℝ) / 7 ≤ ∑ i, threeByTwoRowOpt.val i * threeByTwoExample.g i j
  rw [Fin.sum_univ_three]
  fin_cases j
  · show (1 : ℝ) / 7 ≤ threeByTwoRowOpt.val 0 * threeByTwoExample.g 0 0
                      + threeByTwoRowOpt.val 1 * threeByTwoExample.g 1 0
                      + threeByTwoRowOpt.val 2 * threeByTwoExample.g 2 0
    simp; try norm_num
  · show (1 : ℝ) / 7 ≤ threeByTwoRowOpt.val 0 * threeByTwoExample.g 0 1
                      + threeByTwoRowOpt.val 1 * threeByTwoExample.g 1 1
                      + threeByTwoRowOpt.val 2 * threeByTwoExample.g 2 1
    simp; try norm_num

/-- Player 2's optimal strategy caps payoff at `1/7` against every pure row. -/
theorem threeByTwo_column_guarantee :
    ∀ i, threeByTwoExample.Ei i threeByTwoColOpt ≤ (1 : ℝ) / 7 := by
  intro i
  show ∑ j, threeByTwoColOpt.val j * threeByTwoExample.g i j ≤ (1 : ℝ) / 7
  rw [Fin.sum_univ_two]
  fin_cases i
  · show threeByTwoColOpt.val 0 * threeByTwoExample.g 0 0
        + threeByTwoColOpt.val 1 * threeByTwoExample.g 0 1 ≤ (1 : ℝ) / 7
    simp; try norm_num
  · show threeByTwoColOpt.val 0 * threeByTwoExample.g 1 0
        + threeByTwoColOpt.val 1 * threeByTwoExample.g 1 1 ≤ (1 : ℝ) / 7
    simp; try norm_num
  · show threeByTwoColOpt.val 0 * threeByTwoExample.g 2 0
        + threeByTwoColOpt.val 1 * threeByTwoExample.g 2 1 ≤ (1 : ℝ) / 7
    simp; try norm_num

/-- **Three-by-two example value** [MFoGT §2.8, Exercise 5]. -/
theorem threeByTwoExample_value : threeByTwoExample.value = 1 / 7 := by
  symm
  apply threeByTwoExample.common_guarantee_eq_value
  · exact ⟨threeByTwoRowOpt, threeByTwo_row_guarantee⟩
  · exact ⟨threeByTwoColOpt, threeByTwo_column_guarantee⟩

end EconCSLib.StrategicGame.Examples
