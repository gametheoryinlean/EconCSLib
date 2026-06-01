/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# EconCSLib.Examples.StrategicGame.TwoByTwo

For a 2×2 matrix game

```
      L    R
T   [ a    b ]
B   [ c    d ]
```

either there is a pair of pure optimal strategies, or the completely
mixed optimal strategies give value

$$
  \mathrm{val} = \frac{a d - b c}{a + d - b - c}.
$$

[MFoGT Example 2.6.3].

This file formalises the **mixed case**: under hypotheses that ensure
the mixed strategies are valid probability vectors (each entry ≥ 0),
the value is the displayed quotient.

## Sufficient hypotheses

`0 < a + d - b - c` together with `b ≤ a`, `c ≤ a`, `b ≤ d`, `c ≤ d`
guarantees that `p := ((d-c)/denom, (a-b)/denom)` is row-feasible and
`q := ((d-b)/denom, (a-c)/denom)` is column-feasible. Both players
then realise value `(a*d - b*c)/(a + d - b - c)`.
-/

namespace EconCSLib.StrategicGame.Examples

/-- 2×2 matrix game payoff. -/
def twoByTwo (a b c d : ℝ) : MatrixGame (Fin 2) (Fin 2) ℝ where
  g := !![a, b; c, d]

@[simp] theorem twoByTwo_g_00 (a b c d : ℝ) : (twoByTwo a b c d).g 0 0 = a := by
  simp [twoByTwo]
@[simp] theorem twoByTwo_g_01 (a b c d : ℝ) : (twoByTwo a b c d).g 0 1 = b := by
  simp [twoByTwo]
@[simp] theorem twoByTwo_g_10 (a b c d : ℝ) : (twoByTwo a b c d).g 1 0 = c := by
  simp [twoByTwo]
@[simp] theorem twoByTwo_g_11 (a b c d : ℝ) : (twoByTwo a b c d).g 1 1 = d := by
  simp [twoByTwo]

/-- Row player's completely-mixed strategy `((d-c)/denom, (a-b)/denom)`. -/
noncomputable def twoByTwoRowMixed
    (a b c d : ℝ) (hdenom : 0 < a + d - b - c)
    (hab : b ≤ a) (hdc : c ≤ d) : stdSimplex ℝ (Fin 2) :=
  ⟨![(d - c) / (a + d - b - c), (a - b) / (a + d - b - c)],
    by
      intro i
      fin_cases i
      · exact div_nonneg (by linarith) hdenom.le
      · exact div_nonneg (by linarith) hdenom.le,
    by
      rw [Fin.sum_univ_two]
      show (d - c) / (a + d - b - c) + (a - b) / (a + d - b - c) = 1
      rw [← add_div]
      rw [show (d - c) + (a - b) = a + d - b - c from by ring]
      exact div_self hdenom.ne'⟩

/-- Column player's completely-mixed strategy `((d-b)/denom, (a-c)/denom)`. -/
noncomputable def twoByTwoColumnMixed
    (a b c d : ℝ) (hdenom : 0 < a + d - b - c)
    (hac : c ≤ a) (hdb : b ≤ d) : stdSimplex ℝ (Fin 2) :=
  ⟨![(d - b) / (a + d - b - c), (a - c) / (a + d - b - c)],
    by
      intro j
      fin_cases j
      · exact div_nonneg (by linarith) hdenom.le
      · exact div_nonneg (by linarith) hdenom.le,
    by
      rw [Fin.sum_univ_two]
      show (d - b) / (a + d - b - c) + (a - c) / (a + d - b - c) = 1
      rw [← add_div]
      rw [show (d - b) + (a - c) = a + d - b - c from by ring]
      exact div_self hdenom.ne'⟩

/-- Mixed-case value `(a*d - b*c) / (a + d - b - c)`. -/
noncomputable def twoByTwoMixedValue (a b c d : ℝ) : ℝ :=
  (a * d - b * c) / (a + d - b - c)

/-- Row-mixed strategy guarantees value `(ad-bc)/denom` against either column. -/
theorem twoByTwo_row_guarantee
    (a b c d : ℝ) (hdenom : 0 < a + d - b - c)
    (hab : b ≤ a) (hdc : c ≤ d) :
    ∀ j, twoByTwoMixedValue a b c d
        ≤ (twoByTwo a b c d).Ej (twoByTwoRowMixed a b c d hdenom hab hdc) j := by
  intro j
  show twoByTwoMixedValue a b c d ≤ ∑ i,
    (twoByTwoRowMixed a b c d hdenom hab hdc).val i * (twoByTwo a b c d).g i j
  rw [Fin.sum_univ_two]
  fin_cases j
  · show (a * d - b * c) / (a + d - b - c) ≤
      (twoByTwoRowMixed a b c d hdenom hab hdc).val 0 * (twoByTwo a b c d).g 0 0
      + (twoByTwoRowMixed a b c d hdenom hab hdc).val 1 * (twoByTwo a b c d).g 1 0
    show (a * d - b * c) / (a + d - b - c) ≤
      ((d - c) / (a + d - b - c)) * a + ((a - b) / (a + d - b - c)) * c
    rw [show ((d - c) / (a + d - b - c)) * a + ((a - b) / (a + d - b - c)) * c
        = ((d - c) * a + (a - b) * c) / (a + d - b - c) from by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]]
    apply le_of_eq; congr 1; ring
  · show (a * d - b * c) / (a + d - b - c) ≤
      (twoByTwoRowMixed a b c d hdenom hab hdc).val 0 * (twoByTwo a b c d).g 0 1
      + (twoByTwoRowMixed a b c d hdenom hab hdc).val 1 * (twoByTwo a b c d).g 1 1
    show (a * d - b * c) / (a + d - b - c) ≤
      ((d - c) / (a + d - b - c)) * b + ((a - b) / (a + d - b - c)) * d
    rw [show ((d - c) / (a + d - b - c)) * b + ((a - b) / (a + d - b - c)) * d
        = ((d - c) * b + (a - b) * d) / (a + d - b - c) from by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]]
    apply le_of_eq; congr 1; ring

/-- Column-mixed strategy caps payoff at `(ad-bc)/denom` against either row. -/
theorem twoByTwo_column_guarantee
    (a b c d : ℝ) (hdenom : 0 < a + d - b - c)
    (hac : c ≤ a) (hdb : b ≤ d) :
    ∀ i, (twoByTwo a b c d).Ei i (twoByTwoColumnMixed a b c d hdenom hac hdb)
        ≤ twoByTwoMixedValue a b c d := by
  intro i
  show ∑ j, (twoByTwoColumnMixed a b c d hdenom hac hdb).val j * (twoByTwo a b c d).g i j
    ≤ twoByTwoMixedValue a b c d
  rw [Fin.sum_univ_two]
  fin_cases i
  · show (twoByTwoColumnMixed a b c d hdenom hac hdb).val 0 * (twoByTwo a b c d).g 0 0
      + (twoByTwoColumnMixed a b c d hdenom hac hdb).val 1 * (twoByTwo a b c d).g 0 1
      ≤ twoByTwoMixedValue a b c d
    show ((d - b) / (a + d - b - c)) * a + ((a - c) / (a + d - b - c)) * b
      ≤ (a * d - b * c) / (a + d - b - c)
    rw [show ((d - b) / (a + d - b - c)) * a + ((a - c) / (a + d - b - c)) * b
        = ((d - b) * a + (a - c) * b) / (a + d - b - c) from by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]]
    apply le_of_eq; congr 1; ring
  · show (twoByTwoColumnMixed a b c d hdenom hac hdb).val 0 * (twoByTwo a b c d).g 1 0
      + (twoByTwoColumnMixed a b c d hdenom hac hdb).val 1 * (twoByTwo a b c d).g 1 1
      ≤ twoByTwoMixedValue a b c d
    show ((d - b) / (a + d - b - c)) * c + ((a - c) / (a + d - b - c)) * d
      ≤ (a * d - b * c) / (a + d - b - c)
    rw [show ((d - b) / (a + d - b - c)) * c + ((a - c) / (a + d - b - c)) * d
        = ((d - b) * c + (a - c) * d) / (a + d - b - c) from by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]]
    apply le_of_eq; congr 1; ring

/-- **Two-by-two value formula** [MFoGT Ex. 2.6.3]. Under the
"completely mixed" hypotheses (`0 < denom` and the four monotonicity
conditions), the value of the 2×2 game is `(a*d - b*c)/(a + d - b - c)`. -/
theorem twoByTwo_value
    (a b c d : ℝ) (hdenom : 0 < a + d - b - c)
    (hab : b ≤ a) (hac : c ≤ a) (hdb : b ≤ d) (hdc : c ≤ d) :
    (twoByTwo a b c d).value = twoByTwoMixedValue a b c d := by
  symm
  apply (twoByTwo a b c d).common_guarantee_eq_value
  · exact ⟨twoByTwoRowMixed a b c d hdenom hab hdc,
           twoByTwo_row_guarantee a b c d hdenom hab hdc⟩
  · exact ⟨twoByTwoColumnMixed a b c d hdenom hac hdb,
           twoByTwo_column_guarantee a b c d hdenom hac hdb⟩

end EconCSLib.StrategicGame.Examples
