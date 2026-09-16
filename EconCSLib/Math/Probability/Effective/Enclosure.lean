/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Executable rational enclosures

This module provides the arithmetic foundation for effective probability
interfaces.  A `RatEnclosure` is a closed interval with rational endpoints,
and a `RatOracle` returns such an interval at every positive rational
tolerance.  The oracle contract bounds the interval width by the requested
tolerance; a separate semantic layer can state which real quantity lies in
all returned intervals.

All definitions here are executable and use exact rational arithmetic.
There is deliberately no dependency on measures, kernels, integration, or
real-valued semantics.

The oracle operations split an addition or subtraction tolerance equally
between their two inputs.  Scaling a nonzero oracle queries its input at
`tolerance / |factor|`; scaling by zero returns the exact zero oracle.
-/

namespace EffectiveProbability

/-- A nonempty closed interval with rational endpoints. -/
structure RatEnclosure where
  /-- Lower endpoint. -/
  lower : ℚ
  /-- Upper endpoint. -/
  upper : ℚ
  /-- The endpoint order certifying that the interval is nonempty. -/
  lower_le_upper : lower ≤ upper

namespace RatEnclosure

/-- Exact rational width of an enclosure. -/
def width (interval : RatEnclosure) : ℚ :=
  interval.upper - interval.lower

/-- A rational value belongs to an enclosure exactly when it lies between
the two endpoints. -/
def Contains (interval : RatEnclosure) (value : ℚ) : Prop :=
  interval.lower ≤ value ∧ value ≤ interval.upper

/-- The singleton enclosure containing an exact rational value. -/
def exact (value : ℚ) : RatEnclosure :=
  ⟨value, value, le_rfl⟩

/-- Pointwise negation of a rational enclosure. -/
def neg (interval : RatEnclosure) : RatEnclosure :=
  ⟨-interval.upper, -interval.lower, neg_le_neg interval.lower_le_upper⟩

/-- Minkowski sum of two rational enclosures. -/
def add (left right : RatEnclosure) : RatEnclosure :=
  ⟨left.lower + right.lower, left.upper + right.upper,
    add_le_add left.lower_le_upper right.lower_le_upper⟩

/-- Minkowski difference of two rational enclosures. -/
def sub (left right : RatEnclosure) : RatEnclosure :=
  left.add right.neg

/-- Scale an enclosure, reversing its endpoints when the factor is negative. -/
def scale (factor : ℚ) (interval : RatEnclosure) : RatEnclosure :=
  if hfactor : 0 ≤ factor then
    ⟨factor * interval.lower, factor * interval.upper,
      mul_le_mul_of_nonneg_left interval.lower_le_upper hfactor⟩
  else
    ⟨factor * interval.upper, factor * interval.lower,
      mul_le_mul_of_nonpos_left interval.lower_le_upper
        (le_of_lt (lt_of_not_ge hfactor))⟩

@[simp]
theorem exact_lower (value : ℚ) : (exact value).lower = value := rfl

@[simp]
theorem exact_upper (value : ℚ) : (exact value).upper = value := rfl

@[simp]
theorem neg_lower (interval : RatEnclosure) :
    interval.neg.lower = -interval.upper := rfl

@[simp]
theorem neg_upper (interval : RatEnclosure) :
    interval.neg.upper = -interval.lower := rfl

@[simp]
theorem add_lower (left right : RatEnclosure) :
    (left.add right).lower = left.lower + right.lower := rfl

@[simp]
theorem add_upper (left right : RatEnclosure) :
    (left.add right).upper = left.upper + right.upper := rfl

@[simp]
theorem sub_lower (left right : RatEnclosure) :
    (left.sub right).lower = left.lower - right.upper := by
  simp [sub, sub_eq_add_neg]

@[simp]
theorem sub_upper (left right : RatEnclosure) :
    (left.sub right).upper = left.upper - right.lower := by
  simp [sub, sub_eq_add_neg]

@[simp]
theorem scale_lower_of_nonneg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : 0 ≤ factor) :
    (interval.scale factor).lower = factor * interval.lower := by
  simp [scale, hfactor]

@[simp]
theorem scale_upper_of_nonneg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : 0 ≤ factor) :
    (interval.scale factor).upper = factor * interval.upper := by
  simp [scale, hfactor]

@[simp]
theorem scale_lower_of_neg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : factor < 0) :
    (interval.scale factor).lower = factor * interval.upper := by
  simp [scale, not_le.mpr hfactor]

@[simp]
theorem scale_upper_of_neg (interval : RatEnclosure) {factor : ℚ}
    (hfactor : factor < 0) :
    (interval.scale factor).upper = factor * interval.lower := by
  simp [scale, not_le.mpr hfactor]

/-- Every certified enclosure has nonnegative width. -/
theorem width_nonneg (interval : RatEnclosure) : 0 ≤ interval.width := by
  exact sub_nonneg.mpr interval.lower_le_upper

@[simp]
theorem width_exact (value : ℚ) : (exact value).width = 0 := by
  simp [width]

@[simp]
theorem width_neg (interval : RatEnclosure) :
    interval.neg.width = interval.width := by
  simp [width, neg, sub_eq_add_neg]
  ring

@[simp]
theorem width_add (left right : RatEnclosure) :
    (left.add right).width = left.width + right.width := by
  simp [width, add]
  ring

@[simp]
theorem width_sub (left right : RatEnclosure) :
    (left.sub right).width = left.width + right.width := by
  simp [sub]

@[simp]
theorem width_scale (factor : ℚ) (interval : RatEnclosure) :
    (interval.scale factor).width = |factor| * interval.width := by
  by_cases hfactor : 0 ≤ factor
  · simp [scale, width, hfactor, abs_of_nonneg hfactor]
    ring
  · have hnegative : factor < 0 := lt_of_not_ge hfactor
    simp [scale, width, hfactor, abs_of_neg hnegative]
    ring

@[simp]
theorem contains_exact (value : ℚ) : (exact value).Contains value := by
  simp [Contains]

/-- Negation preserves interval membership. -/
theorem Contains.neg {interval : RatEnclosure} {value : ℚ}
    (hvalue : interval.Contains value) :
    interval.neg.Contains (-value) := by
  rcases hvalue with ⟨hlower, hupper⟩
  exact ⟨neg_le_neg hupper, neg_le_neg hlower⟩

/-- Addition preserves interval membership. -/
theorem Contains.add {left right : RatEnclosure} {x y : ℚ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.add right).Contains (x + y) := by
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

/-- Subtraction preserves interval membership. -/
theorem Contains.sub {left right : RatEnclosure} {x y : ℚ}
    (hx : left.Contains x) (hy : right.Contains y) :
    (left.sub right).Contains (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

/-- Rational scaling preserves interval membership. -/
theorem Contains.scale {interval : RatEnclosure} {value factor : ℚ}
    (hvalue : interval.Contains value) :
    (interval.scale factor).Contains (factor * value) := by
  by_cases hfactor : 0 ≤ factor
  · simpa [Contains, scale, hfactor] using
      (show factor * interval.lower ≤ factor * value ∧
          factor * value ≤ factor * interval.upper from
        ⟨mul_le_mul_of_nonneg_left hvalue.1 hfactor,
          mul_le_mul_of_nonneg_left hvalue.2 hfactor⟩)
  · have hnegative : factor < 0 := lt_of_not_ge hfactor
    have hnonpos : factor ≤ 0 := hnegative.le
    change (interval.scale factor).lower ≤ factor * value ∧
      factor * value ≤ (interval.scale factor).upper
    rw [scale_lower_of_neg interval hnegative,
      scale_upper_of_neg interval hnegative]
    exact ⟨mul_le_mul_of_nonpos_left hvalue.2 hnonpos,
      mul_le_mul_of_nonpos_left hvalue.1 hnonpos⟩

end RatEnclosure

/-- An executable oracle returning an interval of width at most every
requested positive rational tolerance.  Which mathematical value the oracle
represents is intentionally specified outside this data structure. -/
structure RatOracle where
  /-- Query the oracle at a positive rational tolerance. -/
  query : (tolerance : ℚ) → 0 < tolerance → RatEnclosure
  /-- Every returned interval is at most as wide as requested. -/
  query_width_le : ∀ tolerance hpositive,
    (query tolerance hpositive).width ≤ tolerance

namespace RatOracle

/-- A purely rational correctness predicate: every query contains `value`.
The semantic compatibility layer supplies the analogous real-valued
representation predicate. -/
def Encloses (oracle : RatOracle) (value : ℚ) : Prop :=
  ∀ tolerance hpositive, (oracle.query tolerance hpositive).Contains value

/-- The constant oracle for an exact rational value. -/
def exact (value : ℚ) : RatOracle where
  query := fun _ _ => RatEnclosure.exact value
  query_width_le := by
    intro tolerance hpositive
    simpa using hpositive.le

/-- Negate every interval returned by an oracle. -/
def neg (oracle : RatOracle) : RatOracle where
  query := fun tolerance hpositive =>
    (oracle.query tolerance hpositive).neg
  query_width_le := by
    intro tolerance hpositive
    simpa using oracle.query_width_le tolerance hpositive

private theorem half_pos {tolerance : ℚ} (hpositive : 0 < tolerance) :
    0 < tolerance / 2 := by
  linarith

/-- Add two oracles, assigning half of the requested tolerance to each
operand. -/
def add (left right : RatOracle) : RatOracle where
  query := fun tolerance hpositive =>
    (left.query (tolerance / 2) (half_pos hpositive)).add
      (right.query (tolerance / 2) (half_pos hpositive))
  query_width_le := by
    intro tolerance hpositive
    rw [RatEnclosure.width_add]
    have hleft := left.query_width_le (tolerance / 2) (half_pos hpositive)
    have hright := right.query_width_le (tolerance / 2) (half_pos hpositive)
    linarith

/-- Subtract two oracles, assigning half of the requested tolerance to each
operand. -/
def sub (left right : RatOracle) : RatOracle :=
  left.add right.neg

private theorem div_abs_pos {tolerance factor : ℚ}
    (hpositive : 0 < tolerance) (hfactor : factor ≠ 0) :
    0 < tolerance / |factor| :=
  div_pos hpositive (abs_pos.mpr hfactor)

/-- Scale an oracle.  A nonzero factor rescales the input tolerance by its
absolute value; a zero factor returns exact zero without querying the input. -/
def scale (factor : ℚ) (oracle : RatOracle) : RatOracle := by
  by_cases hfactor : factor = 0
  · exact exact 0
  · refine
      { query := fun tolerance hpositive =>
          (oracle.query (tolerance / |factor|)
            (div_abs_pos hpositive hfactor)).scale factor
        query_width_le := ?_ }
    intro tolerance hpositive
    rw [RatEnclosure.width_scale]
    calc
      |factor| *
          (oracle.query (tolerance / |factor|)
            (div_abs_pos hpositive hfactor)).width ≤
          |factor| * (tolerance / |factor|) :=
        mul_le_mul_of_nonneg_left
          (oracle.query_width_le (tolerance / |factor|)
            (div_abs_pos hpositive hfactor)) (abs_nonneg factor)
      _ = tolerance := by
        field_simp

@[simp]
theorem exact_query (value tolerance : ℚ) (hpositive : 0 < tolerance) :
    (exact value).query tolerance hpositive = RatEnclosure.exact value :=
  rfl

@[simp]
theorem neg_query (oracle : RatOracle) (tolerance : ℚ)
    (hpositive : 0 < tolerance) :
    oracle.neg.query tolerance hpositive =
      (oracle.query tolerance hpositive).neg :=
  rfl

@[simp]
theorem add_query (left right : RatOracle) (tolerance : ℚ)
    (hpositive : 0 < tolerance) :
    (left.add right).query tolerance hpositive =
      (left.query (tolerance / 2) (half_pos hpositive)).add
        (right.query (tolerance / 2) (half_pos hpositive)) :=
  rfl

@[simp]
theorem sub_query (left right : RatOracle) (tolerance : ℚ)
    (hpositive : 0 < tolerance) :
    (left.sub right).query tolerance hpositive =
      (left.query (tolerance / 2) (half_pos hpositive)).sub
        (right.query (tolerance / 2) (half_pos hpositive)) := by
  rfl

@[simp]
theorem scale_zero (oracle : RatOracle) : oracle.scale 0 = exact 0 := by
  simp [RatOracle.scale]

/-- A nonzero scale query uses the rescaled input tolerance. -/
theorem scale_query_of_ne (oracle : RatOracle) {factor tolerance : ℚ}
    (hfactor : factor ≠ 0) (hpositive : 0 < tolerance) :
    (oracle.scale factor).query tolerance hpositive =
      (oracle.query (tolerance / |factor|)
        (div_abs_pos hpositive hfactor)).scale factor := by
  simp [RatOracle.scale, hfactor]

/-- The exact rational oracle encloses its value. -/
theorem exact_encloses (value : ℚ) : (exact value).Encloses value := by
  intro tolerance hpositive
  exact RatEnclosure.contains_exact value

/-- Correct rational enclosure is preserved by oracle negation. -/
theorem Encloses.neg {oracle : RatOracle} {value : ℚ}
    (hvalue : oracle.Encloses value) :
    oracle.neg.Encloses (-value) := by
  intro tolerance hpositive
  exact (hvalue tolerance hpositive).neg

/-- Correct rational enclosure is preserved by oracle addition. -/
theorem Encloses.add {left right : RatOracle} {x y : ℚ}
    (hx : left.Encloses x) (hy : right.Encloses y) :
    (left.add right).Encloses (x + y) := by
  intro tolerance hpositive
  exact (hx (tolerance / 2) (half_pos hpositive)).add
    (hy (tolerance / 2) (half_pos hpositive))

/-- Correct rational enclosure is preserved by oracle subtraction. -/
theorem Encloses.sub {left right : RatOracle} {x y : ℚ}
    (hx : left.Encloses x) (hy : right.Encloses y) :
    (left.sub right).Encloses (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

/-- Correct rational enclosure is preserved by oracle scaling. -/
theorem Encloses.scale {oracle : RatOracle} {value : ℚ}
    (hvalue : oracle.Encloses value) (factor : ℚ) :
    (oracle.scale factor).Encloses (factor * value) := by
  intro tolerance hpositive
  by_cases hfactor : factor = 0
  · subst factor
    simp
  · rw [scale_query_of_ne oracle hfactor hpositive]
    exact (hvalue (tolerance / |factor|)
      (div_abs_pos hpositive hfactor)).scale

end RatOracle

end EffectiveProbability
