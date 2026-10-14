/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Rat.Lemmas

/-!
# Exact probabilities of finite rational interval unions

This module gives a pure executable reference algorithm for the probability
of a finite union of closed rational intervals under the uniform law on the
unit interval. Bounds may overlap, repeat, lie outside `[0, 1]`, be reversed,
or describe a singleton. The algorithm clips individual lengths and uses
inclusion-exclusion; it never compares arbitrary real numbers.

The set-theoretic interpretation and equality with unit-interval volume live
in `RationalIntervalUnion.Volume`, so this module has no measure dependency.
The recursive algorithm has exponential worst-case cost in the number of
input intervals and is intended as an exact specification-level evaluator.
-/

namespace RationalIntervalUnion

/-- A pair of rational lower and upper endpoints. Reversed endpoints are
permitted and denote an empty interval after interpretation. -/
abbrev Bounds := ℚ × ℚ

/-- Exact clipped length of one closed rational interval inside `[0, 1]`. -/
def intervalMass (bounds : Bounds) : ℚ :=
  max 0 (min 1 bounds.2 - max 0 bounds.1)

/-- Intersection keeps the greater lower bound and the smaller upper bound. -/
def intersect (left right : Bounds) : Bounds :=
  (max left.1 right.1, min left.2 right.2)

/-- Exact unit-interval probability of a finite union by inclusion-exclusion.
Every recursive call operates on a strictly shorter list. -/
def probability : List Bounds → ℚ
  | [] => 0
  | head :: tail => intervalMass head + probability tail -
      probability (tail.map (intersect head))
termination_by intervals => intervals.length

end RationalIntervalUnion
