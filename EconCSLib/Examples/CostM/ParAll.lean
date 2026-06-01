/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import Mathlib.Data.List.Basic
import Mathlib.Order.Nat

/-!
# EconCSLib.Examples.CostM.ParAll

Smallest possible demonstration of `CostM.parList`, the n-ary parallel
composition. Each operand runs independently; the joint cost is the
sup-semilattice join (`max` on `ℕ`) over all individual costs.

## Why this example

Companion to `ParSum` (which uses the binary `par` for a tree-shaped
reduction). This file shows the **flat n-ary fan-in**: any number of
data-independent operations executed in parallel, joined as a single
`CostM` step.

## Main results

* `parList_three_cost` — `parList [m₁, m₂, m₃]` with individual costs
  `3, 5, 2` has joint cost `5`.
* `parList_empty_cost` — the empty list has cost `0`.
* `parMap_cost_le` — for any list `xs` and unit-cost function, the parallel
  map has cost `≤ 1` regardless of `xs.length`.
-/

namespace ParAll

open CostM

/-- The three-operand example: max of `{3, 5, 2}` is `5`. -/
example :
    (parList
      [(do ✓[3] pure 1 : CostM ℕ ℕ),
       do ✓[5] pure 2,
       do ✓[2] pure 3]).cost = 5 := by
  rfl

/-- The empty list has cost `⊥ = 0` on `ℕ`. -/
example : (parList ([] : List (CostM ℕ Unit))).cost = 0 := by rfl

/-- For a homogeneous unit-cost map `f`, the n-ary parallel composition
has cost at most `1` for any input list — the parallel speedup is
unbounded in the input length. -/
theorem parMap_unit_cost_le (xs : List ℕ) :
    (parList (xs.map (fun _ => (do ✓ pure 0 : CostM ℕ ℕ)))).cost ≤ 1 := by
  induction xs with
  | nil => simp [parList]
  | cons x xs ih =>
    simp only [List.map_cons, cost_parList_cons]
    show max (do ✓ pure 0 : CostM ℕ ℕ).cost _ ≤ 1
    have h : ((do ✓ pure 0 : CostM ℕ ℕ)).cost = 1 := by
      simp [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure]
    rw [h]
    omega

end ParAll
