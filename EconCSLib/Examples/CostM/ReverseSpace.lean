/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.Ring

/-!
# EconCSLib.Examples.CostM.ReverseSpace

Naive list reverse instrumented with `CostM ℕ`, counting the cells
allocated by the `_ ++ [a]` chain. The cumulative allocation is Θ(n²) —
the canonical reason functional code prefers a tail-recursive reverse.

## Why this example

Companion to `GCD` (linear additive cost on a Nat-valued algorithm) and
`MemoFib` (idempotent Finset-valued cost). This file stays in `CostM ℕ`
but exhibits a **quadratic** cost on a linear-sized input — a meaningful
algorithmic content point that `CostM` is built precisely to record.

## Cost model

* Each recursive frame `naiveReverse (a :: as)` allocates `as.length + 1`
  cells via `rest ++ [a]`. We charge that many ticks per frame.
* Sequential composition (`bind`) sums costs additively in ℕ.

Cumulative cost across n frames: `1 + 2 + … + n = n (n + 1) / 2 = Θ(n²)`.

## Main results

* `naiveReverse_cost_le` — `(naiveReverse l).cost ≤ l.length * l.length`.
  Quadratic upper bound; loose by a factor of 2 vs. the exact `n(n+1)/2`.
-/

namespace ReverseSpace

/-- Naive `List A` reverse via `rest ++ [a]`, instrumented with `CostM ℕ`
charging `as.length + 1` per recursive frame (cells allocated by `++`). -/
def naiveReverse {A : Type} : List A → CostM ℕ (List A)
  | []      => pure []
  | a :: as => do
    ✓[as.length + 1] do
      let rest ← naiveReverse as
      pure (rest ++ [a])

/-- Cumulative `++` allocation is quadratic in input length. -/
theorem naiveReverse_cost_le {A : Type} (l : List A) :
    (naiveReverse l).cost ≤ l.length * l.length := by
  induction l with
  | nil =>
    simp [naiveReverse]
  | cons a as ih =>
    unfold naiveReverse
    simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
               List.length_cons, Nat.add_zero]
    have hsq : (as.length + 1) * (as.length + 1) =
               as.length * as.length + (2 * as.length + 1) := by ring
    rw [hsq]
    omega

end ReverseSpace
