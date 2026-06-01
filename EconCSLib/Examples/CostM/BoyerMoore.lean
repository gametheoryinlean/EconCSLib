/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Cells

/-!
# EconCSLib.Examples.CostM.BoyerMoore

Boyer-Moore majority-vote, instrumented with `CostM Cells` to prove a
**constant**-space bound: regardless of input length, the peak working set
is `2` cells (one candidate + one counter).

## Algorithm

A single left-to-right pass over the list. Two pieces of state — a current
"candidate" element and a non-negative "counter":

* on each element matching the candidate, bump the counter;
* otherwise, decrement the counter — and if the counter was already zero,
  promote the new element to candidate with counter `1`.

The algorithm returns `some m` whenever there is a strict majority (more
than half the list), and an arbitrary element otherwise.

## Cost model

* `alloc 2` once at the start declares the two-slot working set.
* The recursive `loop` overwrites those slots; it ticks nothing.
* `free 2` at the end balances the allocation.

The fact that `loop` does **not** call any `tick` is the central point —
this is what makes the peak constant.

## Main results

* `loop_cost` — the inner loop contributes zero cost.
* `majority_peak_le` — `(majority xs).cost.peak ≤ 2`, independent of `xs`.

Functional correctness (that `majority` actually returns the majority
when one exists) is intentionally not proven here: the design point is
that complexity and correctness live on different fields (`.cost` vs
`.ret`) and decouple cleanly.
-/

namespace BoyerMoore

variable {A : Type*} [DecidableEq A]

/-- Boyer-Moore majority vote in `CostM Cells`. The two `alloc`/`free` ticks
declare a constant two-slot working set; the loop itself ticks nothing. -/
def majority : List A → CostM Cells (Option A)
  | []      => pure none
  | x :: xs => do
    ✓[Cells.alloc 2] do
      let result ← loop x 1 xs
      ✓[Cells.free 2] pure result
where
  /-- Single-pass loop carrying the current candidate and counter as
  parameters — no allocation, no ticks. -/
  loop (cand : A) (cnt : ℕ) : List A → CostM Cells (Option A)
    | []      => pure (some cand)
    | y :: ys =>
      if y = cand then loop cand (cnt + 1) ys
      else if cnt = 0 then loop y 1 ys
      else loop cand (cnt - 1) ys

/-- The loop has zero cost: it overwrites the two slots without allocating. -/
theorem loop_cost (cand : A) (cnt : ℕ) (xs : List A) :
    (majority.loop cand cnt xs).cost = 0 := by
  induction xs generalizing cand cnt with
  | nil => simp [majority.loop]
  | cons y ys ih =>
    simp only [majority.loop]
    split_ifs
    · exact ih cand (cnt + 1)
    · exact ih y 1
    · exact ih cand (cnt - 1)

/-- **Constant-space bound**: the peak working set of `majority` is at most
two cells, regardless of input length. -/
theorem majority_peak_le (xs : List A) : (majority xs).cost.peak ≤ 2 := by
  cases xs with
  | nil => simp [majority]
  | cons x xs =>
    simp only [majority, CostM.cost_bind, CostM.cost_tick, CostM.cost_pure]
    rw [loop_cost]
    simp

end BoyerMoore
