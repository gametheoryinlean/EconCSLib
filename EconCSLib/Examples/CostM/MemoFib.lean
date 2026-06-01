/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Visited
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Fib.Basic

/-!
# EconCSLib.Examples.CostM.MemoFib

Bottom-up memoized Fibonacci instrumented with `CostM (Visited ℕ)`.

The algorithm carries the pair `(fib k, fib (k+1))` upward, so each
sub-problem `0, 1, …, n` is visited exactly once. The recorded cost is
exactly `Finset.range (n + 1)`.

Companion to `GCD` (counts steps with `C = ℕ`); here the cost type is
`Visited ℕ`, demonstrating that `CostM` is genuinely polymorphic over the
cost monoid. The union monoid on `Visited ℕ` is *idempotent* — repeated
visits don't enlarge the recorded set — which is the algebraic shadow of
memoization. The algorithm below realizes that shadow by actually
memoizing (bottom-up rather than via a memo table, but the access pattern
matches: every index is hit once).

## Cost model

* Touching sub-problem `i` ticks `Visited.singleton i`.
* Sequential composition unions the visited sets (the `Visited` monoid).

## Main results

* `fib_value`     — `(fib n).ret = Nat.fib n` (functional correctness).
* `fib_cost`      — `(fib n).cost.toFinset = Finset.range (n + 1)`.
* `fib_cost_card` — exactly `n + 1` distinct sub-problems are touched.
-/

namespace MemoFib

open Visited (singleton)

/-- Pair-passing helper: `fibAux k` returns `(Nat.fib k, Nat.fib (k+1))`
and ticks sub-problems `0, …, k` (each exactly once). -/
def fibAux : ℕ → CostM (Visited ℕ) (ℕ × ℕ)
  | 0     => do ✓[singleton 0] pure (0, 1)
  | k + 1 => do
    let p ← fibAux k
    ✓[singleton (k + 1)] pure (p.2, p.1 + p.2)

/-- Bottom-up Fibonacci. Visits each sub-problem in `{0, …, n}` exactly
once. -/
def fib (n : ℕ) : CostM (Visited ℕ) ℕ := do
  let p ← fibAux n
  pure p.1

/-! ### Functional correctness -/

theorem fibAux_ret (n : ℕ) :
    (fibAux n).ret = (Nat.fib n, Nat.fib (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show ((fibAux k) >>= _).ret = _
    simp [CostM.ret_bind, ih, Nat.fib_add_two]

/-- The value computed by `fib n` is the `n`-th Fibonacci number. -/
theorem fib_value (n : ℕ) : (fib n).ret = Nat.fib n := by
  show ((fibAux n) >>= _).ret = _
  simp [fibAux_ret]

/-! ### Cost analysis -/

theorem fibAux_cost (n : ℕ) :
    (fibAux n).cost.toFinset = Finset.range (n + 1) := by
  induction n with
  | zero => simp [fibAux]
  | succ k ih =>
    show ((fibAux k) >>= _).cost.toFinset = _
    simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
      Visited.toFinset_add, Visited.toFinset_singleton, Visited.toFinset_zero,
      Finset.union_empty]
    rw [ih]
    ext x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
    omega

/-- The set of sub-problems touched by `fib n` is exactly `{0, …, n}`. -/
theorem fib_cost (n : ℕ) :
    (fib n).cost.toFinset = Finset.range (n + 1) := by
  show ((fibAux n) >>= _).cost.toFinset = _
  simp only [CostM.cost_bind, CostM.cost_pure,
    Visited.toFinset_add, Visited.toFinset_zero, Finset.union_empty]
  exact fibAux_cost n

/-- Exactly `n + 1` distinct sub-problems are touched by `fib n`. -/
theorem fib_cost_card (n : ℕ) : (fib n).cost.toFinset.card = n + 1 := by
  rw [fib_cost, Finset.card_range]

end MemoFib
