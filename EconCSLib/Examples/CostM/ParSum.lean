/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log

/-!
# EconCSLib.Examples.CostM.ParSum

Balanced parallel reduction over `List ℕ`, instrumented with `CostM ℕ`,
demonstrating `CostM.par` for parallel-time / depth complexity.

## Why this example

Companion to `GCD` (sequential additive cost), `MemoFib` (idempotent cost),
and `ReverseSpace` (max-monoid wrapper). This file uses `CostM.par`, the
non-monadic combinator that composes costs via `⊔` (here `max` on `ℕ`),
together with the ordinary additive `bind` for sequential glue.

The point: the *same* cost monoid `(ℕ, +, 0)` can express *depth* — provided
the algorithm uses `par` at branching points. Each `par` takes the max of
the two branches; each sequential `bind` adds.

## Cost model

* `par (parSum left) (parSum right)` combines the two recursive branches in
  parallel — cost = `max (parSum left).cost (parSum right).cost`.
* Each combine step (the post-`par` addition `sl + sr`) charges 1.
* Leaves charge 0 (`pure`).

So `(parSum xs).cost` counts the depth of the reduction tree.

## Main results

* `parSum_cost_le_clog` — `(parSum xs).cost ≤ Nat.clog 2 xs.length`. The tight
  `O(log n)` parallel-depth bound, by the standard halving recurrence:
  `T(n) = 1 + max(T(⌊n/2⌋), T(⌈n/2⌉))`. Closed via `Nat.clog_of_one_lt`
  (`clog 2 n = clog 2 ⌈n/2⌉ + 1` for `n ≥ 2`) plus monotonicity of `clog`.
* `parSum_cost_le_length` — `(parSum xs).cost ≤ xs.length`. Loose linear
  bound; proven independently (the `clog 2 n ≤ n` step would otherwise need
  its own helper).

## Caveat

This file tracks only depth, not work. To track both at once (work via `+`,
depth via `max`) the cost type would need to be a product `ℕ × ℕ` with a
custom `par`-combine that uses `+` on the first coordinate and `max` on the
second. That extension is not implemented here.
-/

namespace ParSum

/-- Balanced parallel sum of a `List ℕ`, instrumented with `CostM ℕ` to
record the parallel depth of the reduction.

The `if h : 2 ≤ xs.length` shape makes the length lower bound an explicit
hypothesis in the recursive branch — both for the termination prover and
for the cost-bound proof. -/
def parSum (xs : List ℕ) : CostM ℕ ℕ :=
  if _h : 2 ≤ xs.length then do
    let (sl, sr) ← CostM.par
                    (parSum (xs.take (xs.length / 2)))
                    (parSum (xs.drop (xs.length / 2)))
    ✓ pure (sl + sr)
  else
    pure (xs.head?.getD 0)
termination_by xs.length
decreasing_by
  all_goals (simp only [List.length_take, List.length_drop]; omega)

/-- **Tight depth bound**: parallel-sum depth is at most `⌈log₂ n⌉`.

The recurrence is `T(n) = 1 + max(T(⌊n/2⌋), T(⌈n/2⌉))` with `T(0) = T(1) = 0`.
Both halves are bounded above by `⌈n/2⌉ = (n+1)/2`, and
`Nat.clog_of_one_lt` gives `clog 2 n = clog 2 ⌈n/2⌉ + 1` for `n ≥ 2`, so
`T(n) ≤ clog 2 ⌈n/2⌉ + 1 = clog 2 n`. -/
theorem parSum_cost_le_clog (xs : List ℕ) :
    (parSum xs).cost ≤ Nat.clog 2 xs.length := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    unfold parSum
    by_cases hge : 2 ≤ xs.length
    · simp only [hge, dite_true]
      simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
                 CostM.cost_par, CostM.ret_par]
      have hLlt : (xs.take (xs.length / 2)).length < xs.length := by
        simp [List.length_take]; omega
      have hRlt : (xs.drop (xs.length / 2)).length < xs.length := by
        simp [List.length_drop]; omega
      have hLlen : (xs.take (xs.length / 2)).length = xs.length / 2 := by
        simp [List.length_take]; omega
      have hRlen : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 := by
        simp [List.length_drop]
      have ihL := ih _ (hn ▸ hLlt) (xs.take (xs.length / 2)) rfl
      have ihR := ih _ (hn ▸ hRlt) (xs.drop (xs.length / 2)) rfl
      rw [hLlen] at ihL
      rw [hRlen] at ihR
      -- Key identity: clog 2 n = clog 2 ((n+1)/2) + 1 for n > 1
      have h_clog_step :
          Nat.clog 2 xs.length = Nat.clog 2 ((xs.length + 1) / 2) + 1 := by
        have h := Nat.clog_of_one_lt (b := 2) (n := xs.length) (by decide) hge
        have heq : (xs.length + 2 - 1) / 2 = (xs.length + 1) / 2 := by omega
        rw [heq] at h
        exact h
      -- xs.length - xs.length / 2 = (xs.length + 1) / 2
      have h_ceil_eq : xs.length - xs.length / 2 = (xs.length + 1) / 2 := by omega
      rw [h_ceil_eq] at ihR
      -- clog of ⌊n/2⌋ ≤ clog of ⌈n/2⌉
      have ihL' : (parSum (xs.take (xs.length / 2))).cost
                ≤ Nat.clog 2 ((xs.length + 1) / 2) :=
        ihL.trans (Nat.clog_mono_right _ (by omega))
      -- Goal is in terms of `Nat.clog 2 n`; rewrite to `xs.length` then unfold.
      rw [← hn, h_clog_step]
      omega
    · simp only [hge, dite_false, CostM.cost_pure]
      omega

/-- Loose linear upper bound on parallel-sum depth. -/
theorem parSum_cost_le_length (xs : List ℕ) :
    (parSum xs).cost ≤ xs.length := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    unfold parSum
    by_cases hge : 2 ≤ xs.length
    · -- Recursive branch
      simp only [hge, dite_true]
      simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure, CostM.cost_par,
                 CostM.ret_par]
      have hLlt : (xs.take (xs.length / 2)).length < xs.length := by
        simp [List.length_take]; omega
      have hRlt : (xs.drop (xs.length / 2)).length < xs.length := by
        simp [List.length_drop]; omega
      have ihL := ih (xs.take (xs.length / 2)).length (hn ▸ hLlt)
                     (xs.take (xs.length / 2)) rfl
      have ihR := ih (xs.drop (xs.length / 2)).length (hn ▸ hRlt)
                     (xs.drop (xs.length / 2)) rfl
      have hLlen : (xs.take (xs.length / 2)).length ≤ xs.length / 2 := by
        simp [List.length_take]
      have hRlen : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 := by
        simp [List.length_drop]
      omega
    · -- Base branch: pure (xs.head?.getD 0), cost = 0
      simp only [hge, dite_false, CostM.cost_pure]
      omega

end ParSum
