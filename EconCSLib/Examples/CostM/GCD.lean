/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Log

/-!
# EconCSLib.Examples.CostM.GCD

Euclidean GCD instrumented with `CostM ℕ`, counting calls to `_ % _`.

## Cost model

* Each recursive step (one `mod`) costs `1`.
* Pattern matching, the base-case `pure`, and arithmetic on `b + 1` are free.

## Main results

* `gcd_cost_le` — `(gcd a b).cost ≤ b`. Linear bound, easiest to prove.
* `gcd_cost_log_le` — `(gcd a b).cost ≤ 2 * Nat.log 2 b + 1`. Tight up to a
  constant factor of 2 (vs. the sharp Lamé / Fibonacci bound). The proof
  uses the "every two steps, the second argument halves" property of the
  Euclidean recursion.

## Why this example

This is the **simplest instantiation** of `CostM`: cost type `C := ℕ` with
the usual additive monoid. Sequential composition `>>=` adds counts via `+`,
and the proof is structural induction on the second argument with `omega`
closing the arithmetic step.
-/

namespace GCD

/-- Euclidean GCD, instrumented with `CostM ℕ` to count `mod` calls. -/
def gcd : ℕ → ℕ → CostM ℕ ℕ
  | a, 0     => pure a
  | a, b + 1 => do
    ✓ gcd (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- Linear cost bound: `gcd a b` performs at most `b` `mod` operations. -/
theorem gcd_cost_le (a b : ℕ) : (gcd a b).cost ≤ b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    match b with
    | 0 => simp [gcd]
    | b' + 1 =>
      unfold gcd
      simp only [CostM.cost_bind, CostM.cost_tick]
      have hmod : a % (b' + 1) < b' + 1 := Nat.mod_lt _ (Nat.succ_pos _)
      have := ih (a % (b' + 1)) hmod (b' + 1)
      omega

/-! ### Tight `O(log b)` bound -/

/-- Halving lemma for the Euclidean recursion: if `0 < r < b`, then
`b mod r ≤ b / 2`. This is the algebraic core of the `O(log b)` bound:
two consecutive Euclidean steps cause the second argument to halve.

Proof by case analysis on whether `2 * r ≤ b`. If yes, `b mod r < r ≤ b/2`.
If no, then `b / r = 1` (since `r > b/2`), so `b mod r = b - r < b/2`. -/
private lemma mod_halves {b r : ℕ} (hr : 0 < r) (hrb : r < b) :
    b % r ≤ b / 2 := by
  by_cases h : 2 * r ≤ b
  · have hmod_lt : b % r < r := Nat.mod_lt b hr
    omega
  · push_neg at h
    have hge1 : 1 ≤ b / r := (Nat.one_le_div_iff hr).mpr hrb.le
    have hlt2 : b / r < 2 := by
      rw [Nat.div_lt_iff_lt_mul hr]; omega
    have hdiv : b / r = 1 := by omega
    have heq : b = r + b % r := by
      have hdm := Nat.div_add_mod b r
      rw [hdiv] at hdm
      omega
    omega

/-- Tight cost bound up to a factor of 2: `gcd a b` performs at most
`2 * log₂(b) + 1` `mod` operations. -/
theorem gcd_cost_log_le (a b : ℕ) :
    (gcd a b).cost ≤ 2 * Nat.log 2 b + 1 := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    match b with
    | 0 => simp [gcd]
    | b' + 1 =>
      have hb_pos : 0 < b' + 1 := Nat.succ_pos _
      unfold gcd
      simp only [CostM.cost_bind, CostM.cost_tick]
      by_cases hr : a % (b' + 1) = 0
      · -- a % b = 0: gcd b 0 = pure b, cost = 0, total = 1
        rw [hr]
        unfold gcd
        simp only [CostM.cost_pure]
        omega
      · -- a % b > 0: peel two more levels to apply the halving lemma
        have hr_pos : 0 < a % (b' + 1) := Nat.pos_of_ne_zero hr
        have hr_lt : a % (b' + 1) < b' + 1 := Nat.mod_lt _ hb_pos
        -- b ≥ 2 because b = 1 would force a % 1 = 0
        have hb_ge_2 : 2 ≤ b' + 1 := by
          rcases Nat.eq_zero_or_pos b' with hb' | hb'
          · subst hb'; simp [Nat.mod_one] at hr
          · omega
        rcases Nat.exists_eq_succ_of_ne_zero hr with ⟨r', hr'⟩
        rw [hr']
        unfold gcd
        simp only [CostM.cost_bind, CostM.cost_tick]
        have hs_lt_b : (b' + 1) % (r' + 1) < b' + 1 := by
          have : (b' + 1) % (r' + 1) < r' + 1 := Nat.mod_lt _ (Nat.succ_pos _)
          omega
        have ihs := ih ((b' + 1) % (r' + 1)) hs_lt_b (r' + 1)
        have hhalve : (b' + 1) % (r' + 1) ≤ (b' + 1) / 2 := by
          apply mod_halves (Nat.succ_pos _)
          rw [← hr']; exact hr_lt
        have hlog_mono :
            Nat.log 2 ((b' + 1) % (r' + 1)) ≤ Nat.log 2 ((b' + 1) / 2) :=
          Nat.log_mono_right hhalve
        have hlog_rec :
            Nat.log 2 (b' + 1) = Nat.log 2 ((b' + 1) / 2) + 1 :=
          Nat.log_of_one_lt_of_le (by omega : (1 : ℕ) < 2) hb_ge_2
        omega

end GCD
