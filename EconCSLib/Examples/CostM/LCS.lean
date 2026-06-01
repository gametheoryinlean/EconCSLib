/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.CostM
import EconCSLib.Foundation.CostM.Visited
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

/-!
# EconCSLib.Examples.CostM.LCS

Naive recursive **Longest Common Subsequence**, instrumented with
`CostM (Visited (ℕ × ℕ))` to track the **set** of sub-problem indices
visited.

The algorithm itself is **not** memoized — wall-clock time is exponential.
The cost monoid (`Visited` ≅ `Finset` under union, idempotent) is the trick:
visiting the same sub-problem index `(p, q)` twice does not enlarge the
cost. So the recorded cost is *exactly* the set of distinct sub-problem
indices that any path in the recursion tree could reach.

## Cost model

* On entering `lcs xs ys`, tick the index `(xs.length, ys.length)`.
* Sequential composition unions the visited sets.

## Main results

* `lcs_cost_subset` — `(lcs xs ys).cost.toFinset ⊆
    Finset.range (|xs|+1) ×ˢ Finset.range (|ys|+1)`. Containment in the
  natural DP grid.
* `lcs_cost_card_le` — corollary in cardinality form:
  `(lcs xs ys).cost.toFinset.card ≤ (|xs|+1) * (|ys|+1)`.

This is the **canonical "polynomial-space DP" example**: the bound is
exactly the DP table size a memoized version would fill, recovered
without actually memoizing — the idempotent cost monoid does the
deduplication algebraically.

## Companion to `MemoFib`

`MemoFib` uses `Visited ℕ` (1-D sub-problem index) and gets a linear
cardinality bound. This file uses `Visited (ℕ × ℕ)` (2-D index) and
gets a polynomial bound — same monoid shape, one dimension higher.
-/

namespace LCS

variable {A : Type*} [DecidableEq A]

/-- Naive recursive LCS, instrumented to record the set of (length-pair)
sub-problem indices visited.

The `.ret` field gives the LCS length; `.cost.toFinset` gives the set of
visited indices. The two are independent — bound proofs touch only
`.cost`. -/
def lcs : List A → List A → CostM (Visited (ℕ × ℕ)) ℕ
  | [],      ys      => do
    CostM.tick (Visited.singleton (0, ys.length))
    pure 0
  | x :: xs, []      => do
    CostM.tick (Visited.singleton (xs.length + 1, 0))
    pure 0
  | x :: xs, y :: ys =>
    if x = y then do
      CostM.tick (Visited.singleton (xs.length + 1, ys.length + 1))
      let r ← lcs xs ys
      pure (r + 1)
    else do
      CostM.tick (Visited.singleton (xs.length + 1, ys.length + 1))
      let r1 ← lcs xs (y :: ys)
      let r2 ← lcs (x :: xs) ys
      pure (max r1 r2)

/-- Monotonicity helper: enlarging both arguments of `Finset.range`
preserves the `×ˢ` containment. -/
private lemma range_prod_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Finset.range a ×ˢ Finset.range b ⊆ Finset.range a' ×ˢ Finset.range b' :=
  Finset.product_subset_product
    (Finset.range_subset_range.mpr ha)
    (Finset.range_subset_range.mpr hb)

/-- Containment of `(lcs xs ys).cost` in the natural DP grid
`[0, |xs|] × [0, |ys|]`. -/
theorem lcs_cost_subset (xs : List A) : ∀ (ys : List A),
    (lcs xs ys).cost.toFinset ⊆
      Finset.range (xs.length + 1) ×ˢ Finset.range (ys.length + 1) := by
  induction xs with
  | nil =>
    intro ys
    simp only [lcs, CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
               Visited.toFinset_add, Visited.toFinset_singleton, Visited.toFinset_zero,
               Finset.union_empty, List.length_nil]
    simp [Finset.singleton_subset_iff, Finset.mem_range]
  | cons x xs ihX =>
    intro ys
    induction ys with
    | nil =>
      simp only [lcs, CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
                 Visited.toFinset_add, Visited.toFinset_singleton, Visited.toFinset_zero,
                 Finset.union_empty, List.length_cons, List.length_nil]
      simp [Finset.singleton_subset_iff, Finset.mem_range]
    | cons y ys ihY =>
      unfold lcs
      split_ifs with hxy
      · -- match case: tick ∪ recursion on (xs, ys)
        simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
                   Visited.toFinset_add, Visited.toFinset_singleton, Visited.toFinset_zero,
                   Finset.union_empty, List.length_cons]
        refine Finset.union_subset ?_ ?_
        · simp [Finset.singleton_subset_iff, Finset.mem_range]
        · exact (ihX ys).trans (range_prod_mono (Nat.le_succ _) (Nat.le_succ _))
      · -- mismatch case: tick ∪ recursion on (xs, y::ys) ∪ recursion on (x::xs, ys)
        simp only [CostM.cost_bind, CostM.cost_tick, CostM.cost_pure,
                   Visited.toFinset_add, Visited.toFinset_singleton, Visited.toFinset_zero,
                   Finset.union_empty, List.length_cons]
        refine Finset.union_subset ?_ (Finset.union_subset ?_ ?_)
        · simp [Finset.singleton_subset_iff, Finset.mem_range]
        · exact (ihX (y :: ys)).trans
            (range_prod_mono (Nat.le_succ _) (by simp))
        · exact ihY.trans
            (range_prod_mono (by simp) (Nat.le_succ _))

/-- **Polynomial cardinality bound**: at most `(|xs|+1) * (|ys|+1)` distinct
sub-problems are touched, regardless of how often each is hit. -/
theorem lcs_cost_card_le (xs ys : List A) :
    (lcs xs ys).cost.toFinset.card ≤ (xs.length + 1) * (ys.length + 1) := by
  calc (lcs xs ys).cost.toFinset.card
      ≤ (Finset.range (xs.length + 1) ×ˢ Finset.range (ys.length + 1)).card :=
        Finset.card_le_card (lcs_cost_subset xs ys)
    _ = (xs.length + 1) * (ys.length + 1) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]

end LCS
