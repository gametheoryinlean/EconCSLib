/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Implications

Implication theorems between fairness notions for indivisible goods.

## Summary

For indivisible goods the fairness notions are ordered by strength. The proved arrows are:

  EFX → EF1                        (unconditional; existential weakening)
  EF  → EFX                        (for monotone valuations)
  EF  → PROP → MMS                 (for additive valuations, complete allocations)

The arrows are one-way in general:
- EF1 does **not** imply PROP. Counterexample: 2 agents, 3 goods of equal value — give
  1 good to agent A and 2 to agent B. Agent A is EF1 (removing one good from B equalises)
  but does not meet the 1/2-of-total proportionality threshold.
- PROP does **not** imply EF. Counterexample: 2 agents, 2 goods worth (10, 1) to agent 0
  and (1, 10) to agent 1 — the allocation ({g₀}, {g₁}) is PROP but not EF (each agent
  envies the other's good by their own values if swapped).

## Main results (this file)

* `IsEFX.isEF1` — in `Fairness.lean`; EFX → EF1 by existential weakening
* `IsEnvyFree.isProportional_additive` — EF → PROP for additive valuations (complete alloc)
* `IsProportional.isMaxminShare` — PROP → MMS for additive valuations (complete alloc)

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
* Lipton et al., "On Approximately Fair Allocations of Indivisible Goods" (EC 2004)
* Bouveret, Chevaleyre, Maudet — "Fair Allocation of Indivisible Goods" (COMSOC Handbook, Ch. 12)
* Budish — "The Combinatorial Assignment Problem" (JPE 2011)
-/

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### EF implies proportionality (for additive valuations) -/

/-- **EF → PROP** (for additive valuations with complete allocations).

    If every agent is envy-free under an additive valuation `w`, and `A` is a complete
    allocation of `allGoods`, then every agent receives at least `1/n` of the total value.

    *Proof*: for any agent `k`, additivity and the partition property give
    `v_k(allGoods) = Σ_j v_k(A_j)`. Envy-freeness bounds each term: `v_k(A_j) ≤ v_k(A_k)`.
    Summing: `v_k(allGoods) ≤ n · v_k(A_k)`.

    Note: EF1 does **not** imply PROP — see module docstring for a counterexample.
    [AGT Ch.11] -/
theorem IsEnvyFree.isProportional_additive
    [Fintype N] [DecidableEq G]
    (w : AdditiveValuation N G)
    {allGoods : Finset G} {A : Allocation N G}
    (hA : IsAllocation allGoods A)
    (hEF : IsEnvyFree w.toValuation A) :
    IsProportional (Fintype.card N) w.toValuation allGoods A := by
  intro k
  -- Step 1: partition the total value using additivity and the allocation structure.
  -- v_k(allGoods) = Σ_j v_k(A_j)  (since allGoods = ⋃_j A_j, disjoint)
  have hpart : w.toValuation.val k allGoods =
      Finset.univ.sum (fun j => w.toValuation.val k (A j)) := by
    simp only [AdditiveValuation.toValuation]
    rw [hA.complete,
        Finset.sum_biUnion (fun i _ j _ hij => hA.disjoint i j hij)]
  -- Step 2: bound each summand by v_k(A_k) via envy-freeness, then count.
  rw [hpart]
  calc Finset.univ.sum (fun j => w.toValuation.val k (A j))
      ≤ Finset.univ.sum (fun _ => w.toValuation.val k (A k)) :=
          Finset.sum_le_sum (fun j _ => hEF k j)
    _ = Fintype.card N • w.toValuation.val k (A k) := by
          simp [Finset.sum_const, Finset.card_univ]
    _ = (Fintype.card N : ℝ) * w.toValuation.val k (A k) := nsmul_eq_mul _ _

/-! ### PROP implies MMS -/

/-- **PROP → MMS** (for additive valuations with complete allocations).

    If allocation `A` is proportional (each agent receives ≥ 1/n of total value), then
    for every complete allocation `B` of `allGoods`, some bundle of `B` has value ≤
    `v_i(A_i)` for agent `i`. This is exactly the maximin share (MMS) guarantee.

    *Proof*: By contradiction. Suppose no bundle in `B` satisfies `v_i(B_j) ≤ v_i(A_i)`.
    Since the order is linear, every bundle strictly exceeds: `∀ j, v_i(A_i) < v_i(B_j)`.
    By `Finset.sum_lt_sum`, `n · v_i(A_i) = ∑_j v_i(A_i) < ∑_j v_i(B_j)`.
    By additivity and the partition property of `B`, `∑_j v_i(B_j) = v_i(allGoods)`.
    By proportionality, `v_i(allGoods) ≤ n · v_i(A_i)`. This gives
    `n · v_i(A_i) < n · v_i(A_i)`, a contradiction.

    Note: the converse MMS → PROP does not hold in general.

    [BCM Ch.12; Budish 2011] -/
theorem IsProportional.isMaxminShare
    [Fintype N] [Nonempty N] [DecidableEq G]
    (w : AdditiveValuation N G)
    {allGoods : Finset G} {A : Allocation N G}
    (hProp : IsProportional (Fintype.card N) w.toValuation allGoods A) :
    IsMaxminShare w.toValuation allGoods A := by
  intro i B hB
  by_contra hall
  push_neg at hall
  -- `hall : ∀ j : N, w.toValuation.val i (A i) < w.toValuation.val i (B j)`
  -- Partition B covers allGoods, so by additivity:
  -- `∑ j, w.toValuation.val i (B j) = w.toValuation.val i allGoods`
  have hpart : ∑ j : N, w.toValuation.val i (B j) = w.toValuation.val i allGoods := by
    simp only [AdditiveValuation.toValuation]
    rw [hB.complete, Finset.sum_biUnion (fun a _ b _ hab => hB.disjoint a b hab)]
  -- The constant sum `∑ j, w.val i (A i) = (n : ℝ) * w.val i (A i)` via nsmul_eq_mul.
  have hconst : ∑ _j : N, w.toValuation.val i (A i) =
      (Fintype.card N : ℝ) * w.toValuation.val i (A i) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Since every B-term strictly exceeds the A-term, the B-sum strictly exceeds the A-sum.
  have hlt : ∑ _j : N, w.toValuation.val i (A i) <
      ∑ j : N, w.toValuation.val i (B j) :=
    Finset.sum_lt_sum
      (fun j _ => le_of_lt (hall j))
      ⟨Classical.arbitrary N, Finset.mem_univ _, hall _⟩
  -- Combine: (n : ℝ) * v(A i) = ∑ A < ∑ B = v(allGoods) ≤ (n : ℝ) * v(A i). Contradiction.
  exact absurd
    (lt_of_lt_of_le (hpart ▸ hconst ▸ hlt) (hProp i))
    (lt_irrefl _)

end Indivisible
end FairDivision
end SocialChoice
