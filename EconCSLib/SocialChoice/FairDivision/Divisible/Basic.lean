/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.Valuation
import EconCSLib.SocialChoice.FairDivision.Fairness

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.Basic

Foundational definitions for divisible goods (cake-cutting) allocation.

## Main definitions

* `Allocation N Ω` — a function assigning each agent a subset of the cake `Ω`
* `IsAllocation` — predicate that an allocation is a measurable partition of `Ω`
* `CakeValuation N Ω V` — abstract valuation mapping cake-subsets to values in `V`
* `IsNormalized` — predicate that each agent values the whole cake at `1`
* `MeasureValuation` — standard valuation where each agent's value is a measure
* `IsContiguousAllocation` — each agent's piece is a (convex) interval in `ℝ`
* `IsEnvyFree`, `IsProportional`, `IsEquitable` — fairness predicates specialized to
  divisible allocations

## Design

The "cake" is an abstract type `Ω` with a `MeasurableSpace Ω`. This mirrors the indivisible
track (where `G` is an abstract type of goods), with `Set Ω` playing the role of `Finset G`.

`Allocation` is a plain function type alias; the partition predicate
`IsAllocation` is kept separate so that algorithms can manipulate raw allocations
before proving correctness. This follows the same separation principle as `Allocation` /
`IsAllocation` in `SocialChoice.FairDivision.Indivisible.Basic`.

`CakeValuation N Ω V` stays value-polymorphic because measure-based valuations naturally
take values in `ENNReal`. The bundled real-valued divisible cardinal interface lives in
`Divisible.Instance`.

`MeasureValuation` is the standard concrete case where each agent's value for a piece is
given by their personal (possibly non-atomic) measure. This corresponds to `AdditiveValuation`
in the indivisible track.

The fairness predicates `IsEnvyFree`, `IsProportional`, and `IsEquitable` are thin
specializations of the shared `SocialChoice.FairDivision` fairness layer to the share
type `Set Ω`.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 13
* Procaccia, "Cake Cutting: Not Just Child's Play" (2013)
* Robertson–Webb, *Cake-Cutting Algorithms* (1998)
-/

namespace SocialChoice
namespace FairDivision
namespace Divisible

open MeasureTheory Set

/-! ### Fairness predicates -/

/-- Envy-free (EF): every agent weakly prefers their own piece over any other agent's piece.

    `∀ i j, μ_i(A_j) ≤ μ_i(A_i)`.

    For divisible goods with non-atomic measures, EF allocations always exist. This is the key
    difference from the indivisible setting where EF need not exist. -/
def IsEnvyFree {N Ω V : Type*} [Preorder V]
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, μ.val i (A j) ≤ μ.val i (A i)

/-- Proportional (PROP): each agent values their piece at least `1 / n` of the whole cake.

    Stated as `μ_i(Ω) ≤ n * μ_i(A_i)` to avoid division. -/
def IsProportional {N Ω V : Type*} [Preorder V] [Semiring V] (n : ℕ)
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i : N, μ.val i Set.univ ≤ (n : V) * μ.val i (A i)

/-- Equitable: every agent assigns exactly the same value to their own piece. -/
def IsEquitable {N Ω V : Type*} [Preorder V]
    (cv : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, cv.val i (A i) = cv.val j (A j)

/-! ### EF implies proportional -/

/-- **EF implies proportional** for `MeasureValuation` partitions. -/
theorem IsEnvyFree.isProportional
    {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (μ : N → Measure Ω)
    (A : Allocation N Ω)
    (ha : IsAllocation A)
    (hef : IsEnvyFree (MeasureValuation μ) A) :
    IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  intro i
  calc μ i Set.univ
      = μ i (⋃ j, A j) := by rw [ha.cover]
    _ = ∑' j, μ i (A j) :=
          measure_iUnion (fun ⦃j k⦄ hjk => ha.disjoint j k hjk) ha.measurable
    _ = ∑ j : N, μ i (A j) := tsum_fintype _
    _ ≤ ∑ j : N, μ i (A i) := Finset.sum_le_sum fun j _ => hef i j
    _ = Fintype.card N * μ i (A i) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Divisible
end FairDivision
end SocialChoice
