/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Efficiency

Efficiency notions for indivisible goods allocation.

## Main definitions

* `IsParetoOptimal` — no allocation weakly dominates A with at least one strict improvement

## Design

`IsParetoOptimal` is stated with an explicit `IsAllocation` hypothesis on the
dominating allocation `B`, so that the comparison is only over valid complete
allocations (not arbitrary functions `N → Finset G`).

The combination EF1 + PO (Pareto optimal) always exists via the maximum Nash welfare
allocation (Caragiannis et al. 2019), and also via envy-cycle elimination
(Lipton et al. 2004). These results are formalized in later phases.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 12
* Lipton et al., "On Approximately Fair Allocations of Indivisible Goods" (EC 2004)
* Caragiannis et al., "The Unreasonable Fairness of Maximum Nash Welfare" (EC 2016)
-/

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### Pareto optimality -/

/-- An allocation `A` is Pareto optimal if no complete allocation `B` weakly improves
    every agent's bundle value and strictly improves at least one agent's value.

    `[Fintype N]` is required because `IsAllocation` uses `Finset.univ.biUnion`.
    `[DecidableEq G]` is required for `Finset` operations. [AGT Ch.12] -/
abbrev IsParetoOptimal [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsParetoOptimal (fun B => IsAllocation allGoods B) v.val A

/-! ### Basic properties -/

section Properties

variable [Fintype N] [DecidableEq G]
variable (v : Valuation N G) (allGoods : Finset G)

/-- The allocation itself is not a Pareto improvement over itself. -/
lemma not_paretoImproved_self (A : Allocation N G) :
    ¬ (IsAllocation allGoods A ∧ (∀ i, v.val i (A i) ≤ v.val i (A i)) ∧
       ∃ i, v.val i (A i) < v.val i (A i)) := by
  rintro ⟨_, _, i, hi⟩
  exact lt_irrefl _ hi

end Properties

end Indivisible
end FairDivision
end SocialChoice
