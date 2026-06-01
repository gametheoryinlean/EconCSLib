---
id: mechanism_design.myerson.virtual_surplus_maximizing_allocation
title: Virtual-Surplus-Maximizing Allocation
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.myerson
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.myerson.virtual_value_regularity
  - mechanism_design.auction.bayesian.single_item_framework
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.OptimalSingleItem
  declarations:
    - BayesianSingleItemAuction.virtualSurplus
    - BayesianSingleItemAuction.expectedVirtualSurplus
    - BayesianSingleItemAuction.IntegrableVirtualSurplus
    - BayesianSingleItemAuction.IsSingleItemAllocationRule
    - BayesianSingleItemAuction.IsVirtualSurplusOptimalAllocationRule
    - BayesianSingleItemAuction.virtualScore
    - BayesianSingleItemAuction.virtualSurplusMaximizingWinner
    - BayesianSingleItemAuction.winningVirtualValue
    - BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule
    - BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_isSingleItemAllocationRule
    - BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_isVirtualSurplusOptimalAllocationRule
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - mechanism-design
  - myerson
  - virtual-surplus
  - allocation-rule
  - single-item
---

# Virtual-Surplus-Maximizing Allocation

The virtual-surplus objective for a single-item allocation rule \(x\) is
\[
\sum_i x_i(t)\,\psi_i(t_i),
\]
where \(\psi_i\) is bidder \(i\)'s virtual value
([[mechanism_design.myerson.virtual_value_regularity]]).

## Allocation rule

`virtualSurplusMaximizingAllocationRule A` chooses a bidder with maximal
virtual value when the winning virtual value is positive.  If every virtual
value is nonpositive, the allocation rule assigns probability zero to every
bidder, so the item is withheld.

Tie-breaking is deterministic: `virtualScore` pairs each virtual value with the
bidder index in lexicographic order, and `virtualSurplusMaximizingWinner` uses
the existing finite argmax utilities from the auction layer.

## Formal properties

The formalization proves that this rule is a feasible single-item allocation:
allocation probabilities are nonnegative and the total allocation probability
is at most one.  It also proves pointwise virtual-surplus optimality among
all feasible single-item allocation rules.

These pointwise facts lift to ex-ante expected virtual-surplus comparisons
under the corresponding integrability assumptions, and become the allocation
part of the regular Myerson optimal auction theorem
[[mechanism_design.myerson.optimal_auction]].

## References

- [MSZ, Chapter 12, Section 12.10] Maschler, Solan, and Zamir, *Game Theory*.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73.
- [AGT, Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic
  Game Theory*.
