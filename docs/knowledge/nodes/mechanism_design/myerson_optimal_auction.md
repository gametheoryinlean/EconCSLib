---
id: mechanism_design.myerson.optimal_auction
title: Regular Myerson Optimal Single-Item Auction
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.myerson
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.bayesian.selling_problem
  - mechanism_design.myerson.revenue_equivalence
  - mechanism_design.myerson.payment_formula
  - mechanism_design.myerson.monotonicity_characterization
  - mechanism_design.myerson.virtual_value_regularity
  - mechanism_design.myerson.virtual_surplus_maximizing_allocation
  - mechanism_design.auction.bayesian.single_item_framework
  - mechanism_design.auction.bayesian.interim_and_ic
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.OptimalSingleItem
  declarations:
    - BayesianSingleItemAuction.virtualSurplusMaximizingPaymentRule
    - BayesianSingleItemAuction.virtualSurplusMaximizingMechanism
    - BayesianSingleItemAuction.virtualSurplusMaximizingAuction
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions
    - BayesianSingleItemAuction.IsFeasibleICIRIntegrable
    - BayesianSingleItemAuction.IsRegularMyersonOptimalICIRAuction
    - BayesianSingleItemAuction.virtualSurplusMaximizingAuction_regularMyersonOptimalICIR_of_isRegular
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - mechanism-design
  - myerson
  - optimal-auction
  - virtual-valuation
  - bayesian
  - single-item
---

# Regular Myerson Optimal Single-Item Auction

For a regular Bayesian single-item auction environment
([[mechanism_design.auction.bayesian.single_item_framework]]), Myerson's
allocation rule maximizes expected seller revenue among feasible,
incentive-compatible, interim-individually-rational candidates satisfying the
analytic integrability assumptions needed for the density and Fubini steps.

The formalized statement is the regular case of the usual virtual-value
optimal-auction theorem.  Each bidder has a virtual value
\[
\psi_i(v) = v - \frac{1 - F_i(v)}{f_i(v)},
\]
and regularity means that every \(\psi_i\) is monotone.  The allocation rule
selects a bidder with maximum virtual value when that maximum is positive, and
withholds the item when all virtual values are nonpositive.

## Formalization

The module `EconCSLib.MechanismDesign.Auction.OptimalSingleItem` defines:

- `virtualValue` and `IsRegular`, the virtual-value and regularity layer.
- `virtualSurplus` and `expectedVirtualSurplus`, the pointwise and ex-ante
  virtual-surplus objectives.
- `virtualSurplusMaximizingAllocationRule`, which allocates to the highest
  positive virtual value with deterministic tie-breaking.
- `virtualSurplusMaximizingPaymentRule`, the Myerson payment rule attached to
  that allocation.
- `virtualSurplusMaximizingAuction`, the Bayesian auction obtained by reusing
  the original priors and type data.

The main theorem is
`virtualSurplusMaximizingAuction_regularMyersonOptimalICIR_of_isRegular`.
It proves that the constructed auction satisfies
`IsRegularMyersonOptimalICIRAuction`: virtual-surplus optimality,
single-item feasibility, interim incentive compatibility, interim IR on the
support, and expected-revenue optimality over the formal candidate class
`IsFeasibleICIRIntegrable`.

## Proof route

The proof follows the standard Myerson route:

1. Feasible allocation rules are compared pointwise by virtual surplus.
2. Regularity makes the virtual-surplus-maximizing allocation monotone in each
   bidder's own report.
3. The single-parameter Myerson payment construction
   ([[mechanism_design.myerson.payment_formula]]) gives DSIC for the mechanism.
4. DSIC implies the interim IC condition in the Bayesian single-item layer
   ([[mechanism_design.auction.bayesian.interim_and_ic]]).
5. Revenue is related to expected virtual surplus using the interim payment
   envelope, density identities, and Fubini assumptions.

## Analytic assumptions

The Lean theorem is intentionally explicit about analytic side conditions.  The
structure `RegularMyersonICIRAnalyticAssumptions` records the density
nonnegativity, product-prior, integrability, and Fubini hypotheses used to move
between ex-ante payments, interim payments, and virtual surplus.  This keeps the
mechanism-design statement reusable without hiding measure-theoretic obligations
inside the auction data.

## Reserve-price specialization

When bidders are symmetric and a reserve threshold is available, the allocation
behavior specializes to the usual reserve-price interpretation tracked by
[[mechanism_design.myerson.reserve_price]].  The current formal module proves
reserve-threshold sale/no-sale behavior for the virtual-surplus allocation; the
full symmetric equivalence to a second-price auction with optimal reserve is
kept as the separate reserve-price node.

## References

- [MSZ, Chapter 12, Section 12.10] Maschler, Solan, and Zamir, *Game Theory*. Virtual valuations and optimal auctions.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73. Original optimal-auction theorem.
- [Krishna, Chapter 5] Vijay Krishna, *Auction Theory*, 2nd ed.. Revenue equivalence and optimal auctions.
- [AGT, Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic
  Game Theory*. Algorithmic mechanism
  design view of virtual valuations.
