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
    - BayesianSingleItemAuction.cdfVirtualValue
    - BayesianSingleItemAuction.virtualValueCutoff
    - BayesianSingleItemAuction.virtualValueCutoff_boundary_eq
    - BayesianSingleItemAuction.virtualValueCutoff_boundary_eq_of_eq
    - BayesianSingleItemAuction.positiveVirtualValueCutoff
    - BayesianSingleItemAuction.VirtualValueReserve
    - BayesianSingleItemAuction.VirtualValueReserve.of_continuousAt
    - BayesianSingleItemAuction.VirtualValueReserve.virtualValueCutoffReserve_zero
    - BayesianSingleItemAuction.VirtualValueCutoffReserve
    - BayesianSingleItemAuction.VirtualValueCutoffReserve.of_continuousAt
    - BayesianSingleItemAuction.VirtualValueCutoffReserve.virtualValueReserve_of_zero
    - BayesianSingleItemAuction.IsVirtualValueCutoff
    - BayesianSingleItemAuction.CommonRegularReserve
    - BayesianSingleItemAuction.CommonCDFRegularReserve
    - BayesianSingleItemAuction.CommonVirtualValueReserve
    - BayesianSingleItemAuction.CommonVirtualValueReserve.of_continuousAt
    - BayesianSingleItemAuction.CommonVirtualValueReserve.commonRegularReserve
    - BayesianSingleItemAuction.CommonVirtualValueReserve.commonVirtualValueCutoffReserve
    - BayesianSingleItemAuction.CommonVirtualValueCutoffReserve
    - BayesianSingleItemAuction.CommonVirtualValueCutoffReserve.of_continuousAt
    - BayesianSingleItemAuction.CommonCDFVirtualValueReserve
    - BayesianSingleItemAuction.CommonCDFVirtualValueReserve.of_continuousAt
    - BayesianSingleItemAuction.CommonCDFVirtualValueReserve.commonRegularReserve
    - BayesianSingleItemAuction.CommonCDFVirtualValueReserve.commonCDFRegularReserve
    - BayesianSingleItemAuction.CommonCDFVirtualValueReserve.commonCDFVirtualValueCutoffReserve
    - BayesianSingleItemAuction.CommonCDFVirtualValueCutoffReserve
    - BayesianSingleItemAuction.CommonCDFVirtualValueCutoffReserve.of_continuousAt
    - BayesianSingleItemAuction.ProfileSplitMeasurabilityAssumptions
    - BayesianSingleItemAuction.ProfileSplitIntegrabilityAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.toIsFeasibleICIRIntegrable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_isRevenueUpperBounded
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_isRevenueUpperBounded_of_sameEnvironment_of_isFeasibleICIR
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_expectedVirtualSurplus
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_expectedVirtualSurplus_of_sameEnvironment_of_isFeasibleICIR
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_expectedRevenueVirtualSurplusIdentity
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_integrableVirtualSurplus
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_isRevenueComparable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_isRevenueUpperBounded
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular_of_sameEnvironment_of_isFeasibleICIR
    - BayesianSingleItemAuction.IsFeasibleICIRIntegrable
    - BayesianSingleItemAuction.IsRegularMyersonOptimalICIRAuction
    - BayesianSingleItemAuction.IsRegularMyersonOptimalICIRAuction.hasSameSellingEnvironment
    - BayesianSingleItemAuction.IsRegularMyersonOptimalICIRAuction.integrableVirtualSurplus
    - BayesianSingleItemAuction.IsRegularMyersonOptimalICIRAuction.expectedSellerRevenue_le
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
MSZ writes the same object as \(c_i\); in Lean this is `virtualValue`.

This matches [MSZ Theorem 12.59]: when the virtual valuation functions are
monotone, the mechanism defined by the virtual-surplus-maximizing allocation
and its payment rule maximizes expected seller revenue among IC and IR direct
selling mechanisms.  Lean makes the accompanying analytic assumptions explicit.

## Formalization

The module `EconCSLib.MechanismDesign.Auction.OptimalSingleItem` defines:

- `virtualValue` and `IsRegular`, the virtual-value and regularity layer.
- `cdfVirtualValue`, `virtualValueCutoff`, `VirtualValueReserve`,
  `IsVirtualValueCutoff`, and the
  common virtual-value reserve wrappers, the reusable cutoff interface for
  reserve-price and symmetric-environment specializations.  The boundary
  equation at the cutoff can be derived from continuity either at the bare
  virtual-value layer or directly at the common/common-CDF wrapper layer when
  the strict superlevel set is nonempty and bounded below.
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
structure `RegularMyersonICIRAnalyticAssumptions` records the independent-prior
environment, the CDF/density/envelope assumptions, and the profile-split
integrability package for feasible IC/IR candidates.  Projection theorems then
derive the Fubini packages, envelope upper bound, and revenue-upper-bound
interface used in the MSZ 12.59 proof.  The final comparison is also exposed as
`candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular`,
with a raw-assumption wrapper
`candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular_of_sameEnvironment_of_isFeasibleICIR`
for candidates presented directly by same-environment, feasibility, IC, and IR
hypotheses,
so the compact theorem can be read as an assembly of reusable assumptions rather
than a monolithic proof.  The final `IsRegularMyersonOptimalICIRAuction`
predicate also exposes projections for same-environment compatibility,
virtual-surplus integrability, and the expected-revenue comparison against any
formal feasible IC/IR candidate.  This keeps the mechanism-design statement
reusable without hiding measure-theoretic obligations inside the auction data.

## Reserve-price specialization

When bidders are symmetric and a reserve threshold is available, the allocation
behavior specializes to the usual reserve-price interpretation tracked by
[[mechanism_design.myerson.reserve_price]].  The separate reserve-price node now
formalizes the MSZ 12.61 endpoint: under a common regular reserve, the reserve
second-price auction is itself regular-Myerson optimal, with the boundary
tie-convention handled by virtual-surplus and expected-revenue equality rather
than global auction-object equality.

## References

- [MSZ, Chapter 12, Section 12.10] Maschler, Solan, and Zamir, *Game Theory*,
  `references/GameTheory.pdf`. Virtual valuations and optimal auctions.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73. Original optimal-auction theorem.
- [Krishna, Chapter 5] Vijay Krishna, *Auction Theory*, 2nd ed.,
  `references/AuctionTheory.pdf`. Revenue equivalence and optimal auctions.
- [AGT, Chapter 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic
  Game Theory*, `references/AlgorithmicGameTheory.pdf`. Algorithmic mechanism
  design view of virtual valuations.
