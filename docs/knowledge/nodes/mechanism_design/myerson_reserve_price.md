---
id: mechanism_design.myerson.reserve_price
title: Regular Myerson Reserve Second-Price Characterisation
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.myerson
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.myerson.optimal_auction
  - mechanism_design.myerson.virtual_value_regularity
  - mechanism_design.myerson.virtual_surplus_maximizing_allocation
  - mechanism_design.auction.basic.reserve_second_price_mechanism
  - mechanism_design.auction.basic.reserve_second_price_dsic
  - mechanism_design.auction.bayesian.single_item_framework
  - mechanism_design.auction.bayesian.interim_and_ic
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.OptimalSingleItem
    - EconCSLib.MechanismDesign.Auction.RegularMyersonReserveSecondPrice
  declarations:
    - BayesianSingleItemAuction.reserveSecondPriceAuction
    - BayesianSingleItemAuction.ReserveSecondPriceAEUniqueArgmax
    - BayesianSingleItemAuction.ReserveSecondPriceInterimMeasurabilityAssumptions
    - BayesianSingleItemAuction.ReserveSecondPriceCandidateAssumptions
    - BayesianSingleItemAuction.ReserveSecondPriceCandidateAssumptions.of_interimMeasurable
    - BayesianSingleItemAuction.ReserveSecondPriceCandidateAssumptions.of_ae_unique_argmax
    - BayesianSingleItemAuction.ReserveSecondPriceCandidateAssumptions.hasIntegrableInterimObjects
    - BayesianSingleItemAuction.AEUniqueArgmaxPrior
    - BayesianSingleItemAuction.AENonnegativeBidsPrior
    - BayesianSingleItemAuction.AENoReserveTiePrior
    - BayesianSingleItemAuction.AEStrictReserveBidProfile
    - BayesianSingleItemAuction.withheldProbability
    - BayesianSingleItemAuction.sellerSurplusWithReserveValue
    - BayesianSingleItemAuction.expectedSellerSurplusWithReserveValue
    - BayesianSingleItemAuction.IsVirtualValueCutoff
    - BayesianSingleItemAuction.isReserveThreshold_iff_isVirtualValueCutoff_zero
    - BayesianSingleItemAuction.CommonRegularReserve
    - BayesianSingleItemAuction.CommonCDFRegularReserve
    - BayesianSingleItemAuction.cdfVirtualValue
    - BayesianSingleItemAuction.virtualValueCutoff
    - BayesianSingleItemAuction.virtualValueCutoff_boundary_eq
    - BayesianSingleItemAuction.virtualValueCutoff_boundary_eq_of_eq
    - BayesianSingleItemAuction.positiveVirtualValueCutoff
    - BayesianSingleItemAuction.VirtualValueReserve
    - BayesianSingleItemAuction.VirtualValueReserve.of_continuousAt
    - BayesianSingleItemAuction.VirtualValueCutoffReserve
    - BayesianSingleItemAuction.VirtualValueCutoffReserve.of_continuousAt
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
    - BayesianSingleItemAuction.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve
    - BayesianSingleItemAuction.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonCDFRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonCDFRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonCDFVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonCDFRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonCDFVirtualValueReserve
    - BayesianSingleItemAuction.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    - BayesianSingleItemAuction.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFRegularReserve
    - BayesianSingleItemAuction.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonVirtualValueReserve
    - BayesianSingleItemAuction.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_interimMeasurable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_ae_unique_argmax
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_interimMeasurable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_interimMeasurable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_interimMeasurable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_interimMeasurable
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_candidateAssumptions
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_ae_unique_argmax
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_ae_unique_argmax
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_ae_unique_argmax
    - BayesianSingleItemAuction.RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_ae_unique_argmax
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - mechanism-design
  - myerson
  - reserve-price
  - second-price-auction
  - bayesian
  - regular
  - single-item
---

# Regular Myerson Reserve Second-Price Characterisation

In a regular Bayesian single-item auction
([[mechanism_design.auction.bayesian.single_item_framework]]), suppose all
bidders share a strictly increasing virtual-value function \(\phi\) and a
common reserve \(\rho\) satisfying \(\phi(\rho)=0\). Then the reserve
second-price auction with reserve \(\rho\)
([[mechanism_design.auction.basic.reserve_second_price_mechanism]]) is
regular-Myerson optimal: it is feasible, incentive compatible, interim
individually rational, and expected-revenue optimal among the formal
feasible IC/IR candidate class.
Here \(\phi\) is the common presentation of the MSZ virtual valuation functions
\(c_i\), represented in Lean by `CommonRegularReserve.common_virtualValue`.

The virtual-value cutoff interface can also package the reserve as
\[
\rho^*=\inf\{t:\phi(t)>0\},
\]
with the boundary equation \(\phi(\rho^*)=0\) either recorded explicitly or
derived from continuity when the strict superlevel set is nonempty and bounded
below.  This abstract form covers the infimum presentation used in
[MSZ Corollary 12.61].

This is the Lean formalisation of the reserve-price endpoint of Myerson's
regular optimal-auction theorem ([[mechanism_design.myerson.optimal_auction]]),
corresponding to the MSZ reserve-price corollary cited below.

[MSZ Corollary 12.61] specializes Theorem 12.59 to IID private values: under
regularity, the optimal IC direct selling mechanism is a sealed-bid second-price
auction with a reserve price.  Lean represents the IID/common-value content
through common regular-reserve and common-CDF reserve interfaces, with analytic
null-set and integrability assumptions exposed separately.

## Formalization

The formalization is split into a reusable virtual-value layer and a
reserve-second-price specialization.

The module `EconCSLib.MechanismDesign.Auction.OptimalSingleItem` provides the
common-reserve and cutoff interfaces:

- `CommonRegularReserve A rho` states that all virtual values are a common
  strictly increasing function with zero at `rho`.
- `CommonCDFRegularReserve A rho` is the symmetric-CDF version, deriving the
  common virtual value from the stored CDF and density.
- `positiveVirtualValueCutoff`, `VirtualValueReserve`, and
  `CommonVirtualValueReserve` express the reserve as the positive-virtual-value
  cutoff
  \(\rho=\inf\{t:\phi(t)>0\}\).  `VirtualValueReserve.of_continuousAt` and
  `VirtualValueCutoffReserve.of_continuousAt` derive the boundary equation from
  continuity under the nonempty bounded-below superlevel-set assumptions; the
  common virtual-value wrappers provide the same constructors directly.
- `cdfVirtualValue` and `CommonCDFVirtualValueReserve` give the same wrapper
  from a common CDF, with common-CDF `of_continuousAt` constructors for the
  induced virtual value.
  The zero-cutoff conversion lemmas package the same reserve assumptions as
  `CommonVirtualValueCutoffReserve 0 rho` and
  `CommonCDFVirtualValueCutoffReserve 0 rho`.

The module `EconCSLib.MechanismDesign.Auction.RegularMyersonReserveSecondPrice`
adds the reserve-price layer on top of those interfaces:

- `reserveSecondPriceAuction` wraps the reserve Vickrey auction as a
  `BayesianSingleItemAuction`, reusing the original prior and type data.
- `ReserveSecondPriceInterimMeasurabilityAssumptions`,
  `ReserveSecondPriceCandidateAssumptions`,
  `ReserveSecondPriceAEUniqueArgmax`, and the prior-level a.e. packages
  isolate the measurability, nonnegative-reserve, uniqueness, nonnegative-bid,
  and no-reserve-tie obligations used to make reserve second-price an IC/IR
  integrable candidate.
- The expected-revenue equality bridge has both explicit `AEUniqueArgmaxPrior`
  entry points and analytic-assumption entry points, including the common
  virtual-value cutoff presentations.
- `reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve`
  proves that the reserve second-price allocation is pointwise
  virtual-surplus optimal.
- `RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve`
  is the main MSZ 12.61 endpoint.
- `RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve`
  and its common-CDF version package the same optimality result through the
  virtual-value cutoff interface.
- The final optimality endpoint also has variants from packaged interim
  measurability, from `ReserveSecondPriceCandidateAssumptions`, and from a.e.
  unique interim-slice highest-bid assumptions, for each common reserve
  presentation.

The corresponding `commonCDFRegularReserve` theorems package the same result
for the common-CDF presentation used in symmetric IPV specializations.

## Virtual-value cutoffs

The library also records a reusable cutoff layer:
`withheldProbability`, `sellerSurplusWithReserveValue`, and
`expectedSellerSurplusWithReserveValue` define the seller's payoff when keeping
the item has value \(s\).  Independently, `virtualValueCutoff`,
`IsVirtualValueCutoff i κ rho`, `VirtualValueCutoffReserve`,
`CommonVirtualValueCutoffReserve`, and `CommonCDFVirtualValueCutoffReserve`
express the abstract cutoff equation \(\phi(\rho)=κ\).  The comparison level
\(κ\) is not tied to one economic interpretation; seller reservation value is
only one later application.

This layer is intentionally not stated as part of the MSZ 12.61 optimality
theorem. [MSZ Corollary 12.61] is a revenue-maximization statement with zero
seller reservation value. The cutoff and seller-payoff definitions are reusable
groundwork for later optimality statements with nonzero virtual-value cutoffs or
a retained-object payoff.

## Boundary convention

The formal statement deliberately avoids claiming global auction-object
equality with `virtualSurplusMaximizingAuction`. At a bid profile where
\(\max_i b_i=\rho\), the reserve second-price auction sells, while the current
virtual-surplus-maximizing allocation withholds at zero virtual surplus. This
difference is economically immaterial for expected revenue under the analytic
assumptions used here, but it matters for definitional equality in Lean.

The file therefore proves the useful equalities at the right levels:

- allocation and payment agree on strict reserve profiles, away from the
  reserve boundary;
- the reserve second-price allocation has the same pointwise virtual surplus
  as the virtual-surplus-maximizing allocation;
- expected seller revenue agrees under the atomless/product-prior hypotheses
  bundled in `RegularMyersonICIRAnalyticAssumptions`;
- the reserve second-price auction itself satisfies
  `IsRegularMyersonOptimalICIRAuction`.

## Proof route

1. A common strictly increasing virtual value preserves the highest-bidder
   order, so the highest bid is also the highest virtual value.
2. The equation \(\phi(\rho)=0\) turns the reserve test \(b_i \ge \rho\) into
   the nonnegative-virtual-value test used by Myerson's allocation rule.
3. The reserve second-price payment coincides with the Myerson threshold
   payment away from the reserve boundary.
4. Boundary profiles contribute zero virtual surplus and are null under the
   analytic no-tie assumptions.
5. Expected-revenue optimality transfers from the regular Myerson auction to
   the reserve second-price auction.

## References

- [MSZ Corollary 12.61] Maschler, Solan, and Zamir, *Game Theory*,
  `references/GameTheory.pdf`.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73.
- [Krishna, Chapter 5] Vijay Krishna, *Auction Theory*, 2nd ed.,
  `references/AuctionTheory.pdf`.
