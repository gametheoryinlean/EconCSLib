---
id: mechanism_design.myerson.virtual_value_regularity
title: Virtual Values and Regularity
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.myerson
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.bayesian.single_item_framework
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.OptimalSingleItem
  declarations:
    - BayesianSingleItemAuction.virtualValue
    - BayesianSingleItemAuction.IsRegular
    - BayesianSingleItemAuction.IsReserveThreshold
    - BayesianSingleItemAuction.measurable_virtualValue_of_isRegular
    - BayesianSingleItemAuction.isReserveThreshold_of_isRegular_of_virtualValue_eq_zero
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - mechanism-design
  - myerson
  - virtual-valuation
  - regularity
  - reserve-price
---

# Virtual Values and Regularity

For a Bayesian single-item auction
([[mechanism_design.auction.bayesian.single_item_framework]]), the Myerson
virtual value of bidder \(i\) at type \(v\) is
\[
\psi_i(v) = v - \frac{1 - F_i(v)}{f_i(v)}.
\]

In Lean this is `virtualValue A i v`, using the CDF stored in `A.typeData` and
the density `A.typeDensity i`.

## Regularity

`IsRegular A` states that each function \(v \mapsto \psi_i(v)\) is monotone.
Regularity is the condition that makes the virtual-surplus-maximizing
allocation rule monotone in each bidder's own report, which is the bridge to
DSIC via the Myerson monotonicity characterization
([[mechanism_design.myerson.monotonicity_characterization]]).

## Reserve thresholds

`IsReserveThreshold A i rho` records that `rho` separates nonpositive and
nonnegative virtual values for bidder \(i\).  If the virtual value is regular
and \(\psi_i(\rho)=0\), then `rho` is a reserve threshold.  These threshold
lemmas are used to interpret the optimal allocation rule as selling only above
reserve values, and support the reserve-price node
[[mechanism_design.myerson.reserve_price]].

## References

- [MSZ, Chapter 12, Section 12.10] Maschler, Solan, and Zamir, *Game Theory*.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design", *Mathematics of
  Operations Research* 6(1):58-73.
- [Krishna, Chapter 5] Vijay Krishna, *Auction Theory*, 2nd ed..
