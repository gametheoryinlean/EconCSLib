---
id: mechanism_design.auction.bayesian.risk_aversion_comparison
title: Auction Comparisons Under Risk Aversion
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.basic.first_price_mechanism
  - mechanism_design.auction.basic.second_price_mechanism
  - mechanism_design.auction.bayesian.symmetric_first_price_equilibrium
  - mechanism_design.auction.bayesian.all_pay_equilibrium
  - mechanism_design.myerson.revenue_equivalence
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - risk-aversion
  - revenue-comparison
  - ipv
  - cara
---

# Auction Comparisons Under Risk Aversion

**Theorem (MSZ Thm 12.25, 12.26, 12.29; Krishna Ch 4).** Under
symmetric independent private values, the *risk-neutral* revenue
equivalence ([[mechanism_design.myerson.revenue_equivalence]]) between
first-price, second-price, and all-pay auctions breaks down once
bidders are risk averse. The standard ordering of expected revenue
under bidder risk aversion is:

$$
\mathbb{E}[R_{\mathrm{FP}}] \;\ge\; \mathbb{E}[R_{\mathrm{SP}}] \;=\; \mathbb{E}[R_{\mathrm{AP}}],
$$

with strict inequality for any non-trivial risk aversion. First-price
extracts strictly more revenue than second-price, while all-pay and
second-price coincide. Conversely, risk-averse *bidders* strictly
prefer second-price to first-price.

## Setup

- Symmetric IPV environment as in
  [[mechanism_design.auction.bayesian.single_item_framework]]: types $t_i \sim F$ i.i.d.
  on $[0, \omega]$.
- Each bidder has a strictly increasing, concave utility function
  $u : \mathbb{R} \to \mathbb{R}$ (e.g. CARA: $u(x) = -e^{-\rho x}$
  with $\rho > 0$, or CRRA: $u(x) = x^{1-\gamma}/(1-\gamma)$ with
  $\gamma \in (0, 1)$).
- Each bidder maximises expected utility of net payoff (value minus
  payment if winning, zero if losing).

## Key driver

In first-price, *bid shading* below truthful is bounded by the
uncertainty about the marginal opponent's bid:
- A higher bid increases the probability of winning (good) at the cost
  of a higher payment if winning (bad).
- Risk aversion *raises* the marginal value of winning relative to the
  marginal cost of paying more — the bidder prefers a more certain,
  smaller, payoff over a riskier larger one.
- Hence risk-averse bidders shade *less* than risk-neutral bidders,
  bidding closer to their true valuation.

The result is that the first-price equilibrium bid function
$\beta^{\mathrm{FP}}_u(t)$ under risk aversion lies strictly above the
risk-neutral counterpart from
[[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]]: $\beta^{\mathrm{FP}}_u(t) > \beta^{\mathrm{FP}}_{\text{rn}}(t)$ for every interior type $t$. Higher bids ⇒ higher seller revenue.

In second-price (and all-pay), bidders' optimal strategies do *not*
depend on $u$: truth-telling in second-price and the deterministic
"pay your bid no matter what" structure in all-pay both leave the
strategy invariant. The expected revenue is therefore unchanged from
the risk-neutral case.

## Bidder welfare comparison

The same logic reverses for bidder preferences:
- Risk-averse bidders strictly prefer the deterministic "pay only on
  losing" structure of second-price to the lottery-like outcomes of
  first-price.
- Quantitatively, ex-ante expected utility from second-price exceeds
  that from first-price (under symmetric IPV and any concave $u$).

## Why it matters

- **Auction design under risk aversion.** A revenue-maximising seller
  facing risk-averse bidders should prefer first-price over
  second-price — the reverse of the risk-neutral revenue-equivalence
  prediction.
- **Identification of risk attitudes.** Comparing observed first-price
  bids to the risk-neutral benchmark $\beta^{\mathrm{FP}}_{\text{rn}}$
  identifies the curvature of bidder utility from auction data.
- **Mechanism-design extensions.** Risk aversion creates a wedge
  between expected revenue (seller objective) and expected utility
  (bidder objective), motivating optimal mechanisms that exploit
  this wedge (Maskin-Riley 1984).

## Lean port (deferred)

Planned Lean module: `EconCSLib/Auction/RiskAversion.lean`.

Planned declarations:

- `RiskAverseUtility` (utility-function wrapper with concavity and
  strict monotonicity).
- `symmetricFirstPriceBid_riskAverse` (equilibrium bid function under
  risk aversion).
- `firstPrice_revenue_ge_secondPrice_under_riskAversion` (revenue
  comparison theorem).
- `bidder_prefers_secondPrice_under_riskAversion` (welfare comparison).

Dependencies: a Lean treatment of concave utility (likely via Mathlib's
`ConvexOn` / `ConcaveOn`); the risk-neutral first-price equilibrium
([[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]]); the
all-pay equilibrium ([[mechanism_design.auction.bayesian.all_pay_equilibrium]]).
Tracked in the MSZ Ch.12 auction gap review.

## References

- [MSZ Chapter 12, Thm 12.25, 12.26, 12.29] Maschler, Solan, and
  Zamir, *Game Theory*. Revenue and
  welfare comparisons under risk aversion.
- [Krishna, Chapter 4] Vijay Krishna, *Auction Theory*, 2nd ed.. Risk aversion in auctions.
- [Maskin-Riley 1984] Eric Maskin and John Riley, "Optimal Auctions
  with Risk Averse Buyers", *Econometrica* 52(6):1473–1518.
  Optimal mechanism design under risk aversion.
- [Holt 1980] Charles Holt, "Competitive bidding for contracts under
  alternative auction procedures", *Journal of Political Economy*
  88(3):433–445. Original risk-aversion revenue comparison.
