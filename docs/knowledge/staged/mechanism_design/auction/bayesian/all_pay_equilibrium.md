---
id: mechanism_design.auction.bayesian.all_pay_equilibrium
title: All-Pay Auction Symmetric Equilibrium
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.bayesian.single_item_framework
  - mechanism_design.auction.bayesian.symmetric_first_price_equilibrium
  - mechanism_design.myerson.revenue_equivalence
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - all-pay
  - bayes-nash
  - symmetric-equilibrium
  - ipv
  - revenue-equivalence
---

# All-Pay Auction Symmetric Equilibrium

**Theorem (MSZ Thm 12.19; Krishna Prop 3.1).** In the symmetric IPV
all-pay auction — where *every* bidder pays their bid, but only the
highest bidder receives the object — the unique symmetric
strictly-increasing Bayes–Nash equilibrium bid is
$$
\beta^{\mathrm{AP}}(t) \;=\; \int_0^t z\, (n-1) F(z)^{n-2} f(z)\, dz
\;=\; \mathbb{E}\bigl[\, Y_1 \cdot \mathbf{1}\{Y_1 \le t\} \,\bigr],
$$
i.e. the expected value of the highest opponent type *conditional on*
that opponent type being below $t$ — *un-divided* by the probability
$F(t)^{n-1}$.

The expected revenue from this equilibrium equals the expected revenue
of any other standard auction format under the same symmetric IPV
hypothesis ([[mechanism_design.myerson.revenue_equivalence]]).

## Setup

- $n$ symmetric IPV bidders, types $t_i \sim F$ i.i.d. on $[0, \omega]$.
- All-pay auction: each bidder submits a sealed bid; the highest bidder
  wins the object; *every* bidder (winner and losers) pays their own
  bid. Interpret as effort or rent-seeking expenditure that is sunk
  before the outcome is determined.

## Equilibrium derivation

The interim expected payment of a type-$t$ bidder using equilibrium
strategy $\beta$ is $m(t) = \beta(t)$ (everyone pays their bid, no
conditioning on winning). The interim allocation probability is
$q(t) = F(t)^{n-1}$.

By the Myerson envelope identity for the same allocation rule as
first-price/second-price (highest-bidder-wins):
$$
m(t) - m(0) \;=\; t \cdot q(t) \;-\; \int_0^t q(z)\, dz \;=\; t F(t)^{n-1} - \int_0^t F(z)^{n-1} dz.
$$
Integration by parts converts the right-hand side to
$\int_0^t z\, (n-1) F(z)^{n-2} f(z)\, dz$, giving the formula above.

## Comparison to first-price

- **Winners pay less, losers pay more.** In first-price, only the
  winner pays $\beta^{\mathrm{FP}}(t_{\mathrm{winner}})$; in all-pay,
  *every* bidder pays $\beta^{\mathrm{AP}}(t_i)$. To equalise expected
  revenue (per the revenue-equivalence theorem
  [[mechanism_design.myerson.revenue_equivalence]]), bidders shade
  *more aggressively* in all-pay than in first-price for low types,
  with $\beta^{\mathrm{AP}}(t) < \beta^{\mathrm{FP}}(t)$ pointwise
  except at the endpoints.
- **Total expected payment equals expected second-highest type**, just
  as in first-price and second-price under symmetric IPV.

## Why it matters

The all-pay auction is the canonical model of:

- **Rent-seeking** and lobbying contests, where effort is sunk before
  the prize is awarded.
- **R&D races** and patent contests, where participation costs are
  paid by all contenders.
- **Political campaigns**, where campaign spending occurs regardless
  of victory.

The revenue equivalence with first-price and second-price is the most
striking consequence of the general revenue-equivalence theorem: three
auction formats with very different *payment* structures generate the
same expected revenue under symmetric IPV.

## Lean port (deferred)

Planned Lean module: `EconCSLib/Auction/AllPay.lean`.

Planned declarations:

- `AllPayAuction` (mechanism with transfers: payment rule
  `paymentRule b i = b i` for every $i$, regardless of winner).
- `symmetricAllPayBid` (the function $\beta^{\mathrm{AP}}$).
- `symmetricAllPayBid_bne` (the BNE certification).
- `allPay_revenue_eq_firstPrice` (revenue-equivalence corollary
  specialised to all-pay).

Dependencies: the symmetric IPV environment from
[[mechanism_design.auction.bayesian.single_item_framework]], the symmetric first-price
equilibrium ([[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]]),
and the Myerson envelope identity from
`EconCSLib/MechanismDesign/Auction/Myerson.lean`. Tracked in the MSZ Ch.12
auction gap review.

## References

- [MSZ Chapter 12, Thm 12.19] Maschler, Solan, and Zamir, *Game
  Theory*. All-pay auction equilibrium.
- [Krishna, Chapter 3, Section 3.5] Vijay Krishna, *Auction Theory*,
  2nd ed.. All-pay auction and
  comparison to first-price.
- [Riley-Samuelson 1981] John Riley and William Samuelson, "Optimal
  Auctions", *AER* 71(3):381–392. Revenue equivalence including all-pay.
