---
id: mechanism_design.auction.bayesian.entry_fee_and_reserve_price
title: Entry Fees And Reserve Prices In IPV Auctions
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
  - mechanism_design.myerson.optimal_auction
  - mechanism_design.myerson.reserve_price
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - reserve-price
  - entry-fee
  - ipv
  - revenue-improvement
---

# Entry Fees And Reserve Prices In IPV Auctions

**Theorem (MSZ Thm 12.23, Cor 12.24; Krishna Ch 2.5).** In a symmetric
IPV auction (first-price or second-price), a positive reserve price
$r > 0$ that excludes all bidders with valuation below $r$ strictly
increases expected revenue compared to the no-reserve auction, provided
the seller's valuation $v_0$ satisfies $v_0 < r^* = \psi^{-1}(0)$, where
$\psi(t) = t - (1 - F(t))/f(t)$ is the *virtual valuation* and $r^*$ is
the *optimal reserve price*. An entry fee $e$ paid by each participating
bidder is, in the symmetric IPV setting, payoff- and revenue-equivalent
to a reserve price $r(e)$ that solves $r - e = \mathbb{E}[\text{net
expected payoff at type } r]$.

## Setup

- Symmetric IPV environment as in
  [[mechanism_design.auction.bayesian.single_item_framework]]: types $t_i \sim F$ i.i.d.
  on $[0, \omega]$ with continuous positive density $f$.
- **Reserve price $r$**: the auctioneer commits to not sell the object
  for less than $r$. In first-price, bidders below $r$ drop out (or
  equivalently bid $0$ and lose); bidders above $r$ bid in equilibrium
  conditional on not facing a binding reserve. In second-price, the
  price paid by the winner is $\max(r, \text{second-highest bid})$.
- **Entry fee $e$**: each bidder who participates pays a fixed fee $e
  \ge 0$ regardless of outcome. Bidders enter iff their expected
  surplus net of $e$ is nonnegative.

## Optimal reserve (regular case)

When the virtual-valuation function $\psi(t) = t - (1 - F(t))/f(t)$ is
monotone non-decreasing (the *regular case* of
[[mechanism_design.myerson.optimal_auction]]), the revenue-maximising
reserve in any standard auction is
$$
r^* \;=\; \psi^{-1}(\max(v_0, 0)),
$$
where $v_0$ is the seller's own valuation. Setting $r = r^*$ optimises
revenue *for the auctioneer with valuation $v_0$*.

This is the auction-side specialisation of
[[mechanism_design.myerson.reserve_price]] — the optimal mechanism in
the symmetric IPV setting is just the second-price auction (or its
revenue-equivalent first-price counterpart) with reserve $r^*$.

## Entry fee ↔ reserve price equivalence

A reserve price $r$ and an entry fee $e$ are equivalent in the
following sense:

- An entry fee $e$ induces a *participation threshold* $\hat t(e)$: a
  bidder enters iff their expected interim surplus
  $U(t) - e \ge 0$, i.e. iff $t \ge \hat t(e)$ where $\hat t$ is the
  unique solution of $U(\hat t(e)) = e$.
- A reserve price $r$ induces the threshold $\hat t = r$ directly:
  bidders below $r$ cannot win.
- For each entry fee $e$ there is a unique reserve $r(e)$ producing the
  same participation threshold, and the two regimes generate the same
  expected revenue.

This equivalence breaks under risk aversion or budget constraints,
which is one motivation for the entry-fee formulation in some
practical settings.

## Why it matters

The reserve-price result is the prototypical example of how a *small*
amount of seller commitment power dramatically improves revenue: even
without optimising over arbitrary mechanisms (as Myerson's general
optimal auction does), simply adding a reserve to a standard auction
already extracts a substantial portion of the optimal revenue.

The entry-fee variant captures real-world auction conventions (e.g.
bidder pre-qualification, deposit requirements) and gives the
auctioneer a second instrument to fine-tune participation.

## Lean port (deferred)

Planned Lean modules: `EconCSLib/Auction/Reserve.lean` and
`EconCSLib/Auction/EntryFee.lean`.

Planned declarations:

- `SecondPriceAuctionWithReserve` (mechanism with reserve).
- `secondPriceWithReserve_isDSIC` (truth-telling remains DSIC).
- `optimalReserve` (closed-form $r^*$ under regularity).
- `secondPriceWithReserve_revenue_ge_secondPrice_under_regularity`.
- `entryFee_reserve_equivalence` (revenue equivalence theorem).

Dependencies: virtual valuation and Myerson regularity (already in
`EconCSLib/MechanismDesign/Auction/Myerson.lean`); the IPV single-item
framework ([[mechanism_design.auction.bayesian.single_item_framework]]); the
revenue-equivalence theorem
([[mechanism_design.myerson.revenue_equivalence]]). Tracked in the
MSZ Ch.12 auction gap review.

## References

- [MSZ Chapter 12, Thm 12.23 and Cor 12.24] Maschler, Solan, and
  Zamir, *Game Theory*. Reserve prices
  and entry fees in IPV auctions.
- [Krishna, Chapter 2, Section 2.5] Vijay Krishna, *Auction Theory*,
  2nd ed.. Reserve prices in
  first-price and second-price auctions.
- [Myerson 1981] Roger Myerson, "Optimal Auction Design",
  *Math. Oper. Res.* 6(1):58–73. Derivation of the optimal reserve
  via virtual valuations.
- [Riley-Samuelson 1981] John Riley and William Samuelson, "Optimal
  Auctions", *AER* 71(3):381–392. Reserve prices and revenue
  improvement.
