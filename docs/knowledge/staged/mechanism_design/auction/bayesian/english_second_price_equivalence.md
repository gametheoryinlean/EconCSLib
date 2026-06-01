---
id: mechanism_design.auction.bayesian.english_second_price_equivalence
title: English ≡ Second-Price IPV Equivalence
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.basic.second_price_mechanism
  - mechanism_design.auction.basic.second_price_dsic
  - mechanism_design.auction.bayesian.single_item_framework
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - english-auction
  - japanese-auction
  - second-price
  - strategic-equivalence
  - ipv
---

# English ≡ Second-Price IPV Equivalence

**Theorem (MSZ Thm 12.7; Krishna Prop 2.2).** Under independent private
values, the English (ascending-price open-outcry) auction is
strategically equivalent in *weakly dominant* strategies to the
sealed-bid second-price (Vickrey) auction
([[mechanism_design.auction.basic.second_price_mechanism]]): the dominant strategy
"stay in until the price reaches my own valuation" yields the same
allocation and payment as truthful bidding in the second-price auction.

This is a *weaker* equivalence than the Dutch–first-price equivalence
([[mechanism_design.auction.bayesian.dutch_first_price_equivalence]]) — extensive-form
strategy spaces differ — but the dominant-strategy outcomes coincide.

## Setup

Two formats of the open ascending-price auction are usually considered:

- **English (Krishna)**: the price clock rises continuously; bidders
  drop out publicly; the last remaining bidder wins at the drop-out
  price of the second-last.
- **Japanese / Milgrom-Weber**: bidders post a "stay-in" indicator that
  flips to "drop-out" at a price each chooses; the last remaining
  bidder wins at the drop-out price of the second-last. This is the
  cleanest model for the equivalence.

In both formats, under IPV, the natural strategy is to stay in as long
as the current price is below one's own valuation $t_i$ and drop out
when it reaches $t_i$. The result is:

- The bidder with the highest valuation wins.
- The price paid equals the *second-highest* valuation (the drop-out
  price of the last competitor).

These are exactly the allocation and payment of the second-price
auction at truthful bidding $b_i = t_i$.

## Proof route

1. **Dominance in English/Japanese.** Staying in until $t_i$ is weakly
   dominant: dropping out earlier risks losing an item that could be
   bought below $t_i$; staying in longer risks paying more than $t_i$.
   This is the open-outcry analogue of the Vickrey dominance argument
   ([[mechanism_design.auction.basic.second_price_dsic]]).
2. **Outcome coincidence.** Under these dominant strategies, the
   winner is $\mathrm{argmax}_i\, t_i$ and the payment is
   $\max_{j \ne \mathrm{winner}}\, t_j$ — identical to the
   second-price auction at truthful bidding.

Outside the IPV setting (e.g. with affiliated values), the
*open-outcry* English auction can reveal information about opponents'
signals during the bidding process, which the sealed-bid second-price
cannot. The two formats are then no longer equivalent (Krishna
Chapter 6); this gap is the basis of *linkage* and *winner's curse*
analyses.

## Why it matters

The English-second-price equivalence is the practical bridge between
the open-outcry auction format used in art and asset markets and the
theoretical sealed-bid model used in mechanism-design. It justifies
analysing the Vickrey auction as a stand-in for English under IPV,
and motivates the *interdependent values* extension where the
equivalence breaks.

## Lean port (deferred)

Planned Lean module: `EconCSLib/Auction/English.lean`.

Planned declarations:

- `EnglishAuction` / `JapaneseAuction` (extensive-form
  representation)
- The "stay-in-until-valuation" strategy and its weak dominance.
- `EnglishAuction.equivalence_second_price_mechanism_under_ipv`
  (strategic equivalence theorem under IPV).

Dependencies on yet-to-formalise pieces: open-outcry extensive form,
public drop-out information sets, and an IPV-environment specification.
The second-price side is fully in
`EconCSLib/Auction/Vickrey.lean`. Tracked in the MSZ Ch.12 auction gap
review.

## References

- [MSZ Chapter 12, Thm 12.7] Maschler, Solan, and Zamir, *Game Theory*. English-second-price equivalence under
  IPV.
- [Krishna, Chapter 2, Section 2.4] Vijay Krishna, *Auction Theory*,
  2nd ed.. Japanese auction and its
  equivalence to the second-price sealed-bid auction.
- [Krishna, Chapter 6] Vijay Krishna, *Auction Theory*, 2nd ed.. Breakdown of equivalence under
  interdependent values.
- [Milgrom-Weber 1982] Paul Milgrom and Robert Weber, "A theory of
  auctions and competitive bidding", *Econometrica* 50(5):1089–1122.
  Japanese auction formulation.
