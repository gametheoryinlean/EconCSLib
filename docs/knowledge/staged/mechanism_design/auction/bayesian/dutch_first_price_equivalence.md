---
id: mechanism_design.auction.bayesian.dutch_first_price_equivalence
title: Dutch ≡ First-Price Strategic Equivalence
kind: theorem
status: staged
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.bayesian
uses:
  - mechanism_design.auction.basic.first_price_mechanism
  - mechanism_design.auction.bayesian.single_item_framework
verification:
  statement: accepted
  proof: gap
tags:
  - auction
  - dutch-auction
  - first-price
  - strategic-equivalence
---

# Dutch ≡ First-Price Strategic Equivalence

**Theorem (MSZ Thm 12.3; Krishna Prop 2.1).** Under independent private
values, the Dutch (descending-price open-outcry) auction and the
sealed-bid first-price auction
([[mechanism_design.auction.basic.first_price_mechanism]]) are strategically equivalent:
they induce the same extensive-form game (up to information set
relabelling) and hence the same set of equilibrium strategies and
outcomes.

## Setup

- **Dutch auction**: the auctioneer announces a high opening price and
  decreases it continuously over time. The first bidder to stop the
  clock wins the item at the current price.
- **First-price sealed-bid auction**: each bidder simultaneously
  submits a sealed bid; the highest bidder wins and pays their own bid.

In both formats, a bidder's only strategic choice is *the price at
which to commit*. In Dutch this is the stopping price; in sealed-bid
first-price this is the submitted bid. Under the standard observability
assumption (a Dutch bidder learns nothing about opponents before
deciding when to stop), the two extensive forms coincide.

## Proof route

The proof has two parts:

1. **Strategy spaces coincide.** A bidder's pure strategy in the Dutch
   auction is a real number $b_i \in \mathbb{R}_{\ge 0}$ — the stopping
   price as a function of (no observed information). The same strategy
   space describes the first-price sealed-bid auction.
2. **Outcomes coincide.** In both formats, given any pure-strategy
   profile $b : I \to \mathbb{R}_{\ge 0}$, the winner is
   $\mathrm{argmax}_i\, b_i$ and the payment is $\max_i b_i$. The
   allocation and payment maps are pointwise equal.

Together: identical extensive forms ⇒ identical strategic-game
reductions ⇒ identical equilibria.

## Why it matters

The Dutch-first-price equivalence is the simplest example of the
broader *revenue equivalence* phenomenon: auction formats can differ in
their dynamic structure while implementing the same allocation and
payment rules, and hence the same revenue under any equilibrium.

This equivalence motivates the focus on the sealed-bid formulation in
theoretical analysis: any result proved for sealed-bid first-price
applies verbatim to Dutch, including the symmetric IPV equilibrium
formula ([[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]]) and
the revenue comparison with second-price
([[mechanism_design.myerson.revenue_equivalence]]).

## Lean port (deferred)

Planned Lean module: `EconCSLib/Auction/Dutch.lean`.

Planned declarations:

- `DutchAuction` (extensive-form representation)
- `DutchAuction.toFirstPriceMechanism` (strategic equivalence map)
- `DutchAuction.equivalence_first_price_mechanism` (strategic equivalence
  theorem, stated as equality of induced strategic games).

Dependencies on yet-to-formalise pieces: an extensive-form auction
encoding that respects the continuous descending-price clock; the
information-set definition that captures the "no observation before
stopping" rule. The first-price sealed-bid side is already in
`EconCSLib/Auction/FirstPrice.lean`. Tracked in the MSZ Ch.12 auction
gap review.

## References

- [MSZ Chapter 12, Thm 12.3] Maschler, Solan, and Zamir, *Game Theory*. Dutch-first-price strategic equivalence.
- [Krishna, Chapter 2, Proposition 2.1] Vijay Krishna, *Auction Theory*,
  2nd ed.. Dutch auction and its
  equivalence to first-price.
- [Vickrey 1961] William Vickrey, "Counterspeculation, Auctions, and
  Competitive Sealed Tenders", *Journal of Finance* 16(1):8–37.
  Original observation of the equivalence.
