---
id: mechanism_design.auction.basic.first_price_mechanism
title: First-Price Mechanism
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.formats
  - mechanism_design.auction.basic.ordered_bid_utilities
  - mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.FirstPrice
  declarations:
    - Auction.FirstPrice.winner
    - Auction.FirstPrice.utility
    - Auction.FirstPrice.utility_winner
    - Auction.FirstPrice.utility_loser
    - Auction.FirstPrice.mechanism
    - Auction.FirstPrice.game
    - Auction.FirstPrice.game_eq_toStrategicGame
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - first-price
  - mechanism
---

# First-Price Mechanism

The first-price (pay-your-bid) auction is a sealed-bid single-item mechanism
in which the highest bidder wins and pays their own bid. All other bidders
pay nothing.

## Setup

Fix a finite, nontrivial bidder set `I` and an ordered abelian group `U` of
bids and utilities. The bid profile is `b : I → U`.

- `winner b : I` — the highest bidder, defined as `Auction.argmaxBid b`.
  The same deterministic tie-breaker as in the second-price auction
  ([[mechanism_design.auction.basic.ordered_bid_utilities]]).
- `utility v b i : U` — quasi-linear payoff at valuation profile `v`:
  $$
  u_i(v, b) \;=\; \begin{cases} v_i - b_i & i = \mathrm{winner}(b),\\ 0 & \text{otherwise}.\end{cases}
  $$

## Mechanism and strategic-game packaging

- `mechanism : MechanismWithTransfers I (fun _ => U) I U` packages the
  first-price auction as a transfer mechanism
  ([[mechanism_design.transfer.mechanisms_with_transfers]]). The report type
  is `U` per bidder, the allocation type is `I` (the winning bidder), and
  the payment rule is `paymentRule b w = if w = winner b then b w else 0`.
- `game v : StrategicGame I U` packages the same auction as a strategic
  game with the bid profile as the strategy profile and the quasi-linear
  payoff above as the utility function.
- `game_eq_toStrategicGame` certifies that `game v` agrees with
  `mechanism.toStrategicGame` for the auction utility function.

## Allocation rule is shared with second-price

The first-price and second-price auctions share the same allocation rule
(highest bidder wins, ties broken by `argmaxBid`); they differ only in the
payment rule. This is the elementary instance of the broader observation
that, within the single-parameter Myerson framework
([[mechanism_design.transfer.single_parameter_transfer_layer]]), allocation
and payment are independent design choices.

## Position in the library

The negative DSIC result is in the companion theorem node
[[mechanism_design.auction.basic.first_price_no_dsic]]: truthful bidding is not weakly
dominant in the first-price auction. Symmetric Bayesian Nash equilibria
under IPV — the standard positive analysis of first-price — are tracked at
the blueprint level in [[mechanism_design.auction.bayesian.symmetric_first_price_equilibrium]].

## References

- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  First-price auction in the basic algorithmic game theory introduction.
- [MFoGT, Chapter 12] Maschler, Solan, and Zamir, *Game Theory*. First-price auctions with private values.
- [Krishna, Chapter 2, Section 2.3] Vijay Krishna, *Auction Theory*, 2nd
  ed.. First-price sealed-bid auction
  formulation and equilibrium analysis.
