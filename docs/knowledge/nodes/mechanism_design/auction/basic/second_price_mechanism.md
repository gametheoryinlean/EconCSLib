---
id: mechanism_design.auction.basic.second_price_mechanism
title: Second-Price (Vickrey) Mechanism
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
    - EconCSLib.MechanismDesign.Auction.Vickrey
  declarations:
    - Auction.SecondPrice.winner
    - Auction.SecondPrice.secondPrice
    - Auction.SecondPrice.secondPrice_le_bid_winner
    - Auction.SecondPrice.utility
    - Auction.SecondPrice.utility_winner
    - Auction.SecondPrice.utility_loser
    - Auction.SecondPrice.utility_nonneg
    - Auction.SecondPrice.mechanism
    - Auction.SecondPrice.game
    - Auction.SecondPrice.game_eq_toStrategicGame
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - vickrey
  - second-price
  - mechanism
---

# Second-Price (Vickrey) Mechanism

The second-price (Vickrey) auction is a sealed-bid single-item mechanism in
which the bidder submitting the highest bid wins the item, and the winner pays
the second-highest bid. All other bidders pay nothing.

## Setup

Fix a finite, nontrivial bidder set `I` and an ordered abelian group `U` of
bids and utilities (for example `ℚ` or `ℝ`). Bids form a profile `b : I → U`.

- `winner b : I` — the bidder with the highest bid, defined as
  `Auction.argmaxBid b`. Ties are broken by the deterministic argmax of the
  basic auction layer ([[mechanism_design.auction.basic.ordered_bid_utilities]]).
- `secondPrice b : U` — the highest bid among all bidders other than the
  winner, defined as `Auction.maxBidExcluding b (winner b)`.
- `utility v b i : U` — quasi-linear payoff for bidder `i` at valuation
  profile `v` and bid profile `b`:
  $$
  u_i(v, b) \;=\; \begin{cases} v_i - \mathrm{secondPrice}(b) & i = \mathrm{winner}(b),\\ 0 & \text{otherwise}.\end{cases}
  $$

## Basic properties

- `secondPrice_le_bid_winner`: the second-highest bid never exceeds the
  winning bid, $\mathrm{secondPrice}(b) \le b(\mathrm{winner}\,b)$.
- `utility_winner`, `utility_loser`: the case analysis of `utility` as
  computational lemmas.
- `utility_nonneg`: truthful bidding ($b_i = v_i$) yields nonnegative payoff
  for bidder `i`, regardless of opponents' bids.

## Mechanism and strategic-game packaging

- `mechanism : MechanismWithTransfers I (fun _ => U) I U` packages the
  second-price auction as a transfer mechanism
  ([[mechanism_design.transfer.mechanisms_with_transfers]]): the report type
  is `U` per bidder, the allocation type is `I` (the winning bidder), and
  payments live in `U` with `paymentRule b w = if w = winner b then
  secondPrice b else 0`.
- `game v : StrategicGame I U` packages the same mechanism as a strategic
  game with bid profile `b` as the strategy profile and the quasi-linear
  payoff above as the utility function.
- `game_eq_toStrategicGame` certifies that `game v` agrees with
  `mechanism.toStrategicGame` for the auction utility function.

## Position in the library

The second-price auction is an instance of the general transfer-mechanism
interface ([[mechanism_design.transfer.mechanisms_with_transfers]]). Its
DSIC property is proved in the companion theorem node
[[mechanism_design.auction.basic.second_price_dsic]]. The first-price auction with the same
allocation rule but different payment is in
[[mechanism_design.auction.basic.first_price_mechanism]].

## References

- [MFoGT, Chapter 1, Section 1.2.4 and Exercise 4] Maschler, Solan, and
  Zamir, *Game Theory*. Vickrey auction example.
- [AGT, Chapter 9, Section 9.3.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. Vickrey
  auction as the canonical truthful single-item mechanism.
- [Krishna, Chapter 2] Vijay Krishna, *Auction Theory*, 2nd ed.. Standard second-price sealed-bid auction
  formulation.
- [Vickrey 1961] William Vickrey, "Counterspeculation, Auctions, and
  Competitive Sealed Tenders", *Journal of Finance* 16(1):8–37.
