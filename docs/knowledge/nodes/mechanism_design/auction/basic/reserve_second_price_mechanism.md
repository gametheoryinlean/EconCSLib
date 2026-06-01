---
id: mechanism_design.auction.basic.reserve_second_price_mechanism
title: Reserve Second-Price Mechanism
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.second_price_mechanism
  - mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.ReserveVickrey
  declarations:
    - Auction.ReserveSecondPrice.clearingPrice
    - Auction.ReserveSecondPrice.allocation
    - Auction.ReserveSecondPrice.utility
    - Auction.ReserveSecondPrice.game
    - Auction.ReserveSecondPrice.mechanism
    - Auction.ReserveSecondPrice.allocation_eq_some_iff
    - Auction.ReserveSecondPrice.allocation_eq_none_iff
    - Auction.ReserveSecondPrice.clearingPrice_le_bid_of_allocation_eq_some
    - Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some
    - Auction.ReserveSecondPrice.mechanism_payment_of_allocation_ne_some
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - vickrey
  - second-price
  - reserve-price
  - mechanism
---

# Reserve Second-Price Mechanism

The reserve second-price auction is the Vickrey auction with a seller reserve.
The highest bidder receives the item only if the highest bid meets the reserve;
otherwise the item is withheld.  When the item is sold, the winner pays the
maximum of the reserve and the second-highest bid.

## Lean objects

The module `EconCSLib.MechanismDesign.Auction.ReserveVickrey` reuses the
second-price primitives from
[[mechanism_design.auction.basic.second_price_mechanism]].

- `clearingPrice reserve b` is
  \(\max(\mathrm{reserve}, \mathrm{secondPrice}(b))\).
- `allocation reserve b : Option I` is `some i` when bidder `i` is the
  selected highest bidder and the reserve is met; it is `none` when the item is
  withheld.
- `utility reserve v b i` is the quasi-linear payoff: the allocated bidder gets
  value minus clearing price, and all other bidders get zero.
- `mechanism reserve` packages the rule as a `MechanismWithTransfers` with
  allocation type `Option I`.

## Basic facts

The formalization records the expected case analysis:

- `allocation_eq_some_iff` characterizes the sale case.
- `allocation_eq_none_iff` characterizes the no-sale case.
- `clearingPrice_le_bid_of_allocation_eq_some` shows that the allocated bidder
  never pays more than her bid.

These facts are the local algebraic core used in the DSIC proof
[[mechanism_design.auction.basic.reserve_second_price_dsic]].

## References

- [AGT, Chapter 9, Section 9.3] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
- [Krishna, Chapter 2] Vijay Krishna, *Auction Theory*, 2nd ed..
- [MSZ, Chapter 12] Maschler, Solan, and Zamir, *Game Theory*.
