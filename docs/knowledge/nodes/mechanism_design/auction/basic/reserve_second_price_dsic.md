---
id: mechanism_design.auction.basic.reserve_second_price_dsic
title: Reserve Second-Price Truth-Telling Is Dominant
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.reserve_second_price_mechanism
  - mechanism_design.auction.basic.second_price_dsic
  - mechanism_design.basic.dsic_predicate
  - game_theory.strategic_game.weakly_dominant_strategy
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.ReserveVickrey
  declarations:
    - Auction.ReserveSecondPrice.utility_nonneg
    - Auction.ReserveSecondPrice.valuation_is_dominant
    - Auction.ReserveSecondPrice.truthful_weakly_dominant
    - Auction.ReserveSecondPrice.game_eq_toStrategicGame
    - Auction.ReserveSecondPrice.mechanism_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - vickrey
  - reserve-price
  - dsic
  - weakly-dominant
---

# Reserve Second-Price Truth-Telling Is Dominant

For every reserve price, truthful bidding is a weakly dominant strategy in the
reserve second-price auction
([[mechanism_design.auction.basic.reserve_second_price_mechanism]]).

Formally, for valuation profile \(v : I \to U\), bidder \(i\), and bid profile
\(b\), replacing bidder \(i\)'s bid by \(v_i\) weakly increases bidder \(i\)'s
utility:
\[
u_i(v,b) \le u_i(v,b[i \mapsto v_i]).
\]

## Lean form

- `utility_nonneg` proves that truthful bidding gives nonnegative payoff.
- `valuation_is_dominant` proves the direct utility inequality.
- `truthful_weakly_dominant` packages the same result as `IsWeaklyDominant` in
  the induced strategic game.
- `mechanism_isDSIC` lifts the theorem to the
  `MechanismWithTransfers.isDSIC` predicate.

## Proof idea

The proof is the Vickrey dominance argument with one extra threshold.  Bidder
`i`'s own bid does not change the highest bid among opponents, so the critical
price faced by `i` is the maximum of the reserve and the highest opposing bid.
Truthful bidding wins exactly when \(v_i\) clears that threshold; in the winning
case the payoff is nonnegative, and in the losing case the payoff is zero.

## References

- [AGT, Chapter 9, Section 9.3] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
- [Krishna, Chapter 2] Vijay Krishna, *Auction Theory*, 2nd ed..
- [Vickrey 1961] William Vickrey, "Counterspeculation, Auctions, and
  Competitive Sealed Tenders", *Journal of Finance* 16(1):8-37.
