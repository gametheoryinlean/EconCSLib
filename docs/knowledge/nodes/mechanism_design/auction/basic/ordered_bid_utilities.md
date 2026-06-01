---
id: mechanism_design.auction.basic.ordered_bid_utilities
title: Ordered-Bid Utilities
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.auction.basic.formats
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.AuctionBasic
  declarations:
    - Auction.maxBid
    - Auction.exists_maxBid
    - Auction.argmaxBid
    - Auction.argmaxBid_eq_maxBid
    - Auction.bid_le_maxBid
    - Auction.eq_argmaxBid_of_strict_max
    - Auction.maxBidExcluding
    - Auction.maxBidExcluding_le_maxBid
    - Auction.maxBidExcluding_eq_maxBid_of_not_argmax
    - Auction.maxBidExcluding_le_argmaxBid_bid
    - Auction.maxBidExcluding_update_self
tags:
  - auction
  - bids
  - argmax
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
---

# Ordered-Bid Utilities

For a finite, nontrivial set of bidders `I` and a linearly ordered scalar
bid type `V`, the auction layer provides three computational utilities
operating on bid profiles `b : I → V`: highest bid, the bidder achieving
it, and the highest bid excluding any chosen bidder.

These are *purely mathematical* tools — they do not commit any concrete
auction to using them as the winner-selection rule. Each instantiated
auction explicitly states which of these utilities, if any, drive its
allocation rule.

## Highest bid

- **`Auction.maxBid b : V`** is the supremum of `b` over the finite
  bidder set, implemented as `Finset.sup' Finset.univ univ_nonempty b`.
- **`Auction.exists_maxBid`** witnesses that some bidder attains the
  maximum: $\exists i.\; b_i = \mathrm{maxBid}(b)$.

## Argmax bidder

- **`Auction.argmaxBid b : I`** is a deterministic choice of a bidder
  achieving the maximum, built via `Classical.choose` from
  `exists_maxBid`. It is `noncomputable` and serves only as a tie-break
  rule.
- **`Auction.argmaxBid_eq_maxBid`** records that
  $b(\mathrm{argmaxBid}\,b) = \mathrm{maxBid}(b)$.
- **`Auction.bid_le_maxBid j`** records the universal upper bound
  $b_j \le b(\mathrm{argmaxBid}\,b)$.
- **`Auction.eq_argmaxBid_of_strict_max`** says that if some bidder $i$
  *strictly* outbids everyone else, then `argmaxBid b = i` — uniqueness
  of the argmax up to ties.

## Highest bid excluding a bidder

Under additionally `[DecidableEq I]`:

- **`Auction.maxBidExcluding b i : V`** is the supremum of `b` over the
  bidder set with `i` removed: `(Finset.univ.erase i).sup' ⋯ b`.
- **`Auction.maxBidExcluding_le_maxBid`** — removing a bidder cannot
  increase the maximum.
- **`Auction.maxBidExcluding_eq_maxBid_of_not_argmax`** — if `i` is *not*
  the argmax bidder, then `maxBidExcluding b i = maxBid b`. Removing a
  non-maximal bidder does not change the maximum.
- **`Auction.maxBidExcluding_le_argmaxBid_bid`** — applied to
  `i = argmaxBid b`, this is the standard "second highest ≤ highest"
  inequality used in Vickrey analyses.
- **`Auction.maxBidExcluding_update_self`** — overwriting bidder `i`'s
  own bid leaves `maxBidExcluding b i` unchanged. This is the key
  identity behind Vickrey weak dominance: an agent's payment depends on
  everyone *but* themselves.

## How concrete auctions use these utilities

- The second-price (Vickrey) auction
  ([[mechanism_design.auction.basic.second_price_mechanism]]) sets the winner to
  `argmaxBid b` and the price to `maxBidExcluding b (argmaxBid b)`.
- The first-price auction ([[mechanism_design.auction.basic.first_price_mechanism]]) also
  uses `argmaxBid b` for the winner, but charges the winner's own bid.
- Both use `maxBidExcluding_update_self` (Vickrey) or
  `eq_argmaxBid_of_strict_max` (first-price counterexample) in
  incentive-property proofs.

## References

- [MFoGT, Chapter 1, Section 1.2.4 and Exercise 4] Maschler, Solan, and
  Zamir, *Game Theory*. Highest-bid and
  second-highest-bid comparisons in the Vickrey auction example.
- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Second-price auction payoffs and ordered bid comparisons.
- [Krishna, Chapter 2] Vijay Krishna, *Auction Theory*, 2nd ed.. Standard ordering of sealed bids and
  highest-/second-highest-bid statistics.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:auction_basic_ordered_bids` in `blueprint/src/content.tex`.
