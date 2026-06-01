---
id: mechanism_design.auction.basic.bid_profile_supports
title: Bid-Profile Supports
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
    - Auction.BidProfile.Nonnegative
    - Auction.BidProfile.InSet
    - Auction.BidProfile.InBox
    - Auction.BidProfile.StrategyMapsBoxToBox
    - Auction.BidProfile.inBox_iff_inSet_Icc
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - bid-profile
  - support
---

# Bid-Profile Supports

The basic auction layer supplies a small family of *support* predicates on
bid profiles — predicates that constrain the admissible bid space without
modifying the underlying auction format itself. These are useful when
analysing auctions with bounded bid domains, sign restrictions, or
strategy-set constraints.

## Predicates

For a fixed bidder set `I` and an ordered scalar bid type `V` (typically
`ℝ`):

- **`Auction.BidProfile.Nonnegative b`** — every bid is nonnegative,
  $\forall i.\; b_i \ge 0$. Captures the standard convention in private-
  value auctions that bids represent willingness-to-pay.
- **`Auction.BidProfile.InSet b S`** — for a per-bidder admissible set
  $S_i \subseteq V$, the profile satisfies $\forall i.\; b_i \in S_i$.
  Captures heterogeneous strategy spaces.
- **`Auction.BidProfile.InBox b ℓ u`** — for per-bidder lower/upper
  bounds $\ell_i, u_i$, the profile lies in the rectangular box
  $\forall i.\; \ell_i \le b_i \le u_i$.
- **`Auction.BidProfile.StrategyMapsBoxToBox σ ℓ u ℓ' u'`** — a strategy
  $\sigma : V \to V$ maps the input bid box $[\ell, u]$ into the output
  bid box $[\ell', u']$. Captures Lipschitz/contraction conditions for
  best-response dynamics in bounded auctions.

## Identification with closed intervals

`Auction.BidProfile.inBox_iff_inSet_Icc` certifies that the
"rectangular box" predicate `InBox b ℓ u` coincides pointwise with
`InSet b (fun i => Set.Icc ℓ_i u_i)`. This makes box-constrained bid
spaces interoperable with the Mathlib `Set.Icc` API (continuity,
compactness, integration).

## Usage

The support predicates are not part of any concrete auction's definition;
they are *side conditions* attached to theorems about bounded or
sign-restricted auctions. Typical use cases:

- Existence of equilibria in compact bid spaces (closed boxes).
- Single-crossing arguments in Bayesian first-price auctions, where bids
  are restricted to a bounded interval $[0, \omega]$ matching the type
  support.
- Best-response correspondences for fixed-point arguments.

## References

- [Krishna, Chapters 2-3] Vijay Krishna, *Auction Theory*, 2nd ed.. Bid and valuation domains for standard
  sealed-bid auction models with bounded support.
- [AGT, Chapter 9, Sections 9.3-9.5] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Reports, strategy spaces, and payment mechanisms in direct mechanisms.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:auction_basic_bid_support` in `blueprint/src/content.tex`.
