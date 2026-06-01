---
id: mechanism_design.auction.basic.formats
title: Basic Auction Formats
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.basic
uses:
  - mechanism_design.transfer.single_parameter_transfer_layer
  - mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.AuctionBasic
  declarations:
    - SingleItemAuction
    - MultiItemBundle
    - CombinatorialAllocation
    - CombinatorialAuction
    - CombinatorialAuction.IsFeasible
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - mechanism-design
  - transfers
---

# Basic Auction Formats

The basic auction layer specialises the
generic `MechanismWithTransfers`
([[mechanism_design.transfer.mechanisms_with_transfers]]) interface to two
classical auction shapes: single-item auctions and multi-item auctions.

## Single-item auction

`SingleItemAuction I V P` extends
`MechanismWithTransfers I (fun _ => V) (Option I) P` with no extra data.
The components are:

- **Bidders**: a finite (typically) index type `I`.
- **Bids**: each bidder reports a scalar value in `V`.
- **Allocation**: the outcome type is `Option I` —
  - `some i` means bidder `i` receives the single item;
  - `none` means the item is withheld (e.g. the reserve price was not met).
- **Payments**: per-bidder transfers in `P`.

Importantly, the structure does not commit to *which* bidder wins. The
specific allocation rule (highest bidder, weighted scoring, randomised
allocation, …) is supplied by each concrete instantiation
— see [[mechanism_design.auction.basic.second_price_mechanism]] and
[[mechanism_design.auction.basic.first_price_mechanism]].

## Multi-item auction

`CombinatorialAuction I k V P` extends
`MultipleParameterMechanism I (CombinatorialAllocation I k) V P`:

- **Bids**: each bidder submits a valuation function on full allocation
  profiles.
- **Allocation**: a function $a : I \to \mathrm{Finset}\,(\mathrm{Fin}\,k)$
  assigning a bundle of items to each bidder.

The structure imposes no feasibility constraint by default; the
companion predicate `CombinatorialAuction.IsFeasible` records the
no-double-allocation requirement:
$$
\forall i \ne j.\; \mathrm{allocationRule}(b, i) \cap \mathrm{allocationRule}(b, j) = \emptyset.
$$
Equivalently, the allocation defines a (possibly partial) assignment of
distinct items to distinct bidders.

## Position in the library

These formats provide the *outcome geometry*: what bids look like and how
allocations are encoded. They sit above the generic transfer-mechanism
interface and below concrete mechanisms (Vickrey, first-price, VCG,
Myerson, …) that fix allocation and payment rules. The single-parameter
layer ([[mechanism_design.transfer.single_parameter_transfer_layer]]) is
the scalar-allocation cousin used for Myerson-style theory; multi-item
auctions naturally feed into the multi-parameter VCG analysis
([[mechanism_design.vcg.welfare_and_payments]]).

## References

- [Krishna, Chapters 2-3] Vijay Krishna, *Auction Theory*, 2nd ed.. Standard sealed-bid auction formats and
  private-value auction models.
- [Krishna, Chapter 11] Vijay Krishna, *Auction Theory*, 2nd ed.. Multi-object auctions and bundle
  allocation.
- [AGT, Chapter 1, Section 1.3.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  First-price and second-price sealed-bid auctions as basic algorithmic
  game theory examples.
- [AGT, Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Combinatorial auctions and feasibility constraints.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:auction_basic_formats` in `blueprint/src/content.tex`.
