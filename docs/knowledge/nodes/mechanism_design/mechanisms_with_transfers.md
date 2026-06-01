---
id: mechanism_design.transfer.mechanisms_with_transfers
title: Mechanisms With Transfers
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.transfer
uses:
- mechanism_design.basic.direct_mechanism_interface
- mechanism_design.basic.dsic_predicate
- mechanism_design.basic.ex_post_ir_predicate
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Transfer
  declarations:
  - MechanismWithTransfers
  - MechanismWithTransfers.quasiLinearUtility
  - MechanismWithTransfers.toMechanism
  - MechanismWithTransfers.toStrategicGame
  - MechanismWithTransfers.isDSIC
  - MechanismWithTransfers.isExPostIR
  - MechanismWithTransfers.toQuasiLinearGame
  - MechanismWithTransfers.isQuasiLinearDSIC
  - MechanismWithTransfers.isQuasiLinearExPostIR
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- transfers
- quasi-linear-utility
---

# Mechanisms With Transfers

A mechanism with transfers separates the allocation rule from the payment rule.
Quasi-linear utility is supplied by combining the value of the selected
allocation with the agent's payment.

The transfer interface can be viewed as a direct mechanism, as an induced
strategic game, and as a source of DSIC and ex-post IR predicates specialized to
quasi-linear utilities.

## References

- [AGT, Chapter 9, Section 9.3.2, Def. 9.14] Nisan, Roughgarden,
  Tardos, and Vazirani, *Algorithmic Game Theory*. Direct mechanisms with allocation
  and payment rules.
- [AGT, Chapter 9, Sections 9.3.3-9.3.4] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Quasi-linear utilities and VCG-style transfer mechanisms.

## Used by auctions

[[mechanism_design.auction.basic.formats]] (basic auction formats use the
transfer interface), [[mechanism_design.auction.basic.first_price_mechanism]]
(first-price mechanism as a transfer mechanism),
[[mechanism_design.auction.basic.second_price_mechanism]] (second-price
mechanism as a transfer mechanism).

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_transfer_interface` in `blueprint/src/content.tex`.
