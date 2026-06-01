---
id: mechanism_design.vcg.welfare_and_payments
title: VCG Welfare And Payments
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.vcg
uses:
- mechanism_design.transfer.multiple_parameter_transfer_layer
- mechanism_design.vcg.social_welfare
- mechanism_design.vcg.welfare_without
- mechanism_design.vcg.payment_identity
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.VCG
  declarations:
  - vcgPayment
  - VCGMechanism
  - VCGTransferMechanism
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- vcg
- social-welfare
---

# VCG Welfare And Payments

The VCG interface defines social welfare for reported valuation profiles,
efficient allocations, welfare without a given agent, Clarke-pivot payments,
and the induced direct and transfer mechanisms.

## References

- [AGT, Chapter 9, Section 9.3.3, Def. 9.16] Nisan, Roughgarden,
  Tardos, and Vazirani, *Algorithmic Game Theory*. VCG mechanisms and welfare-maximizing
  allocation rules.
- [AGT, Chapter 9, Section 9.3.4, Def. 9.19] Nisan, Roughgarden,
  Tardos, and Vazirani, *Algorithmic Game Theory*. Clarke-pivot payments.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_vcg_interface` in `blueprint/src/content.tex`.
