---
id: mechanism_design.transfer.multiple_parameter_transfer_layer
title: Multiple-Parameter Transfer Layer
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.transfer
uses:
- mechanism_design.transfer.mechanisms_with_transfers
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Transfer
  declarations:
  - MultipleParameterMechanism
  - MultipleParameterMechanism.Valuation
  - MultipleParameterMechanism.valueOfAllocation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- multiple-parameter
- transfers
---

# Multiple-Parameter Transfer Layer

In a multiple-parameter mechanism, each agent reports a valuation function over
the allocation space. This is the abstract transfer-mechanism layer used by
VCG-style constructions.

## References

- [AGT, Chapter 9, Sections 9.3.2-9.3.3] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Multi-parameter valuation functions, outcomes, and transfer mechanisms.
- [AGT, Chapter 12, Section 12.3] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Multidimensional mechanism-design domains in combinatorial-auction settings.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_multiple_parameter_interface` in `blueprint/src/content.tex`.
