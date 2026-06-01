---
id: mechanism_design.myerson.payment_formula
title: Myerson Payment Formula
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.transfer.single_parameter_transfer_layer
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Myerson
  declarations:
  - myersonPayment
  - ZeroNormalized
  - myersonPayment_zeroNormalized
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- myerson
- single-parameter
---

# Myerson Payment Formula

For single-parameter mechanisms over real values, the Myerson module defines
the canonical payment formula associated to an allocation rule and records the
zero-normalized payment condition.

## References

- [AGT, Chapter 9, Section 9.5.4, Thm. 9.36] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Payment formulae for monotone
  single-parameter allocation rules.
- [Myerson 1981, Section 2] Myerson, R. B. "Optimal auction design."
  *Mathematics of Operations Research* 6(1):58-73. Canonical
  single-parameter payment identities in auction-design notation.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_myerson_payment_interface` in `blueprint/src/content.tex`.
