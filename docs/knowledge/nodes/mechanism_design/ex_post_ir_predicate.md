---
id: mechanism_design.basic.ex_post_ir_predicate
title: Ex-Post Individual Rationality Predicate
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.basic
uses:
- mechanism_design.basic.direct_mechanism_interface
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.MechBasic
  declarations:
  - Mechanism.IsExPostIR
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
- mechanism-design
- individual-rationality
---

# Ex-Post Individual Rationality Predicate

A direct mechanism is ex-post individually rational when truthful reporting gives
each agent nonnegative utility for every true type profile and every profile of
the other agents' reports.

The predicate is ex-post because it is stated pointwise over realized types and
reports rather than in expectation over a prior.

## References

- [AGT, Chapter 9, Lem. 9.20] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Individual rationality for Clarke-pivot VCG mechanisms with nonnegative
  valuations.
- [AGT, Chapter 9, Section 9.5.5] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
  Individual-rationality constraints in mechanism-design applications.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:md_basic_interface` in `blueprint/src/content.tex`.
