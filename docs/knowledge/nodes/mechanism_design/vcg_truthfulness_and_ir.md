---
id: mechanism_design.vcg.truthfulness_and_ir
title: VCG Truthfulness And Individual Rationality
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.vcg
uses:
- mechanism_design.vcg.welfare_and_payments
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.VCG
  declarations:
  - VCGMechanism_truthful_quasiLinearUtility_nonneg
  - VCGMechanism_truthful_profile_quasiLinearUtility_nonneg
  - VCGMechanism_isExPostIR_of_all_nonnegative
  - VCGMechanism_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- vcg
- dsic
- individual-rationality
---

# VCG Truthfulness And Individual Rationality

The VCG mechanism is dominant-strategy incentive compatible (DSIC)
unconditionally for quasi-linear utilities, and — under the additional
nonnegativity hypothesis on every valuation in the type space — gives every
agent nonnegative truthful quasi-linear utility, which yields ex-post
individual rationality.

That is: DSIC needs no sign assumption; IR and the nonnegative-utility bound
require nonnegative valuations.

## References

- [AGT, Chapter 9, Thm. 9.17] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. VCG
  mechanisms are incentive compatible.
- [AGT, Chapter 9, Lem. 9.20] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. Clarke
  pivot payments and individual rationality under nonnegative valuations.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:md_vcg_results` in `blueprint/src/content.tex`.
