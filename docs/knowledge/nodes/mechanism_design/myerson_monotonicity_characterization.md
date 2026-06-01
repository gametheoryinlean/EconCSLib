---
id: mechanism_design.myerson.monotonicity_characterization
title: Myerson Monotonicity Characterization
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
- mechanism_design
- mechanism_design.myerson
uses:
- mechanism_design.myerson.payment_formula
- mechanism_design.myerson.payment_envelope
- mechanism_design.myerson.payment_construction
lean:
  modules:
  - EconCSLib.MechanismDesign.Auction.Myerson
  declarations:
  - isMonotone_of_isDSIC
  - withMyersonPayment_isDSIC_of_isMonotone
  - isImplementable_of_isMonotone
  - isImplementable_iff_isMonotone
  - payment_formula_of_isDSIC_of_zeroNormalized
  - payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized
  - existsUnique_zeroNormalized_payment_of_isMonotone
  - payment_formula_of_zeroNormalized_and_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
- mechanism-design
- myerson
- dsic
- monotonicity
---

# Myerson Monotonicity Characterization

For single-parameter mechanisms over real values, DSIC implies monotonicity.
Conversely, a monotone allocation rule paired with the canonical Myerson
payment rule is DSIC.

The zero-normalized DSIC payment rule is characterized by the Myerson payment
formula, yielding existence and uniqueness of the zero-normalized payment rule
for monotone allocation rules.

## References

- [AGT, Chapter 9, Section 9.5.4, Thm. 9.36] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Monotonicity and critical payments
  characterize single-parameter incentive-compatible mechanisms.
- [Myerson 1981, Sections 2-3] Myerson, R. B. "Optimal auction design."
  *Mathematics of Operations Research* 6(1):58-73. Monotonicity and payment
  formulae in optimal auction design.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:md_myerson_results` in `blueprint/src/content.tex`.
