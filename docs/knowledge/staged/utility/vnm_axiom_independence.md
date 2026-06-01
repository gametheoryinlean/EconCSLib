---
id: foundation.utility.vnm_axiom_independence
title: Independence Of The VNM Axioms
kind: theorem
status: staged
uses:
  - foundation.utility.vnm_axioms
lean:
  modules:
    - EconCSLib.Foundation.Utility.VNMAxioms
  declarations:
    - VNM.axioms_independent
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - utility
  - vnm
  - exercise
---

# Independence Of The VNM Axioms

The vNM axioms are logically independent: for each axiom, there is a preference
relation over lotteries that violates that axiom while satisfying the others.

## Proof Sketch

Construct separate finite lottery preference relations. For completeness, use a
preference that compares only identical lotteries. For transitivity, create a
cycle. For continuity, use a lexicographic-style preference. For independence,
use a preference rule whose ranking changes under common mixing. Each example
keeps the remaining axioms valid.

## References

- [MSZ, Chapter 2, Exercise 2.5] Maschler, Solan, and Zamir, *Game Theory*. The vNM axioms are independent.
