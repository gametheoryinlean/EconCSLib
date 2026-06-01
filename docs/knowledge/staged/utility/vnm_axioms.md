---
id: foundation.utility.vnm_axioms
title: Von Neumann Morgenstern Axioms
kind: definition
status: staged
uses:
  - foundation.utility.lottery
lean:
  modules:
    - EconCSLib.Foundation.Preference
    - EconCSLib.Foundation.Utility.VNMAxioms
  declarations:
    - VNM.Completeness
    - VNM.Transitivity
    - VNM.Independence
    - VNM.Continuity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - utility
  - vnm
  - lottery
---

# Von Neumann Morgenstern Axioms

For preferences over lotteries, the vNM axioms require the ordinary preference
axioms together with lottery-specific compatibility conditions.

The central lottery-specific axioms are:

- independence: mixing both sides with the same third lottery preserves
  preference;
- continuity: if $L_1$ is weakly preferred to $L_2$ and $L_2$ is weakly preferred
  to $L_3$, then $L_2$ is indifferent to a mixture of $L_1$ and $L_3$.

Together with completeness and transitivity, these axioms are the input for the
expected-utility representation theorem.

## References

- [MSZ, Chapter 2, Axioms 2.12-2.17] Maschler, Solan, and Zamir, *Game Theory*. The vNM axioms for preferences over lotteries.
