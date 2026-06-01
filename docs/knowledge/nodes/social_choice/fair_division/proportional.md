---
id: social_choice.fair_division.proportional
title: Proportional Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.core
uses:
  - social_choice.fair_division.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Fairness
  declarations:
    - SocialChoice.FairDivision.IsProportional
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - proportional
  - fairness
---

# Proportional Allocation

Fix a population size $n$, a distinguished *whole* share `whole : S`
(typically "the entire resource"), a utility profile $u : N \to S \to
\mathbb{R}$, and an allocation $A : N \to S$
([[social_choice.fair_division.allocation]]).

The allocation $A$ is *proportional* (PROP) if every agent values their own
share at least a $1/n$ fraction of the whole:
$$
\forall i \in N,\ u_i(\mathrm{whole}) \le n \cdot u_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.IsProportional`. The "$1/n$"
intuition is stated without division (multiply through by $n$) so the
definition works over arbitrary `Semiring V`.

PROP and EF ([[social_choice.fair_division.envy_free]]) are related but
incomparable in general:

- For divisible goods (non-atomic measures), EF implies PROP
  ([[social_choice.fair_division.divisible.ef_implies_proportional]]).
- For indivisible goods (additive valuations) on complete allocations,
  EF still implies PROP
  ([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]]),
  but PROP does not imply EF in general.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Proportional allocations.
