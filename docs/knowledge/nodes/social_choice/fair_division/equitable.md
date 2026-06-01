---
id: social_choice.fair_division.equitable
title: Equitable Allocation
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
    - SocialChoice.FairDivision.IsEquitable
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - equitable
  - fairness
---

# Equitable Allocation

An allocation $A : N \to S$ ([[social_choice.fair_division.allocation]])
is *equitable* (EQ) under a utility profile $u$ if every agent assigns the
same numeric value to their own share:
$$
\forall i, j \in N,\ u_i(A(i)) = u_j(A(j)).
$$

In Lean: `SocialChoice.FairDivision.IsEquitable`.

Equitability is meaningful only when utilities are interpersonally
comparable — typically when each agent's $u_i$ is *normalized* so the
whole resource is valued at the same total (often $1$). Without
normalization, equating "$u_i(A_i) = u_j(A_j)$" mixes apples and oranges.

EQ is incomparable with EF ([[social_choice.fair_division.envy_free]]):

- *EF does not imply EQ.* Two agents with disjoint goods can both be
  envy-free yet derive very different self-utilities.
- *EQ does not imply EF.* Two agents may both value their own share at
  the same number while one of them strictly prefers the other's share
  by their own measure.

For divisible goods with normalized valuations, equitable + EF allocations
always exist (Alon 1987, $n^2 - n$ cuts suffice). For indivisible goods,
equitable allocations may fail to exist outright.

## References

- [AGT Chapters 11, 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Equitability.
- Bouveret, Chevaleyre, and Maudet (2016). "Fair Allocation of Indivisible Goods", COMSOC Handbook Ch. 12.
