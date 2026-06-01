---
id: social_choice.fair_division.indivisible.equitable
title: Indivisible Equitable
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.allocation
  - social_choice.fair_division.indivisible.valuation
  - social_choice.fair_division.equitable
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEquitable
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - equitable
  - fairness
---

# Indivisible Equitable

For a valuation $v$ ([[social_choice.fair_division.indivisible.valuation]])
and an allocation $A$, $A$ is *equitable* (EQ) if every agent assigns
the same numeric value to their own bundle:
$$
\forall i, j \in N,\ v_i(A(i)) = v_j(A(j)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsEquitable` — an
`abbrev` for the generic [[social_choice.fair_division.equitable]]
specialised at `v.val`.

EQ is meaningful only when valuations are *interpersonally comparable*,
typically when each $v_i$ is normalised so the whole good set has the
same total (often $1$). Without normalisation, equating
"$v_i(A(i)) = v_j(A(j))$" mixes agents' value scales.

## Relation to EF

EQ is *incomparable* with EF
([[social_choice.fair_division.indivisible.envy_free]]):

- *EF does not imply EQ.* Two agents may both be envy-free yet derive
  very different self-utilities — e.g. agent 0 gets a good worth 10 to
  them, agent 1 gets a good worth 7 to them; if neither envies the
  other, EF holds but EQ fails.
- *EQ does not imply EF.* Equal numeric utilities don't prevent an
  agent from preferring the other's bundle by their own measure — if
  agent 0 values both bundles at 5, they may still strictly prefer
  agent 1's bundle.

## Existence

For divisible goods with normalized valuations, equitable + EF
allocations always exist (Alon 1987, $n^2 - n$ cuts suffice). For
*indivisible* goods, equitable allocations may not exist at all.

## References

- [AGT Chapters 11, 13] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Equitability.
- Bouveret, Chevaleyre, and Maudet (2016). "Fair Allocation of Indivisible Goods", COMSOC Handbook Ch. 12.
