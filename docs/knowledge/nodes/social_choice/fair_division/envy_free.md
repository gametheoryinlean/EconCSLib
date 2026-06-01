---
id: social_choice.fair_division.envy_free
title: Envy-Free Allocation
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
    - SocialChoice.FairDivision.IsEnvyFree
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - envy-free
  - fairness
---

# Envy-Free Allocation

For a real-valued utility profile $u : N \to S \to \mathbb{R}$ and an
allocation $A : N \to S$ ([[social_choice.fair_division.allocation]]),
$A$ is *envy-free* (EF) if every agent weakly prefers their own share to
every other agent's share:
$$
\forall i, j \in N,\ u_i(A(j)) \le u_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.IsEnvyFree`. The signature takes
$u$ and $A$ as plain functions, so the predicate applies uniformly to the
divisible and indivisible specializations
([[social_choice.fair_division.divisible.envy_free]],
[[social_choice.fair_division.indivisible.envy_free]]).

## Existence

- *Divisible* (cake cutting with non-atomic finite measures): EF
  allocations always exist (Stromquist,
  [[social_choice.fair_division.divisible.ef_exists]]).
- *Indivisible* (additive valuations over a finite set of items): EF
  *need not* exist, even with 2 agents and 1 item
  ([[social_choice.fair_division.indivisible.ef_impossible_two_agents_one_good]]).
  This motivates the relaxations EF1 / EFX
  ([[social_choice.fair_division.indivisible.ef1]],
  [[social_choice.fair_division.indivisible.efx]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Envy-freeness in fair division.
