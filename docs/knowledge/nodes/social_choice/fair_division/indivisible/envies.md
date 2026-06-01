---
id: social_choice.fair_division.indivisible.envies
title: Envy Relation and Sources
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.envies
    - SocialChoice.FairDivision.Indivisible.envies_irrefl
    - SocialChoice.FairDivision.Indivisible.envies_ne
    - SocialChoice.FairDivision.Indivisible.isSource
    - SocialChoice.FairDivision.Indivisible.IsEnvyFree.isSource_all
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - algorithms
---

# Envy Relation and Sources

For an indivisible valuation $v$
([[social_choice.fair_division.indivisible.valuation]]) and allocation
$A$, the *envy relation* points from the envier to the envied:
$$
i \to_{\text{envy}} j \iff v_i(A(j)) > v_i(A(i)).
$$

In Lean: `envies v A i j`.

## Basic structural lemmas

- **Irreflexivity.** `envies_irrefl`: no agent envies themselves
  ($v_i(A(i)) > v_i(A(i))$ is false).
- **Distinct.** `envies_ne`: $i \to_{\text{envy}} j \Rightarrow i \ne j$
  (immediate from irreflexivity).

## Sources

An agent $i$ is an *envy-graph source* if no other agent envies them:
$$
\mathrm{isSource}(v, A, i) \iff \forall j,\ \neg (j \to_{\text{envy}} i).
$$

In Lean: `isSource v A i`.

The relation between sources and envy-freeness:
- `IsEnvyFree.isSource_all`: if $A$ is envy-free
  ([[social_choice.fair_division.indivisible.envy_free]]) then *every*
  agent is a source.

Sources play a central role in the envy-cycle elimination algorithm
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]]):
fresh items are always given to a source agent, ensuring that the
recipient does not generate new envy against themselves.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Envy graph and elimination.
