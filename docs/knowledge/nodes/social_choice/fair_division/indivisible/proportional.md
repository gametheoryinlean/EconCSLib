---
id: social_choice.fair_division.indivisible.proportional
title: Indivisible Proportional
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
  - social_choice.fair_division.proportional
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsProportional
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - proportional
  - fairness
---

# Indivisible Proportional

For a valuation $v$ ([[social_choice.fair_division.indivisible.valuation]])
and an allocation $A$ over an outer good set `allGoods : Finset G`,
$A$ is *proportional* (PROP) if every agent's bundle is worth at least
a $1/n$ fraction of the total value:
$$
\forall i \in N,\ v_i(\mathrm{allGoods}) \le n \cdot v_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsProportional` — an
`abbrev` for the generic [[social_choice.fair_division.proportional]]
specialised at `v.val` and the whole-set `allGoods`.

## Existence

PROP allocations **need not exist** for indivisible goods. The same
counterexample that defeats EF
([[social_choice.fair_division.indivisible.ef_impossible_two_agents_one_good]])
also defeats PROP: with 2 agents and 1 unit-value good, the agent who
gets nothing receives value $0 < 1/2$.

For additive valuations on complete allocations, however, EF (when it
holds) implies PROP
([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]]).

## Implications

In the indivisible-additive setting:
- **EF ⇒ PROP**
  ([[social_choice.fair_division.indivisible.ef_implies_proportional_additive]]):
  envy-freeness combined with additivity forces every agent to receive
  at least $1/n$ of the total value.
- **PROP ⇒ MMS**
  ([[social_choice.fair_division.indivisible.proportional_implies_mms_additive]]):
  the proportional bound implies the maximin-share guarantee.
- **EF1 does *not* imply PROP** in general.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Indivisible proportionality.
