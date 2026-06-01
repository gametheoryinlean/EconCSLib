---
id: social_choice.fair_division.indivisible.envy_free
title: Indivisible Envy-Free
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
  - social_choice.fair_division.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEnvyFree
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-free
  - fairness
---

# Indivisible Envy-Free

For an indivisible valuation $v$
([[social_choice.fair_division.indivisible.valuation]]) and an
allocation $A$ ([[social_choice.fair_division.indivisible.allocation]]),
$A$ is *envy-free* (EF) if every agent weakly prefers their own bundle:
$$
\forall i, j \in N,\ v_i(A(j)) \le v_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsEnvyFree` — an
`abbrev` for the generic [[social_choice.fair_division.envy_free]]
specialised at `v.val`.

## Non-existence

In the indivisible setting EF allocations *need not exist*: the simplest
counterexample is two agents and one good (the
"give it to one agent" allocation makes the other agent envy the
recipient). This is captured precisely in
[[social_choice.fair_division.indivisible.ef_impossible_two_agents_one_good]].

The standard relaxations EF1 and EFX
([[social_choice.fair_division.indivisible.ef1]],
[[social_choice.fair_division.indivisible.efx]]) recover existence by
weakening the strict comparison: envy is allowed if it vanishes after
removing some / any single item from the envied bundle.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Indivisible envy-freeness.
