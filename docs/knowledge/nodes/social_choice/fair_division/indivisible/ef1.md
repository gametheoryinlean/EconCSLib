---
id: social_choice.fair_division.indivisible.ef1
title: EF1 — Envy-Free Up to One Good
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.envy_free
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEF1
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - ef1
  - fairness
---

# EF1 — Envy-Free Up to One Good

An allocation $A$ is *envy-free up to one good* (EF1) if, for every
envied non-empty bundle $A(j)$ from agent $i$'s perspective, **some**
single item $g \in A(j)$ exists whose removal eliminates the envy:
$$
\forall i \ne j,\ A(j) \ne \emptyset \Rightarrow
\exists g \in A(j),\ v_i(A(j) \setminus \{g\}) \le v_i(A(i)).
$$

In Lean: `SocialChoice.FairDivision.Indivisible.IsEF1`. Requires
`[DecidableEq G]` for the `Finset` difference.

The nonempty guard on $A(j)$ is necessary because an empty bundle has
no item to remove; the existential is vacuously false in that case,
which would make EF1 trivially fail. With the guard, an empty bundle
trivially satisfies the condition (no envy from agent $i$ toward an
empty bundle is possible up to value-monotonicity assumptions; the
predicate ignores empty bundles cleanly).

## Existence

Unlike plain EF ([[social_choice.fair_division.indivisible.envy_free]]),
EF1 *always exists* for arbitrary indivisible valuations:

- **Round-robin** constructs an EF1 allocation for any additive
  valuation
  ([[social_choice.fair_division.indivisible.round_robin_ef1]]).
- **Envy-cycle elimination** constructs an EF1 + Pareto-improving
  allocation for arbitrary valuations
  ([[social_choice.fair_division.indivisible.envy_cycle_ef1]]).

## Relation to other notions

- **EFX implies EF1** unconditionally
  ([[social_choice.fair_division.indivisible.efx]]):
  if removing any single item eliminates the envy, then in particular
  *some* item does.
- **EF implies EF1** under monotone valuations: any EF allocation is
  also EFX, which entails EF1.
- **EF1 does not imply PROP**: counterexample with 2 agents and 3
  equal-value goods (give 1 to A, 2 to B; A is EF1 but does not meet
  the 1/2-threshold of PROP).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF1.
- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*.
