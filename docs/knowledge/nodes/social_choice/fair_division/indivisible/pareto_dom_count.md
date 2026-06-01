---
id: social_choice.fair_division.indivisible.pareto_dom_count
title: Pareto-Domination Count Termination Measure
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.rotate_bundles
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.paretoDomCount
    - SocialChoice.FairDivision.Indivisible.paretoDomSet_subset
    - SocialChoice.FairDivision.Indivisible.self_mem_paretoDomSet
    - SocialChoice.FairDivision.Indivisible.not_mem_paretoDomSet_of_strict
    - SocialChoice.FairDivision.Indivisible.rotateBundles_paretoDomCount_lt
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - termination
  - well-founded
---

# Pareto-Domination Count Termination Measure

The envy-cycle elimination algorithm
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
repeatedly rotates bundles along cycles. To prove termination we need a
strictly decreasing well-founded measure.

The chosen measure is the *Pareto-domination count*: the number of
allocations (over the finite set of possible $\mathrm{Allocation}\ N\ G$
functions for $N, G$ finite) that *Pareto-dominate or equal* the
current allocation in agent-utility vectors.

In Lean: `paretoDomCount v allGoods A : ℕ`, with hypotheses
`[Fintype N] [Fintype G]`.

## Structural lemmas

- `paretoDomSet_subset`: the domination set is a subset of the
  (finite) set of complete allocations of `allGoods`.
- `self_mem_paretoDomSet`: $A$ Pareto-dominates itself
  (weak domination is reflexive), so $A$ is in its own set and the
  count is $\ge 1$.
- `not_mem_paretoDomSet_of_strict`: if $A'$ *strictly* improves over
  $A$ (some agent gets strictly more), then $A$ no longer belongs to
  $A'$'s Pareto-domination set — i.e. $A$ is dropped from the count
  when we move to $A'$.

## Strict decrease under rotation

`rotateBundles_paretoDomCount_lt` (with `[DecidableEq N]`): if $l$ is an
envy cycle, the rotation strictly decreases the Pareto-domination
count:
$$
\mathrm{paretoDomCount}(\mathrm{rotate}(A, l)) < \mathrm{paretoDomCount}(A).
$$

The argument:

1. Cycle rotation strictly improves at least one agent
   ([[social_choice.fair_division.indivisible.rotate_bundles]]'s
   `rotateBundles_improves`) and weakly improves the rest.
2. Therefore $\mathrm{rotate}(A, l)$ Pareto-dominates $A$ strictly.
3. By `not_mem_paretoDomSet_of_strict`, $A$ leaves the Pareto-domination
   set of $\mathrm{rotate}(A, l)$, dropping the count by at least one.
4. The new set is a subset of the old (any allocation dominating
   $\mathrm{rotate}(A, l)$ also dominates $A$).

Hence the count strictly decreases, which gives termination.

## Why this measure works

The total number of allocations is finite (`[Fintype N]` and
`[Fintype G]` together with `Finset.card allGoods`), so any
strictly-decreasing $\mathbb{N}$-valued measure is well-founded. This
lets `eliminateAllCycles`
([[social_choice.fair_division.indivisible.eliminate_all_cycles]]) be
defined by well-founded recursion in Lean.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*. Termination of envy-cycle elimination.
