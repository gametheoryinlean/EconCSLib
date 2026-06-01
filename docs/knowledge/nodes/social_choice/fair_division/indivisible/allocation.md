---
id: social_choice.fair_division.indivisible.allocation
title: Indivisible Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses: []
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Basic
  declarations:
    - SocialChoice.FairDivision.Indivisible.Allocation
    - SocialChoice.FairDivision.Indivisible.IsAllocation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - allocation
---

# Indivisible Allocation

For a population $N$ and a finite type of goods $G$ (with
`[DecidableEq G]`), an *indivisible allocation* assigns each agent a
bundle (a finite subset of $G$):
$$
A : N \to \mathrm{Finset}\ G.
$$

In Lean: `SocialChoice.FairDivision.Indivisible.Allocation N G := N → Finset G`,
a plain type alias.

## Partition predicate

A *complete* indivisible allocation partitions an outer good set
`allGoods : Finset G`. In Lean: `IsAllocation` is a structure with two
fields:

- `disjoint : ∀ i ≠ j, Disjoint (A i) (A j)` — agents receive disjoint
  bundles;
- `complete : allGoods = Finset.univ.biUnion A` — every good in
  `allGoods` is allocated to some agent.

The class hypotheses `[Fintype N]` and `[DecidableEq G]` are required
by the `Finset.univ.biUnion` and `Disjoint` operators.

A small derived fact `IsAllocation.mem_biUnion` says every good in
`allGoods` belongs to some agent's bundle.

## Why feasibility is a separate predicate

Algorithms like round-robin
([[social_choice.fair_division.indivisible.round_robin_alloc]]) and
envy-cycle elimination
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
manipulate raw allocations (function values, not partition witnesses) in
intermediate states. Keeping `Allocation` as a plain function type and
`IsAllocation` as a separate hypothesis lets these algorithms be
written without prematurely committing to partition invariants at
every step.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Indivisible goods allocations.
