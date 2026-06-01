---
id: social_choice.fair_division.indivisible.round_robin_partition
title: Round-Robin Output Is a Complete Partition
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.round_robin_alloc
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin
  declarations:
    - SocialChoice.FairDivision.Indivisible.roundRobinAllocation_isAllocation
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - round-robin
  - partition
---

# Round-Robin Output Is a Complete Partition

**Theorem.** For any additive valuation $w$ and any finite good set
`allGoods : Finset G`, the round-robin allocation
([[social_choice.fair_division.indivisible.round_robin_alloc]]) satisfies
`IsAllocation allGoods (roundRobinAllocation ...)`
([[social_choice.fair_division.indivisible.allocation]]).

In Lean: `SocialChoice.FairDivision.Indivisible.roundRobinAllocation_isAllocation`.

## Proof outline

Two invariants tracked through the recursion:

- **Disjointness.** Each step assigns one good to one agent and removes
  it from the `remaining` set. The invariant "the bundles `bundles[i]`
  and `bundles[j]` are disjoint, and both are disjoint from
  `remaining`" is preserved at each step.

- **Cover.** The invariant "`(⋃_i bundles[i]) ∪ remaining = allGoods`"
  is preserved at each step (the freshly-allocated good moves from
  `remaining` into `bundles[i]`).

When `remaining = ∅` at termination, the cover invariant collapses to
$\bigcup_i \mathrm{bundles}[i] = \mathrm{allGoods}$, which together with
disjointness gives a partition.

## Significance

This is the *feasibility* theorem for round-robin. The next-step EF1
correctness proof
([[social_choice.fair_division.indivisible.round_robin_ef1]]) needs
this feasibility as a prerequisite — the EF1 statement compares values
of agents' bundles in a complete allocation.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Round-robin partition correctness.
