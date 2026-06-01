---
id: social_choice.fair_division.indivisible.acyclic_has_source
title: Acyclic Envy Graph Has a Source
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.envy_cycle
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.acyclic_has_source
    - SocialChoice.FairDivision.Indivisible.findSource
    - SocialChoice.FairDivision.Indivisible.findSource_isSource
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - source
  - acyclic
---

# Acyclic Envy Graph Has a Source

**Theorem.** Let $v$ be a valuation and $A$ an allocation on a finite
nonempty agent type. If the envy graph has no envy cycles
([[social_choice.fair_division.indivisible.envy_cycle]]), then some
agent is a source ([[social_choice.fair_division.indivisible.envies]]).

In Lean: `acyclic_has_source`, with hypotheses `[Fintype N] [Nonempty N]`.

## Proof sketch

Standard finite-DAG argument: an irreflexive relation on a finite
nonempty set with no cycles must have a minimal element. The Lean proof
shows the contrapositive — if no agent is a source, follow envy edges
backwards from any starting agent; by finiteness and the pigeonhole
principle, eventually the path revisits an agent, producing a cycle.

## Computable witness

`findSource` (noncomputable) — a deterministic procedure that returns
an agent guaranteed to be a source whenever one exists. The companion
correctness lemma `findSource_isSource` shows that the returned agent
satisfies `isSource`.

## Use in the algorithm

After `eliminateAllCycles`
([[social_choice.fair_division.indivisible.eliminate_all_cycles]])
removes all envy cycles, this theorem guarantees that some agent is a
source. That agent receives the next item to assign, ensuring no fresh
envy is created against them. This is the key invariant used in
proving EF1 of the envy-cycle algorithm
([[social_choice.fair_division.indivisible.envy_cycle_ef1]]).

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*. Source existence in acyclic envy graphs.
