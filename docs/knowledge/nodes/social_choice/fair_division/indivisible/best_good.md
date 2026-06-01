---
id: social_choice.fair_division.indivisible.best_good
title: Best-Good Selection
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin
  declarations:
    - SocialChoice.FairDivision.Indivisible.bestGood
    - SocialChoice.FairDivision.Indivisible.bestGood_mem
    - SocialChoice.FairDivision.Indivisible.bestGood_le
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - round-robin
  - algorithms
---

# Best-Good Selection

The *best-good* operation picks an agent's favourite available item from
a remaining finite set $R \subseteq G$ under an additive valuation
$w : N \to G \to \mathbb{R}$
([[social_choice.fair_division.indivisible.additive_valuation]]).

Informally:
$$
\mathrm{bestGood}(i, R) = \arg\max_{g \in R} w(i, g),
$$
with deterministic tie-breaking using the underlying decidable
equality on $G$.

In Lean: `SocialChoice.FairDivision.Indivisible.bestGood`. Marked
`noncomputable` because the `arg max` selection over a `Finset` uses
classical decidability.

## Basic properties

Two small lemmas pin down the operation:

- `bestGood_mem` : when $R$ is nonempty, $\mathrm{bestGood}(i, R) \in R$.
- `bestGood_le` : $\mathrm{bestGood}(i, R)$ achieves the maximum value:
  $\forall g \in R,\ w(i, g) \le w(i, \mathrm{bestGood}(i, R))$.

These are exactly what the round-robin partition / correctness proofs
need to reason about: an agent always takes a *valid* item (not yet
allocated) and always takes their *best-remaining* item.

## Use in round-robin

The round-robin allocation
([[social_choice.fair_division.indivisible.round_robin_alloc]]) calls
`bestGood` at each step to give the current agent their favourite
remaining item. The two properties above are the only facts about
`bestGood` that the EF1 correctness proof
([[social_choice.fair_division.indivisible.round_robin_ef1]]) uses —
the rest is bookkeeping about turn order.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Round-robin item selection.
