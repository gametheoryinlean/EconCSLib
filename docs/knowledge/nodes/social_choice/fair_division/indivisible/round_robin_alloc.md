---
id: social_choice.fair_division.indivisible.round_robin_alloc
title: Round-Robin Allocation
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.best_good
  - social_choice.fair_division.indivisible.allocation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.RoundRobin
  declarations:
    - SocialChoice.FairDivision.Indivisible.roundRobinAux
    - SocialChoice.FairDivision.Indivisible.roundRobinAllocation
    - SocialChoice.FairDivision.Indivisible.roundRobinRule
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - round-robin
  - algorithms
---

# Round-Robin Allocation

The *round-robin algorithm* under an additive valuation
([[social_choice.fair_division.indivisible.additive_valuation]]) cycles
through agents in a fixed turn order. Each agent, on their turn, picks
their favourite remaining good
([[social_choice.fair_division.indivisible.best_good]]) and adds it to
their bundle. The procedure terminates when the good set is exhausted.

In Lean: `SocialChoice.FairDivision.Indivisible.roundRobinAllocation`
(plus the recursive worker `roundRobinAux` and the bundled rule form
`roundRobinRule`). All are `noncomputable` because they call `bestGood`
on an `arg max`.

## Algorithm shape

```
state := (remaining = allGoods, bundles = empty for each agent)
for k in 0, 1, 2, ...:
  if remaining is empty: stop
  let i := agentTurn(k)        -- cyclically: 0, 1, ..., n-1, 0, 1, ...
  let g := bestGood(i, remaining)
  bundles[i] := bundles[i] ∪ {g}
  remaining := remaining \ {g}
return bundles
```

The Lean implementation closely follows this shape, using
`Fin (Finset.card allGoods)` to index rounds and `Fin.foldr` /
`List.foldr` to thread the state.

## Three layers

- `roundRobinAux` — the recursive worker on the state tuple.
- `roundRobinAllocation` — top-level call: takes the full agent type,
  the additive valuation, and `allGoods`, and returns an
  `Allocation N G`.
- `roundRobinRule` — bundled-additive-instance form returning a
  feasibility-paired allocation
  ([[social_choice.fair_division.solution_concept]]).

## Correctness theorems

Two key correctness theorems for `roundRobinAllocation`:

- `roundRobinAllocation_isAllocation`: the output is a complete
  measurable partition of `allGoods`
  ([[social_choice.fair_division.indivisible.round_robin_partition]]).
- `roundRobinAllocation_isEF1`: the output is EF1
  ([[social_choice.fair_division.indivisible.round_robin_ef1]]).

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Round-robin algorithm.
- Caragiannis, Kurokawa, Moulin, Procaccia, Shah, and Wang (2019). "The Unreasonable Fairness of Maximum Nash Welfare". *EC*.
