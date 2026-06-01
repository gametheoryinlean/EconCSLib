---
id: social_choice.fair_division.indivisible.envy_cycle_algorithm
title: Envy-Cycle Elimination Algorithm
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.eliminate_all_cycles
  - social_choice.fair_division.indivisible.acyclic_has_source
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.envyCycleAllocation
    - SocialChoice.FairDivision.Indivisible.envyCycleRule
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - algorithms
---

# Envy-Cycle Elimination Algorithm

The full envy-cycle elimination algorithm (Lipton et al. 2004):

```
state := (remaining = allGoods, A = empty bundles)
while remaining is nonempty:
  A := eliminateAllCycles(v, allGoods, A)   -- clear all envy cycles
  i := findSource(v, A)                     -- pick a source agent
  g := pickItem(remaining)                  -- pick any remaining item
  A[i] := A[i] ∪ {g}
  remaining := remaining \ {g}
return A
```

In Lean: `SocialChoice.FairDivision.Indivisible.envyCycleAllocation`
(top-level worker) and
`SocialChoice.FairDivision.Indivisible.envyCycleRule` (bundled rule
form).

## Why each step is needed

- **Eliminate cycles first.** Each call to `eliminateAllCycles`
  ([[social_choice.fair_division.indivisible.eliminate_all_cycles]])
  ensures the envy graph is acyclic, which (by
  [[social_choice.fair_division.indivisible.acyclic_has_source]])
  guarantees that some agent is a source.

- **Assign to a source.** Giving the fresh item to a source means no
  one envies the recipient *before* the item is added. The
  new envy created by the item is bounded by the value of *that one
  item*, so the resulting allocation remains EF1.

- **Loop.** The outer loop runs `|allGoods|` times. Each iteration may
  do many `rotateBundles` calls inside `eliminateAllCycles`, but each
  rotation strictly decreases the Pareto-domination count
  ([[social_choice.fair_division.indivisible.pareto_dom_count]]),
  giving overall termination.

## Termination

The outer loop has a fixed number of iterations (the number of items).
The inner `eliminateAllCycles` terminates by the well-founded
Pareto-domination measure. Overall termination is polynomial in
$|N|, |G|$ on standard random-access models.

## Correctness

Two top-level correctness theorems:

- `envyCycleAllocation_isAllocation`
  ([[social_choice.fair_division.indivisible.envy_cycle_ef1]]'s
  companion): the output is a valid complete partition.
- `envyCycleAllocation_isEF1` / `envyCycleRule_isEF1`: the output
  is EF1.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*. The original envy-cycle algorithm.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF1 from envy-cycle elimination.
