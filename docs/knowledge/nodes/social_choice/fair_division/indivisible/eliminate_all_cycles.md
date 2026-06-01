---
id: social_choice.fair_division.indivisible.eliminate_all_cycles
title: Eliminate All Envy Cycles
kind: definition
status: formalized
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
  - social_choice.fair_division.indivisible.algorithms
uses:
  - social_choice.fair_division.indivisible.pareto_dom_count
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.EnvyCycle
  declarations:
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles_unfold
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles_acyclic
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles_isAllocation
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles_nondecreasing
    - SocialChoice.FairDivision.Indivisible.eliminateAllCycles_eq_of_acyclic
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - envy-cycle
  - algorithms
---

# Eliminate All Envy Cycles

The recursive procedure that, given an allocation with an envy cycle,
rotates the cycle and recurses; terminates when the envy graph is
acyclic.

In Lean: `eliminateAllCycles v allGoods A : Allocation N G`, defined by
well-founded recursion on the Pareto-domination count
([[social_choice.fair_division.indivisible.pareto_dom_count]]).

## Structural lemmas

- `eliminateAllCycles_unfold`: the standard fixed-point unfolding. If
  $A$ has no envy cycle, return $A$; otherwise pick a cycle, rotate,
  and recurse.

- `eliminateAllCycles_acyclic`: the output never has an envy cycle —
  the recursion stops only when acyclic.

- `eliminateAllCycles_isAllocation` (with `[DecidableEq G]`):
  termination preserves the partition property
  ([[social_choice.fair_division.indivisible.allocation]]). The
  intermediate rotation step preserves allocations
  ([[social_choice.fair_division.indivisible.rotate_bundles]]'s
  `rotateBundles_isAllocation`), and `eliminateAllCycles_isAllocation`
  lifts that through the recursion.

- `eliminateAllCycles_nondecreasing`: every agent's utility weakly
  improves across the whole recursion. Each cycle-rotation step is
  nondecreasing, so the composition is too.

- `eliminateAllCycles_eq_of_acyclic`: if the input is already acyclic,
  the output equals the input (fixed-point base case).

## Significance

This is the *engine* of envy-cycle elimination — a procedure that, given
an arbitrary allocation, produces an acyclic-envy-graph allocation that
weakly Pareto-dominates the input. The full algorithm
([[social_choice.fair_division.indivisible.envy_cycle_algorithm]])
sandwiches `eliminateAllCycles` between item-assignment steps to
produce EF1 + (weak) Pareto-improving allocations.

## References

- Lipton, Markakis, Mossel, and Saberi (2004). "On Approximately Fair Allocations of Indivisible Goods". *EC*.
- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. Envy-cycle elimination subroutine.
