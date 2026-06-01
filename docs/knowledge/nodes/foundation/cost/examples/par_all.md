---
id: foundation.cost.examples.par_all
title: "Worked Example: N-ary parList Depth Bound"
kind: example
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost.examples
uses:
  - foundation.cost.costm
  - foundation.cost.parallel
lean:
  modules:
    - EconCSLib.Examples.CostM.ParAll
  declarations:
    - ParAll.parMap_unit_cost_le
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - parallel
---

# Worked Example: N-ary parList Depth Bound

The n-ary `parList` combinator ([[node:foundation.cost.parallel]]) applied to a
list of independent unit-cost operations. Because the costs are folded with
`⊔` from `⊥`, running `n` operations that each charge one unit in parallel has
depth-1 cost:
$$
  (\operatorname{parList}\,ms).\mathrm{cost}
    \;=\; \bigsqcup_i (m_i).\mathrm{cost} \;\le\; 1,
$$
proved as `parMap_unit_cost_le`. This is the flat fan-out / fan-in schedule:
arbitrarily many independent unit tasks cost the same as one, the defining
property distinguishing the parallel `⊔` cost from the sequential `+` cost
([[node:foundation.cost.costm]]). The empty-list base case (`parList [] `has
cost `⊥ = 0`) is exercised by the accompanying examples in the source file.

## Lean declarations

- `ParAll.parMap_unit_cost_le` — the `parList`-of-unit-tasks depth bound `≤ 1`,
  alongside two `example`s pinning the empty and singleton cases.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. The underlying cost
  monad ([[node:foundation.cost.costm]]).
