---
id: foundation.cost.examples.reverse_space
title: "Worked Example: Quadratic Naive List Reversal"
kind: example
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost.examples
uses:
  - foundation.cost.costm
lean:
  modules:
    - EconCSLib.Examples.CostM.ReverseSpace
  declarations:
    - ReverseSpace.naiveReverse
    - ReverseSpace.naiveReverse_cost_le
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - time-complexity
---

# Worked Example: Quadratic Naive List Reversal

The append-at-the-end naive list reversal, instrumented in `CostM ℕ` to
exhibit a **quadratic** cost. Each of the `length` recursive steps performs an
append whose cost is proportional to the accumulated length, giving
$$
  (\operatorname{naiveReverse}\,l).\mathrm{cost} \;\le\; |l|^2,
$$
proved as `naiveReverse_cost_le`. This is the counterpoint to the linear and
logarithmic `CostM ℕ` examples ([[node:foundation.cost.examples.gcd]]): a
worse algorithm shows up directly as a worse bound on `.cost`, with no change
to the monad or to the correctness of the reversed result on `.ret`.

## Lean declarations

- `ReverseSpace.naiveReverse : List α → CostM ℕ (List α)`.
- `ReverseSpace.naiveReverse_cost_le` — the `|l|²` cost bound.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. Cost-annotated
  functional algorithms ([[node:foundation.cost.costm]]).
