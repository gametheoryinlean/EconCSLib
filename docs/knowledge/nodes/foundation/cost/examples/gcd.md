---
id: foundation.cost.examples.gcd
title: "Worked Example: Euclidean GCD Step Count"
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
    - EconCSLib.Examples.CostM.GCD
  declarations:
    - GCD.gcd
    - GCD.gcd_cost_le
    - GCD.gcd_cost_log_le
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - time-complexity
---

# Worked Example: Euclidean GCD Step Count

The simplest `CostM` instance: `gcd` in `CostM ℕ`, charging one unit per
modulus operation. Two bounds are proved:

- `gcd_cost_le`  —  `(gcd a b).cost ≤ b` (a trivial linear bound), and
- `gcd_cost_log_le`  —  `(gcd a b).cost ≤ 2 · \log_2 b + 1`, the textbook
  logarithmic bound following from the fact that two consecutive remainders
  at least halve the modulus.

This is the canonical "`C = ℕ`, additive, counts one resource" use of the
monad ([[node:foundation.cost.costm]]): the cost field accumulates the number
of `mod` steps, and the bound lives purely on `.cost` while the returned gcd
value lives on `.ret`.

## Lean declarations

- `GCD.gcd : ℕ → ℕ → CostM ℕ ℕ` — the instrumented algorithm.
- `GCD.gcd_cost_le`, `GCD.gcd_cost_log_le` — the linear and logarithmic step
  bounds (the latter via a private `mod_halves` halving lemma).

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. Cost-annotated
  functional algorithms ([[node:foundation.cost.costm]]).
