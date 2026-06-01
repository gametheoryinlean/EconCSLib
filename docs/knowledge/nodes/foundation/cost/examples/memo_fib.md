---
id: foundation.cost.examples.memo_fib
title: "Worked Example: Memoized Fibonacci Footprint"
kind: example
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost.examples
uses:
  - foundation.cost.costm
  - foundation.cost.visited
lean:
  modules:
    - EconCSLib.Examples.CostM.MemoFib
  declarations:
    - MemoFib.fibAux
    - MemoFib.fib
    - MemoFib.fibAux_ret
    - MemoFib.fib_value
    - MemoFib.fibAux_cost
    - MemoFib.fib_cost
    - MemoFib.fib_cost_card
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - memoization
---

# Worked Example: Memoized Fibonacci Footprint

Fibonacci instrumented in `CostM (Visited ℕ)` ([[node:foundation.cost.visited]]),
so the cost field records the **set of indices** the recursion touches rather
than a call count. Because the `Visited` monoid is idempotent, the footprint
collapses to the distinct subproblems:
$$
  (\operatorname{fib} n).\mathrm{cost}.\mathrm{toFinset}
    \;=\; \{0, 1, \dots, n\} \;=\; \operatorname{range}(n+1),
$$
hence `fib_cost_card : (fib n).cost.toFinset.card = n + 1` — exactly `n+1`
distinct subproblems, the hallmark of an `O(n)` memoized DP.

Correctness and cost are proved independently: `fib_value : (fib n).ret =
Nat.fib n` lives on `.ret`, while `fib_cost` lives on `.cost`. This is the
intended `CostM` separation ([[node:foundation.cost.costm]]).

## Lean declarations

- `MemoFib.fibAux`, `MemoFib.fib` — the instrumented recursion and its wrapper.
- `MemoFib.fibAux_ret`, `MemoFib.fib_value` — correctness (`= Nat.fib`).
- `MemoFib.fibAux_cost`, `MemoFib.fib_cost`, `MemoFib.fib_cost_card` — the
  footprint equals `range (n+1)`, of cardinality `n+1`.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. Memoization as an
  idempotent cost monoid ([[node:foundation.cost.visited]]).
