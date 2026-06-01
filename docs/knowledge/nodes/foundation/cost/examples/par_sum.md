---
id: foundation.cost.examples.par_sum
title: "Worked Example: Balanced Parallel Sum Depth"
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
    - EconCSLib.Examples.CostM.ParSum
  declarations:
    - ParSum.parSum
    - ParSum.parSum_cost_le_clog
    - ParSum.parSum_cost_le_length
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - parallel
---

# Worked Example: Balanced Parallel Sum Depth

A divide-and-conquer list sum built from `par` ([[node:foundation.cost.parallel]]),
where cost is combined by `⊔` so that `.cost` measures parallel **depth**, not
total work. Splitting the list in half and summing the halves in parallel
gives a logarithmic depth,
$$
  (\operatorname{parSum}\,xs).\mathrm{cost} \;\le\; \lceil \log_2 |xs| \rceil,
$$
i.e. `parSum_cost_le_clog` (`Nat.clog 2 xs.length`). The coarser linear bound
`parSum_cost_le_length` is also provided. This is the depth-side counterpart of
the additive-work examples: the same algorithm under `+` would cost `O(n)`, but
under `⊔` the independent branches overlap and only the tree height counts.

## Lean declarations

- `ParSum.parSum : List ℕ → CostM ℕ ℕ` — the balanced parallel sum.
- `ParSum.parSum_cost_le_clog` — the `⌈log₂ n⌉` depth bound.
- `ParSum.parSum_cost_le_length` — the coarser linear bound.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. The underlying cost
  monad ([[node:foundation.cost.costm]]).
