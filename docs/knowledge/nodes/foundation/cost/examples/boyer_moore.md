---
id: foundation.cost.examples.boyer_moore
title: "Worked Example: Constant-Space Boyer–Moore Majority"
kind: example
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost.examples
uses:
  - foundation.cost.costm
  - foundation.cost.cells
lean:
  modules:
    - EconCSLib.Examples.CostM.BoyerMoore
  declarations:
    - BoyerMoore.majority
    - BoyerMoore.loop_cost
    - BoyerMoore.majority_peak_le
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - peak-memory
---

# Worked Example: Constant-Space Boyer–Moore Majority

The Boyer–Moore majority vote in `CostM Cells` ([[node:foundation.cost.cells]]),
proving a **constant** peak-memory bound: regardless of input length, the peak
working set is two cells — one candidate and one counter,
$$
  (\operatorname{majority}\,xs).\mathrm{cost}.\mathrm{peak} \;\le\; 2,
$$
which is `majority_peak_le`. The mechanism is that the single-pass `loop`
allocates nothing — `loop_cost : (majority.loop \ldots).cost = 0` — so the only
contributions to the peak come from one `alloc 2` / `free 2` pair bracketing
the pass. Because peak (not sum) is the resource, the tropical `Cells` monoid
is essential here; an additive `ℕ` cost cannot state this bound.

This example deliberately **does not** prove functional correctness (that
`majority` returns the true majority when one exists). That omission is the
point: in `CostM` the complexity bound lives on `.cost` and is provable in
complete isolation from the `.ret` value, demonstrating the
correctness/complexity decoupling described in [[node:foundation.cost.costm]].

## Lean declarations

- `BoyerMoore.majority : List α → CostM Cells (Option α)` with its single-pass
  `where loop` carrying the candidate and counter.
- `BoyerMoore.loop_cost` — the loop contributes zero cost.
- `BoyerMoore.majority_peak_le` — the constant `peak ≤ 2` bound.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. Cost monoids for
  resource analysis ([[node:foundation.cost.cells]]).
