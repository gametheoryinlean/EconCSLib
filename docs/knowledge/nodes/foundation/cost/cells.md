---
id: foundation.cost.cells
title: Peak-Memory Cost via the Cells Monoid
kind: definition
status: formalized
primary_topic: foundation
topics:
  - foundation
  - foundation.cost
uses:
  - foundation.cost.costm
lean:
  modules:
    - EconCSLib.Foundation.CostM.Cells
  declarations:
    - Cells
    - Cells.alloc
    - Cells.free
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - cost
  - memory
  - tropical
---

# Peak-Memory Cost via the Cells Monoid

Additive cost ([[node:foundation.cost.costm]]) cannot express **peak** memory,
because the high-water mark of a sequence of allocations and frees is not the
sum of the per-step changes. `Cells` is the cost monoid that fixes this: an
element carries a non-negative `peak` and a signed net `delta` with the
invariant `delta ≤ peak` (and `0 ≤ peak`).

Composition is the **tropical / (max,+)** law that tracks the worst high-water
mark across a sequence — the peak of the second block is reached *after* the
first block's net allocation:
$$
  (p_1, d_1) \star (p_2, d_2)
    \;=\; \bigl(\max(p_1,\; d_1 + p_2),\; d_1 + d_2\bigr),
  \qquad 0 = (0,0).
$$
This is an additive monoid (the EconCSLib `CostM` framework requires `C` to be
an additive monoid), but a *non-cancellative* one — the `⋆` above is its `+`.

The two generators model allocation and release of `n` cells:
$$
  \operatorname{alloc} n = (n, n),
  \qquad
  \operatorname{free} n = (0, -n).
$$
An `alloc n` raises both the current footprint and the peak by `n`; a
`free n` lowers the net footprint by `n` while leaving the peak untouched
(the cells were live at some point).

## Lean declarations

- `Cells` — the structure (`peak`, `delta`, `zero_le_peak`, `delta_le_peak`);
  its `Zero`/`Add`/`AddMonoid` instances are anonymous.
- `Cells.alloc`, `Cells.free` — the generators.
- Projection lemmas `peak_zero`/`delta_zero`, `peak_add`/`delta_add`,
  `peak_alloc`/`delta_alloc`, `peak_free`/`delta_free` drive the `simp`
  normal form for peak computations.

The canonical use is the constant-space Boyer–Moore majority vote,
[[node:foundation.cost.examples.boyer_moore]], which proves `peak ≤ 2`
independent of input length.

## References

- [Danielsson 2008] Nils Anders Danielsson, *Lightweight Semiformal Time
  Complexity Analysis for Purely Functional Data Structures*, POPL 2008. Cost
  monoids for resource analysis ([[node:foundation.cost.costm]]).

## Provenance

- `Cells` is an EconCSLib addition (no `TimeM` counterpart upstream), built on
  the [leanprover/cslib](https://github.com/leanprover/cslib)-derived monad
  core (Apache 2.0).
