---
id: foundation.cost.examples.lcs
title: "Worked Example: Longest Common Subsequence DP Grid"
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
    - EconCSLib.Examples.CostM.LCS
  declarations:
    - LCS.lcs
    - LCS.lcs_cost_subset
    - LCS.lcs_cost_card_le
verification:
  proof: accepted
  alignment: aligned
tags:
  - cost
  - example
  - dynamic-programming
---

# Worked Example: Longest Common Subsequence DP Grid

Longest common subsequence in `CostM (Visited (ℕ × ℕ))`: the cost footprint is
now a set of **2-D grid cells** `(i, j)`, one per `(prefix of xs, prefix of
ys)` subproblem. The memoization footprint is contained in the full DP grid,
$$
  (\operatorname{lcs}\,xs\,ys).\mathrm{cost} \;\subseteq\;
    \{0,\dots,|xs|\} \times \{0,\dots,|ys|\},
$$
which is `lcs_cost_subset`; taking cardinalities gives the polynomial-space
bound
$$
  (\operatorname{lcs}\,xs\,ys).\mathrm{cost}.\mathrm{toFinset}.\mathrm{card}
    \;\le\; (|xs|+1)\,(|ys|+1),
$$
i.e. `lcs_cost_card_le`. This is the canonical polynomial-space DP example —
the 2-D analogue of [[node:foundation.cost.examples.memo_fib]].

`lcs` uses the bare `CostM.tick` form (rather than the `✓` macro) at its
footprint-recording points, since each tick records a specific grid cell
`Visited.singleton (i, j)` rather than a unit cost.

## Lean declarations

- `LCS.lcs : List α → List α → CostM (Visited (ℕ × ℕ)) ℕ`.
- `LCS.lcs_cost_subset` — footprint `⊆` the DP grid (via a private
  `range_prod_mono` monotonicity lemma).
- `LCS.lcs_cost_card_le` — the `(|xs|+1)(|ys|+1)` cell-count bound.

## References

- [Danielsson 2008] Nils Anders Danielsson, POPL 2008. Footprint cost monoids
  ([[node:foundation.cost.visited]]).
