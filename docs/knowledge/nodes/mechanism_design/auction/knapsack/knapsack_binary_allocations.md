---
id: mechanism_design.auction.knapsack.binary_allocations
title: Binary Knapsack Allocations
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.knapsack
uses:
  - mechanism_design.auction.knapsack.environment
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.Knapsack
  declarations:
    - BinaryAllocation
    - binaryToAllocation
    - binaryLoad
    - binaryRespectsCapacity
    - feasibleBinaryAllocations
    - binarySocialWelfare
    - zeroBinaryRespectsCapacity
    - feasibleBinaryAllocations_nonempty
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - knapsack
  - binary-allocation
---

# Binary Knapsack Allocations

The binary-allocation layer specialises the knapsack auction environment
([[mechanism_design.auction.knapsack.environment]]) to **0/1 allocations**: each agent is
either selected or not. This is the standard combinatorial substrate for
the 0/1 knapsack problem and for the welfare-maximising knapsack
mechanism.

## Boolean profiles

- **`BinaryAllocation I := I → Bool`** — a profile assigning each agent a
  Boolean inclusion flag.
- **`binaryToAllocation x i : ℝ`** — coerces the Boolean profile to a
  real-valued allocation vector: `1` if `x i = true`, `0` otherwise.
  This is the bridge to the single-parameter mechanism's real-valued
  allocation rule.

## Load and feasibility

- **`binaryLoad A x : ℝ`** — the total weight selected:
  $$
  \mathrm{binaryLoad}(A, x) \;=\; \sum_{i \in I} w_i \cdot \mathbf{1}[x_i].
  $$
- **`binaryRespectsCapacity A x`** — the predicate
  $\mathrm{binaryLoad}(A, x) \le W$.
- **`feasibleBinaryAllocations A`** — the *list* of all feasible binary
  profiles, computed by filtering the finite cartesian product
  $\{0,1\}^I$ on `binaryRespectsCapacity`. Implemented via
  `Finset.toList` of the filtered universe to support `List.argMaxOn` in
  downstream welfare-maximisation arguments.

## Welfare objective

- **`binarySocialWelfare b x : ℝ`** — the social-welfare functional at
  valuation profile $b : I \to \mathbb{R}$:
  $$
  \mathrm{binarySocialWelfare}(b, x) \;=\; \sum_{i \in I} b_i \cdot \mathbf{1}[x_i],
  $$
  i.e. the total reported value collected by selected agents.

## Existence of feasible allocations

The all-zero profile is the structural witness:

- **`zeroBinaryRespectsCapacity A hW`** — assuming
  `hW : 0 ≤ A.totalCapacity`, the all-zero profile is feasible (its load
  is `0 ≤ W`).
- **`feasibleBinaryAllocations_nonempty A hW`** — the feasible-allocations
  list is non-empty under the same hypothesis.

Non-emptiness is the precondition for invoking `List.argMaxOn` to choose
a welfare-maximising feasible allocation, which is what
[[mechanism_design.auction.knapsack.welfare_maximizing_mechanism]] does.

## Why a list rather than a Finset

The downstream `welfareMaximizer` uses `List.exists_argMax_on` (which
operates on lists with a non-emptiness witness given by the
`head :: tail` shape) rather than `Finset.exists_max_image`. The list
formulation matches the linear-time algorithmic flavour and pairs
cleanly with the dynamic-programming solver in
[[mechanism_design.auction.knapsack.relaxations_dynamic_programming]].

## References

- [AGT, Chapter 12, Section 12.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Binary 0/1 allocation rules in single-parameter mechanism-design
  domains.
- [AGT, Chapter 11, Section 11.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Single-minded combinatorial-auction feasibility and welfare objectives.
- [AGT, Chapter 12, Lemma 12.7] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Welfare maximisation over binary profiles as the reference benchmark
  for approximation mechanisms.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:auction_knapsack_binary` in `blueprint/src/content.tex`.
