---
id: mechanism_design.auction.knapsack.environment
title: Knapsack Auction Environment
kind: definition
status: formalized
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.knapsack
uses:
  - mechanism_design.transfer.single_parameter_transfer_layer
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.Knapsack
  declarations:
    - KnapsackAuction
    - KnapsackAuction.RespectsCapacity
    - KnapsackAuction.IsFeasible
    - KnapsackAuction.size
    - KnapsackAuction.capacity
    - KnapsackAuction.NonnegativeWeights
    - KnapsackAuction.PositiveWeights
    - KnapsackAuction.NonnegativeCapacity
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - auction
  - knapsack
  - single-parameter
---

# Knapsack Auction Environment

A **knapsack auction** is a single-parameter mechanism
([[mechanism_design.transfer.single_parameter_transfer_layer]]) equipped
with two pieces of public data: a per-agent weight (item size) and a
global capacity bound.

## Structure

`KnapsackAuction I U` extends `SingleParameterMechanism I U`, where the value
type `U` is any **linearly ordered field** (`[Field U] [LinearOrder U]
[IsStrictOrderedRing U]`; `ℚ`, `ℝ`, …):

- `weight : I → U` — the public, common-knowledge size of agent `i`'s
  item.
- `totalCapacity : U` — the total weight the knapsack can hold.

The combinatorial layer (welfare, welfare-maximizing allocation, fractional
greedy) is generic in `U`; the Myerson-payment **DSIC mechanism** is pinned to
`U = ℝ` because the Myerson payment formula is real-valued.

The inherited single-parameter fields are:

- `allocationRule : (I → ℝ) → I → ℝ` — given the reported value profile
  $b$, returns each agent's fractional allocation $x_i(b) \in \mathbb{R}$.
- `paymentRule : (I → ℝ) → I → ℝ` — the per-agent payment.

This shape covers both the integral 0/1 knapsack (when `x_i ∈ {0, 1}`)
and its fractional/LP relaxation (when `x_i ∈ [0, 1]`).

## Feasibility

Two predicates capture knapsack feasibility:

- `IsAllocFeasible` (inherited): each $x_i(b) \in [0, 1]$.
- `RespectsCapacity`: the weighted allocation respects the capacity
  $$
  \forall b.\; \sum_{i \in I} w_i \, x_i(b) \;\le\; W.
  $$
- `IsFeasible` is the conjunction of both.

This separation lets one prove allocation-bound and capacity-bound
properties independently — useful when the allocation is built up from
greedy/LP machinery in stages.

## Sign hypotheses

Three sign predicates are offered as named hypotheses, so theorems can
state precisely which positivity assumption they need:

- `NonnegativeWeights A`: $\forall i.\; w_i \ge 0$. Standard for knapsack.
- `PositiveWeights A`: $\forall i.\; w_i > 0$. Needed when dividing by
  $w_i$ (e.g. value-density ranking for greedy approximation).
- `NonnegativeCapacity A`: $0 \le W$. Needed to ensure the empty
  allocation is feasible (the base case of all welfare-maximisation
  arguments — see [[mechanism_design.auction.knapsack.binary_allocations]]).

Convenience accessors `size A i := A.weight i` and
`capacity A := A.totalCapacity` are provided to keep theorem statements
readable.

## Position in the library

The knapsack auction is the canonical single-parameter mechanism with a
non-trivial allocation constraint. It sits below:

- The binary 0/1 allocation layer ([[mechanism_design.auction.knapsack.binary_allocations]])
  used for both the welfare-maximisation argument and the dynamic-
  programming solver.
- The welfare-maximising Myerson mechanism
  ([[mechanism_design.auction.knapsack.welfare_maximizing_mechanism]]) and the
  relaxation/DP analysis ([[mechanism_design.auction.knapsack.relaxations_dynamic_programming]]).

## References

- [AGT, Chapter 12, Section 12.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Single-parameter domains, monotone allocation rules, and the knapsack
  approximation mechanism.
- [AGT, Chapter 11, Sections 11.1-11.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Combinatorial-auction allocation constraints and single-minded bidder
  feasibility models.
- [AGT, Chapter 9, Section 9.5.4] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Single-parameter Myerson framework, which the knapsack auction
  specialises.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `def:auction_knapsack_environment` in `blueprint/src/content.tex`.
