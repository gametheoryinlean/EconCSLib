---
id: mechanism_design.auction.knapsack.relaxations_dynamic_programming
title: Knapsack Relaxations And Dynamic Programming
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.knapsack
uses:
  - mechanism_design.auction.knapsack.welfare_maximizing_mechanism
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.Knapsack
  declarations:
    - fractionalSocialWelfare
    - fractionalFeasible
    - fractionalGreedyAllocation
    - fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal
    - dpSolveList
    - dynamicProgrammingOptimalAllocation
    - dynamicProgrammingOptimalValue
    - dynamicProgrammingOptimalAllocation_feasible
    - dynamicProgrammingOptimalAllocation_optimal
    - integralGreedyAllocation
    - integralGreedyValue
    - natFractionalGreedyAllocation
    - natFractionalGreedyValue
    - dynamicProgrammingOptimalAllocation_fractionalFeasible
    - integralGreedy_halfApprox_dpOptimal
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - knapsack
  - dynamic-programming
  - approximation
---

# Knapsack Relaxations And Dynamic Programming

This node assembles the algorithmic layer of the knapsack auction
([[mechanism_design.auction.knapsack.environment]]): the fractional LP relaxation, the
integer dynamic-programming solver, the integral greedy rule, and their
quantitative comparisons.

The headline result is a $1/2$-approximation: the integral greedy
allocation achieves at least half the welfare of the dynamic-programming
optimum.

## Fractional relaxation

The LP relaxation drops the 0/1 constraint to $x_i \in [0, 1]$ while
keeping the same capacity and welfare:

- **`fractionalSocialWelfare b x : ℝ`** — the welfare functional applied
  to a real-valued allocation profile $x : I \to \mathbb{R}$:
  $\sum_i b_i x_i$.
- **`fractionalFeasible A x`** — the LP feasibility predicate:
  $\forall i.\; 0 \le x_i \le 1$ together with
  $\sum_i w_i x_i \le W$.
- **`fractionalGreedyAllocation A b`** — the value-density greedy LP
  solution: sort agents by $b_i / w_i$ in decreasing order, fill
  capacity, then split the *last* fractional agent. This is the
  classical greedy LP optimiser for the fractional knapsack.

The first bridge inequality
**`fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal`** establishes
that the fractional greedy welfare upper-bounds the integral
welfare-maximising 0/1 objective:
$$
\mathrm{fractionalSocialWelfare}(b, \mathrm{fractionalGreedyAllocation}(A, b))
\;\ge\;
\mathrm{binarySocialWelfare}(b, x^*(b)),
$$
i.e. the LP optimum dominates the IP optimum (the standard LP
relaxation gap inequality, but explicit on the greedy LP solver).

## Dynamic programming (integer 0/1)

For the natural-number specialisation (weights and capacity are
nonnegative integers), an explicit dynamic-programming solver:

- **`dpSolveList`** — table-based DP that runs over a list of items,
  returning per-capacity optimal selections.
- **`dynamicProgrammingOptimalAllocation A b`** — the
  `BinaryAllocation` reconstructed from the DP table.
- **`dynamicProgrammingOptimalValue A b`** — the DP objective value.
- **`dynamicProgrammingOptimalAllocation_feasible`** — the DP output
  respects the capacity constraint.
- **`dynamicProgrammingOptimalAllocation_optimal`** — the DP output
  attains the maximum of `binarySocialWelfare b` over the feasible
  0/1 search space.
- **`dynamicProgrammingOptimalAllocation_fractionalFeasible`** — bridge
  lemma certifying that the DP allocation, viewed as a real-valued
  allocation via `binaryToAllocation`, is `fractionalFeasible`.

Combined, these lemmas verify that the DP solver is a *correct*
algorithm for the integer knapsack: it produces the unique-up-to-ties
optimum of the same combinatorial problem solved abstractly by
[[mechanism_design.auction.knapsack.welfare_maximizing_mechanism]], but constructively
and in pseudo-polynomial time.

## Integral greedy and the half-approximation

- **`integralGreedyAllocation`** — round the fractional greedy solution
  to 0/1 by dropping the split agent.
- **`integralGreedyValue`** — the welfare of the integral greedy
  allocation.
- **`natFractionalGreedyAllocation`, `natFractionalGreedyValue`** —
  the natural-number specialisations used in the comparison with the
  DP optimum.

The headline approximation guarantee is:

**Theorem (`integralGreedy_halfApprox_dpOptimal`).** Under the standard
sign hypotheses on weights, capacity, and bids,
$$
\mathrm{dpOptimalValue}(A, b) \;\le\; 2 \cdot \mathrm{integralGreedyValue}(A, b),
$$
i.e. the integral greedy rule achieves at least $1/2$ of the optimal
integer welfare.

### Proof sketch

The LP optimum upper-bounds the integer optimum
(`fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal`). The LP optimum
is bounded by twice the better of two integer feasible allocations:
"the integral greedy prefix" and "the single best item alone". The
half-approximation then follows by triangle inequality, taking the
better of the two as `integralGreedyValue`.

## Position in the library

These results are the algorithmic counterpart to the truthfulness story
in [[mechanism_design.auction.knapsack.welfare_maximizing_mechanism]]: the abstract
welfare maximiser is replaced by a *constructive* (DP) or
*approximation* (integral greedy) algorithm, and the approximation is
quantified explicitly. In Myerson terms, both algorithms induce monotone
allocation rules (in the value parameter), so they can in principle be
combined with Myerson payments to produce DSIC approximation mechanisms
in the spirit of AGT Chapter 12.

## References

- [AGT, Chapter 12, Sections 12.1-12.3] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Fractional LP relaxation, dynamic-programming solvers, and integral
  greedy half-approximation for single-parameter approximation
  mechanisms.
- [AGT, Chapter 11, Section 11.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Greedy allocation rules, critical payments, and approximation
  analysis in combinatorial auctions.
- [Vazirani 2001, Chapter 8] Vijay Vazirani, *Approximation Algorithms*.
  Classical $1/2$- and FPTAS-style analyses for the 0/1 knapsack
  problem.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:auction_knapsack_algorithms` in `blueprint/src/content.tex`.
