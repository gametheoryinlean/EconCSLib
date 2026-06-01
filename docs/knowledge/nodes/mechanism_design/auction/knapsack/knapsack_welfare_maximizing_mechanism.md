---
id: mechanism_design.auction.knapsack.welfare_maximizing_mechanism
title: Welfare-Maximizing Knapsack Mechanism
kind: theorem
status: proved
primary_topic: mechanism_design
topics:
  - mechanism_design
  - mechanism_design.auction
  - mechanism_design.auction.knapsack
uses:
  - mechanism_design.auction.knapsack.binary_allocations
  - mechanism_design.myerson.monotonicity_characterization
  - mechanism_design.myerson.payment_formula
lean:
  modules:
    - EconCSLib.MechanismDesign.Auction.Knapsack
  declarations:
    - exists_welfareMaximizer
    - welfareMaximizer
    - maximalSocialWelfare
    - welfareMaximizer_mem_feasibleBinaryAllocations
    - welfareMaximizer_ge
    - welfareMaximizingAllocationRule
    - welfareMaximizingPaymentRule
    - welfareMaximizingMechanism
    - welfareMaximizingAllocationRule_isMonotone
    - welfareMaximizingMechanism_isDSIC
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - auction
  - knapsack
  - dsic
  - myerson
---

# Welfare-Maximizing Knapsack Mechanism

**Theorem.** The mechanism obtained by combining the welfare-maximising
binary allocation rule ([[mechanism_design.auction.knapsack.binary_allocations]]) with
Myerson payments ([[mechanism_design.myerson.payment_formula]]) is a
dominant-strategy incentive compatible (DSIC) single-parameter mechanism
for the knapsack auction environment ([[mechanism_design.auction.knapsack.environment]]),
under the hypothesis $W \ge 0$.

## Construction

Fix a knapsack auction $A : \mathrm{KnapsackAuction}\,I\,\mathbb{R}$ (the DSIC
mechanism with Myerson payments is real-valued) with
`hW : 0 ≤ A.totalCapacity`. From the reported value profile $b$:

1. **Existence**. `exists_welfareMaximizer A b hW` chooses a feasible
   binary allocation $x^*(b) \in A.\mathrm{feasibleBinaryAllocations}$
   maximising `binarySocialWelfare b`. The argument uses
   `List.argMaxOn` over the non-empty list of feasible profiles supplied
   by `feasibleBinaryAllocations_nonempty`.
2. **Maximiser and value**.
   - `welfareMaximizer A b hW : BinaryAllocation I` is the chosen
     maximiser.
   - `maximalSocialWelfare A b hW : ℝ` is its objective value,
     `binarySocialWelfare b (welfareMaximizer A b hW)`.
   - `welfareMaximizer_mem_feasibleBinaryAllocations` certifies
     feasibility; `welfareMaximizer_ge` certifies optimality among
     feasible binary profiles.
3. **Allocation rule**. `welfareMaximizingAllocationRule` returns the
   real-valued allocation `binaryToAllocation (welfareMaximizer b)`,
   i.e. the 0/1 indicator vector of the chosen profile.
4. **Payment rule**. `welfareMaximizingPaymentRule` is the Myerson
   payment rule attached to the welfare-maximising allocation rule via
   `SingleParameterMechanism.withMyersonPayment`.
5. **Packaged mechanism**. `welfareMaximizingMechanism A hW` assembles
   the above into a `KnapsackAuction I` whose single-parameter mechanism
   is `withMyersonPayment` of the welfare-maximising allocation.

## Monotonicity

`welfareMaximizingAllocationRule_isMonotone` proves that the
welfare-maximising allocation rule is monotone in each agent's report:
raising bidder $i$'s reported value cannot remove $i$ from the chosen
allocation. The argument is the standard exchange-style swap:

- Suppose $b'_i > b_i$ and that, at $b$, agent $i$ is in the chosen
  allocation $x^*(b)$.
- The same profile $x^*(b)$ is still feasible at $b'$ (capacity
  depends only on weights, not on bids).
- At $b'$, $x^*(b)$ has weakly larger social welfare than at $b$ since
  only $b_i$ increased and $x^*(b)_i = 1$.
- Hence the welfare-maximising profile at $b'$ also includes $i$ (by
  monotone selection of the argmax).

## DSIC via Myerson

`welfareMaximizingMechanism_isDSIC` chains the monotonicity result with
Myerson's monotonicity characterisation
([[mechanism_design.myerson.monotonicity_characterization]]):

$$
\text{monotone allocation rule} \;\Longrightarrow\;
\text{withMyersonPayment is DSIC}
$$

via `withMyersonPayment_isDSIC_of_isMonotone`. The conclusion is
$$
\mathrm{IsDSIC}(\mathrm{welfareMaximizingMechanism}\,A\,hW),
$$
i.e. truthful reporting is a dominant strategy for every agent in the
knapsack mechanism.

## Why it matters

This is the canonical example of *VCG done by hand* in the single-
parameter Myerson framework: rather than computing $n+1$ welfare maxima
and taking differences (the VCG payment formula), one defines a single
welfare-maximising allocation rule, applies the Myerson critical-value
payment formula, and gets DSIC for free.

The construction is also the optimality benchmark against which the
approximation results in
[[mechanism_design.auction.knapsack.relaxations_dynamic_programming]] are stated: the
fractional greedy rule and the dynamic-programming integer optimum are
compared to this welfare maximum.

## References

- [AGT, Chapter 9, Section 9.5.4, Thm. 9.36] Nisan, Roughgarden, Tardos,
  and Vazirani, *Algorithmic Game Theory*. Monotonicity and critical-value
  payments for single-parameter incentive compatibility.
- [AGT, Chapter 12, Section 12.2] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Monotone allocation algorithms in truthful single-parameter
  approximation mechanisms.
- [AGT, Chapter 11, Theorem 11.6] Nisan, Roughgarden, Tardos, and
  Vazirani, *Algorithmic Game Theory*.
  Welfare maximisation in combinatorial auctions and its truthfulness
  implications.

## Provenance

- Migrated from EconCSLib pull request 27, old blueprint label
  `thm:auction_knapsack_welfare_mechanism` in `blueprint/src/content.tex`.
