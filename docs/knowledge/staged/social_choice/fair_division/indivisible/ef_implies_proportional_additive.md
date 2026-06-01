---
id: social_choice.fair_division.indivisible.ef_implies_proportional_additive
title: EF ⇒ PROP (Additive Valuations, Complete Allocations)
kind: theorem
status: staged
primary_topic: social_choice
topics:
  - social_choice
  - social_choice.fair_division
  - social_choice.fair_division.indivisible
uses:
  - social_choice.fair_division.indivisible.envy_free
  - social_choice.fair_division.indivisible.proportional
  - social_choice.fair_division.indivisible.additive_valuation
lean:
  modules:
    - EconCSLib.SocialChoice.FairDivision.Indivisible.Implications
  declarations:
    - SocialChoice.FairDivision.Indivisible.IsEnvyFree.isProportional_additive
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - fair-division
  - indivisible
  - additive
  - envy-free
  - proportional
---

# EF ⇒ PROP (Additive Valuations, Complete Allocations)

**Theorem.** Let $w : N \to G \to \mathbb{R}$ be an additive valuation
([[social_choice.fair_division.indivisible.additive_valuation]]),
`allGoods : Finset G` the outer good set, and $A$ a complete allocation
of `allGoods` ([[social_choice.fair_division.indivisible.allocation]]).
If $A$ is envy-free under $w.\mathrm{toValuation}$
([[social_choice.fair_division.indivisible.envy_free]]), then $A$ is
proportional with population size $|N|$
([[social_choice.fair_division.indivisible.proportional]]).

In Lean: `SocialChoice.FairDivision.Indivisible.IsEnvyFree.isProportional_additive`.

## Proof

For each agent $k$, partition $\mathrm{allGoods}$ via $A$ and use
additivity:
$$
\begin{aligned}
v_k(\mathrm{allGoods})
  &= \sum_{j} v_k(A(j)) && \text{additivity over the disjoint cover} \\
  &\le \sum_{j} v_k(A(k)) && \text{envy-freeness: $v_k(A(j)) \le v_k(A(k))$} \\
  &= |N| \cdot v_k(A(k)) && \text{constant sum.}
\end{aligned}
$$

The first equality combines `IsAllocation.complete` (the cover) with
`AdditiveValuation.toValuation_union` extended to a `biUnion` over the
disjoint family.

## Caveats

- *Additivity is essential.* For non-additive valuations EF does not
  imply PROP — additivity is what converts "weakly less than $A(k)$"
  (a per-bundle inequality) into "total value bounded by $n \cdot
  v_k(A(k))$" (a sum bound).

- *EF1 does not imply PROP.* The counterexample (2 agents, 3
  equal-value goods, give 1 to agent A and 2 to agent B; A is EF1 but
  $v_A < |\mathrm{allGoods}|/2 \cdot v_A(A(A))$) is real even with
  additive valuations.

## References

- [AGT Chapter 11] Nisan, Roughgarden, Tardos, and Vazirani, *Algorithmic Game Theory*. EF-PROP for additive valuations.
