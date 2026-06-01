---
id: game_theory.strategic_game.zero_sum.operators.value_operator_properties
title: Value Operator Properties
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.operators
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3, after Theorem 2.3.1"
      format: section
      note: "Continuity, monotonicity, and non-expansiveness of val"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - value
  - continuity
---

# Value Operator Properties

For finite real matrix games, the value operator $A \mapsto \operatorname{val}(A)$
is continuous, monotone increasing, and non-expansive for the sup norm:
$$
  |\operatorname{val}(A)-\operatorname{val}(B)| \le \|A-B\|_\infty.
$$

*Proof.* If $A\le B$ entrywise, then for every mixed row $x$ and mixed column
$y$ one has $xAy\le xBy$. Taking maxmin values gives
$\operatorname{val}(A)\le\operatorname{val}(B)$, so the value operator is
monotone. Let $\delta=\|A-B\|_\infty$. Then
$$
  A\le B+\delta\mathbf 1
  \quad\text{and}\quad
  B\le A+\delta\mathbf 1.
$$
Adding the constant matrix $\delta\mathbf 1$ raises every mixed payoff, and
therefore the value, by $\delta$. Monotonicity gives
$$
  \operatorname{val}(A)\le\operatorname{val}(B)+\delta
  \quad\text{and}\quad
  \operatorname{val}(B)\le\operatorname{val}(A)+\delta,
$$
which is the non-expansive estimate. Non-expansiveness implies continuity.

## References

- [MFoGT, Chapter 2, Section 2.3, after Thm. 2.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Continuity, monotonicity, and non-expansiveness of val.
