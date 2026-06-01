---
id: game_theory.strategic_game.zero_sum.continuous.monotone_family_assumption_counterexamples
title: Monotone Family Assumption Counterexamples
kind: example
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.monotone_decreasing_values_limit
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 3(2)"
      format: section
      note: "Examples showing why compactness and monotonicity assumptions matter in the monotone-family value theorem"
    - artifact: mfogt
      locator: "Section 9.3, Exercise 3 hints"
      format: section
      note: "Both examples have v_n=1 and limiting value 0"
verification:
  proof: not_applicable
tags:
  - zero-sum
  - value
  - limit
  - counterexample
---

# Monotone Family Assumption Counterexamples

MFoGT Exercise 3.5.3(2) gives two one-player examples showing why the hypotheses
in the monotone-family value theorem are not cosmetic.

In the first example,
$$
  S=[0,+\infty),\qquad f_n(s)=\mathbf 1_{s\ge n}.
$$
For each $n$, the value is $v_n=1$, but the pointwise infimum has value $0$.
The failure is that $S$ is not compact.

In the second example, $S=[0,1]$ is compact and $f_n$ is continuous and
piecewise linear with
$$
  f_n(0)=f_n(2/n)=f_n(1)=0,\qquad f_n(1/n)=1.
$$
Again $v_n=1$ for each $n$, while the limiting value is $0$. The failure is that
the sequence $(f_n)$ is not monotone decreasing.

These examples explain the role of compactness of $S$ and monotone decrease of
the payoff sequence in `zero_sum.continuous.monotone_decreasing_values_limit`.

## References

- [MFoGT, Section 3.5, Exercise 3(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Examples showing why compactness and monotonicity assumptions matter in the monotone-family value theorem.
- [MFoGT, Section 9.3, Exercise 3 hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Both examples have v_n=1 and limiting value 0.
