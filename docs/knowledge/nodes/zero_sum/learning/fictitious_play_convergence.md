---
id: game_theory.strategic_game.zero_sum.learning.fictitious_play_convergence
title: Fictitious Play Convergence
kind: theorem
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.cesaro_payoff_from_robinson
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 2.7.2"
      format: section
      note: "Convergence of fictitious play in finite zero-sum games"
verification:
  statement: accepted
  proof: gap
tags:
  - zero-sum
  - learning
  - fictitious-play
---

# Fictitious Play Convergence

Let $(i_n,j_n)_{n\ge1}$ be a fictitious-play realization in a finite matrix game
$A$, and let $(x_n,y_n)$ be the empirical frequencies of play.

MFoGT Thm. 2.7.2 has two conclusions.

First, the empirical frequencies approach the optimal-strategy sets
$X(A)\times Y(A)$. Explicitly, for every $\varepsilon>0$ there is $N$ such that,
for every $n\ge N$,
$$
  x_nAy\ge \operatorname{val}(A)-\varepsilon
  \quad\text{for all }y\in\Delta(J),
$$
and
$$
  xAy_n\le \operatorname{val}(A)+\varepsilon
  \quad\text{for all }x\in\Delta(I).
$$

Second, the Cesaro average of realized payoffs converges to the value:
$$
  \frac1n\sum_{t=1}^n A_{i_tj_t}
  \longrightarrow \operatorname{val}(A).
$$

*Proof.* The two conclusions decouple along independent technical chains.

**Frequency convergence to optimal strategies.** By
[[game_theory.strategic_game.zero_sum.learning.robinson_admissible_lemma]] the cumulative duality
gap $\mu(n) := \max_i \beta^i(n) - \min_j \alpha^j(n)$ is $o(n)$. Dividing by
$n$ and using $\alpha(n)/n = x_n A + O(1/n)$ and $\beta(n)/n = A y_n + O(1/n)$,
the two eventual optimality inequalities follow, so the empirical frequencies
approach $X(A) \times Y(A)$.

**Cesàro payoff convergence.** This is a separate elementary telescoping
argument; see [[game_theory.strategic_game.zero_sum.learning.cesaro_payoff_from_robinson]] for the
self-contained derivation $R_n / n \to \operatorname{val}(A)$ from the
$o(n)$ gap bound.

## References

- [MFoGT, Thm. 2.7.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Convergence of fictitious play in finite zero-sum games.
