---
id: game_theory.strategic_game.zero_sum.continuous.compact_mixed_vs_finite_support_minimax
title: Compact Mixed Versus Finite-Support Minimax
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.general_mixed_strategy_space
  - game_theory.strategic_game.zero_sum.continuous.pure_minimax_compact_convex_one_sided
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 3.3.1"
      format: section
      note: "The game (Delta(S), Delta_f(T), g) has a value under compactness and upper semicontinuity"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - mixed-strategy
  - minimax
---

# Compact Mixed Versus Finite-Support Minimax

Let $(S,T,g)$ be a zero-sum game such that $S$ is compact Hausdorff and
$g(\cdot,t)$ is upper semicontinuous for every $t\in T$. Then the mixed game
$$
  (\Delta(S),\Delta_f(T),g)
$$
has a value, and player 1 has an optimal strategy.

*Proof.* The space $\Delta(S)$ is compact in the weak-star topology, and integration
preserves upper semicontinuity of $g(\cdot,t)$. The payoff is bilinear on
$\Delta(S)\times\Delta_f(T)$. Thus the one-sided compact convex minimax theorem
applies.

## References

- [MFoGT, Prop. 3.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The game (Delta(S), Delta_f(T), g) has a value under compactness and upper semicontinuity.
