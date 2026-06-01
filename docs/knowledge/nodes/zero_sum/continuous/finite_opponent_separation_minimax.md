---
id: game_theory.strategic_game.zero_sum.continuous.finite_opponent_separation_minimax
title: Finite-Opponent Separation Minimax
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.general_mixed_strategy_space
  - game_theory.strategic_game.zero_sum.core.value
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 3.3.3"
      format: section
      note: "Separation proof of minimax when the minimizing player's pure strategy set is finite"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - mixed-strategy
  - separation
---

# Finite-Opponent Separation Minimax

Assume:

1. $S$ is a measurable space and $X$ is a nonempty convex set of probability
   measures over $S$;
2. $T$ is a finite nonempty set;
3. $g:S\times T\to\mathbb R$ is measurable and bounded.

Then the game $(X,\Delta(T),g)$ has a value, and player 2 has an optimal strategy.

*Proof.* Let $v=\sup_X\inf_T g(x,t)$. Consider the convex payoff-vector set
$$
  D=\{(g(x,t))_{t\in T}:x\in X\}\subseteq\mathbb R^T
$$
and the upper orthant $C=\{a:a_t\ge v+\epsilon\text{ for all }t\}$. These two
convex sets are disjoint. A separating hyperplane gives nonnegative weights on
$T$, normalized to a mixed strategy $y\in\Delta(T)$, such that
$g(x,y)\le v+\epsilon$ for all $x\in X$. Letting $\epsilon\downarrow0$ gives the
value, and compactness of $\Delta(T)$ gives an optimal strategy for player 2.

## References

- [MFoGT, Prop. 3.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Separation proof of minimax when the minimizing player's pure strategy set is finite.
