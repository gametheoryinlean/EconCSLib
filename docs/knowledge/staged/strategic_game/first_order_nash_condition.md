---
id: game_theory.strategic_game.continuous.first_order_nash_condition
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: First-Order Nash Condition
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.continuous.smooth_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - smooth-game
  - variational-inequality
---

# First-Order Nash Condition

Let $G$ be a smooth Hilbert game. If $s$ is a Nash equilibrium, then
$$
  \sum_{i\in I}
  \langle \nabla_i g_i(s),\, s_i-t_i\rangle
  \ge 0
  \quad\text{for all }t\in S.
$$
If the game is concave, this condition is also sufficient for $s$ to be a Nash
equilibrium.

## Proof Sketch

For each player, Nash optimality means $s_i$ locally maximizes
$g_i(\cdot,s_{-i})$ on a convex set. The first-order necessary condition gives the
corresponding inner-product inequality. Summing over players yields the displayed
variational inequality. If each payoff is concave in the player's own variable, the
same first-order condition is sufficient for global optimality, hence for Nash
equilibrium.

## References

- [MFoGT, Thm. 4.7.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. First-order variational inequality characterization in smooth games.
