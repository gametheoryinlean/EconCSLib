---
id: game_theory.strategic_game.continuous.supermodular_best_response_lattice
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Supermodular Best Responses Are Lattices
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.continuous.supermodular_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - supermodular-game
  - best-response
---

# Supermodular Best Responses Are Lattices

In a supermodular game, for every player $i$ and opponent profile $s_{-i}$, the
best-response set $BR_i(s_{-i})$ is a nonempty compact lattice.

Moreover, best responses are monotone in the following sense: if
$s_{-i}\ge s'_{-i}$ and $t'_i\in BR_i(s'_{-i})$, then there exists
$t_i\in BR_i(s_{-i})$ such that
$$
  t_i\ge t'_i.
$$

## References

- [MFoGT, Section 4.12, Exercise 4(2a-b)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Best-response lattice and monotonicity properties in supermodular games.
