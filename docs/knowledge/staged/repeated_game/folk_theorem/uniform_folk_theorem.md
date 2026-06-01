---
id: game_theory.repeated_game.folk_theorem.uniform_folk_theorem
title: Uniform Folk Theorem
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.folk_theorem
uses:
  - game_theory.repeated_game.core.uniform_equilibrium
  - game_theory.repeated_game.core.feasible_individually_rational_payoffs
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - repeated-game
  - folk-theorem
---

# Uniform Folk Theorem

In a standard repeated game with public monitoring, the set of uniform
equilibrium payoffs is exactly the feasible and individually rational set:
$$
  E_\infty=E.
$$

The construction follows a feasible main path and punishes the first deviator at
their independent minmax level forever.

## References

- [MFoGT, Chapter 8, Thm. 8.5.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Uniform equilibrium payoffs equal feasible individually rational payoffs.
