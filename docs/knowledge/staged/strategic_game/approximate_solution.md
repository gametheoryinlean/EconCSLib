---
id: game_theory.strategic_game.refinements.approximate_solution
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Approximate Solution
kind: definition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.epsilon_equilibrium
  - game_theory.strategic_game.refinements.reny_solution
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - approximate-equilibrium
---

# Approximate Solution

A pair $(s,v)\in\overline\Gamma$ is an approximate solution if there exist
profiles $s^n$ and positive numbers $\epsilon_n\to 0$ such that:

1. each $s^n$ is an $\epsilon_n$-equilibrium;
2. $(s^n,g(s^n))\to(s,v)$.

The profile $s$ is then called an approximate equilibrium.

## References

- [MFoGT, Def. 4.8.9] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Approximate solution and approximate equilibrium.
