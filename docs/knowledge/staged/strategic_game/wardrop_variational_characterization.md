---
id: game_theory.strategic_game.population.wardrop_variational_characterization
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Wardrop Variational Characterization
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.population.wardrop_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - population-game
  - variational-inequality
---

# Wardrop Variational Characterization

For a population game, $x\in X$ is a Nash/Wardrop equilibrium if and only if
$$
  \langle K(x),x-y\rangle\ge 0
  \quad\text{for every }y\in X,
$$
where
$$
  \langle K(x),x-y\rangle
  =
  \sum_i\sum_{s_i\in S_i}K_i(s_i,x)(x_i(s_i)-y_i(s_i)).
$$

This expresses the equilibrium condition as a variational inequality over the
product of population simplexes.

## References

- [MFoGT, Chapter 5, Prop. 5.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Variational inequality form of Nash/Wardrop equilibrium.
