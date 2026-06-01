---
id: game_theory.strategic_game.population.population_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Population Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - population-game
---

# Population Game

A population game has a finite set $I$ of nonatomic populations. For each
population $i$, the finite set $S_i$ lists the strategies available to agents in
that population, and
$$
  X_i=\Delta(S_i)
$$
is the simplex of population shares. A configuration is
$x=(x_i)_{i\in I}\in X=\prod_i X_i$, where $x_i(s_i)$ is the proportion of
population $i$ using strategy $s_i$.

The payoff data are maps
$$
  K_i:S_i\times X\to\mathbb R,
$$
where $K_i(s_i,x)$ is the payoff of an individual agent of population $i$ who
uses $s_i$ when the aggregate configuration is $x$.

## References

- [MFoGT, Chapter 5, Section 5.2.1.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Population games and nonatomic strategy proportions.
