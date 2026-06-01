---
id: game_theory.strategic_game.population.wardrop_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Nash Wardrop Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.population.population_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - population-game
  - wardrop-equilibrium
---

# Nash Wardrop Equilibrium

In a population game, a configuration $x\in X$ is a Nash/Wardrop equilibrium if
every strategy used with positive mass is payoff-maximizing for its population:
$$
  x_i(s_i)>0
  \quad\text{implies}\quad
  K_i(s_i,x)\ge K_i(t_i,x)
  \quad\text{for every }t_i\in S_i.
$$

The nonatomic interpretation is essential: a single agent may change strategy
without changing the aggregate configuration $x$.

## References

- [MFoGT, Chapter 5, Def. 5.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nash/Wardrop equilibrium for population games.
