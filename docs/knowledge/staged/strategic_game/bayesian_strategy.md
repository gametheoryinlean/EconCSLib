---
id: game_theory.strategic_game.bayesian.bayesian_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - bayesian-game
  - strategy
---

# Bayesian Strategy

In a Bayesian game, a pure strategy of player $i$ is a type-contingent action
plan
$$
  s_i:T_i\to A_i.
$$
It specifies what player $i$ will do after each type that player might observe.

A mixed or behavioral Bayesian strategy assigns to each type a distribution over
actions:
$$
  \sigma_i:T_i\to\Delta(A_i).
$$
A Bayesian strategy profile is a tuple of such type-contingent plans, one for
each player.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strategies in Bayesian games are type-contingent plans.
