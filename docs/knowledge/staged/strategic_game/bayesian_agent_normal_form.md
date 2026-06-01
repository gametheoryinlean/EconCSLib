---
id: game_theory.strategic_game.bayesian.agent_normal_form
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Agent Normal Form Of A Bayesian Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - bayesian-game
  - normal-form
---

# Agent Normal Form Of A Bayesian Game

The agent normal form of a finite Bayesian game replaces each player-type pair
$(i,t_i)$ by a separate agent. The action set of agent $(i,t_i)$ is $A_i$.

The payoff of agent $(i,t_i)$ is the conditional expected payoff of the original
player $i$, conditional on observing type $t_i$, when the other type agents use
their prescribed actions.

This construction turns the interim incentive constraints of a Bayesian
equilibrium into ordinary Nash best-response constraints in a finite
strategic-form game.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Reduction of Bayesian games to strategic-form games by type agents.
