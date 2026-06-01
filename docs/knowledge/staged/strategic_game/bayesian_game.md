---
id: game_theory.strategic_game.bayesian.bayesian_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Bayesian Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - bayesian-game
  - incomplete-information
---

# Bayesian Game

A finite Bayesian game models incomplete information by giving each player a
type and allowing payoffs to depend on the full type profile.

The data consist of players $I$, finite action sets $(A_i)$, finite type sets
$(T_i)$, a common prior $p\in\Delta(T)$ on $T=\prod_i T_i$, and payoff functions
$$
  g_i:A\times T\to\mathbb R,
  \qquad A=\prod_i A_i.
$$
Player $i$ observes only their own type $t_i$ before choosing an action.

The common prior records the ex-ante probability of type profiles. Conditional
beliefs about other players' types are derived from the prior whenever the
observed type has positive probability.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Games with incomplete information, also called Bayesian games.
