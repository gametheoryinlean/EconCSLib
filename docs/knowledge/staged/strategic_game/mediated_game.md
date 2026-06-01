---
id: game_theory.strategic_game.correlated.mediated_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Mediated Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategy_profile
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - correlated-equilibrium
---

# Mediated Game

Given a finite strategic-form game, a mediated game augments play with a
correlating device. The device samples a pure strategy profile
$s\in\prod_i S_i$ according to a probability distribution and privately
recommends $s_i$ to player $i$.

Players observe only their own recommendations and then choose whether to obey
or deviate.

## References

- [MSZ, Chapter 8, before Def. 8.4] Maschler, Solan, and Zamir, *Game Theory*. A mediator samples a strategy profile and privately recommends each component.
