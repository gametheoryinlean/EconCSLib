---
id: game_theory.extensive_game.imperfect_information.linear_extensive_game
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Linear Extensive Game
kind: definition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.information_set
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - perfect-recall
  - behavioral-strategy
---

# Linear Extensive Game

An extensive game is linear for player $i$ if no play intersects any information
set of player $i$ more than once.

Linearity rules out repeated visits to the same information set along a single play,
which is enough to compare behavioral and mixed strategies in one direction.

## References

- [MFoGT, Def. 6.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Linearity for a player means no play crosses one of that player's information sets more than once.
