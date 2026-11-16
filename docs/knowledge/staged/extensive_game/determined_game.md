---
id: game_theory.extensive_game.perfect_information.determined_game
title: Determined Game
kind: definition
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.simple_perfect_information_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - extensive-game
  - determinacy
---

# Determined Game

A simple two-player game is determined if one of the two players has a winning
strategy.

Because the winning sets $R_1$ and $R_2$ are disjoint, both players cannot have
winning strategies simultaneously.

## Lean Status

The current Zermelo module defines rational zero-sum payoffs and proves a
saddle-value theorem. It does not define winning outcome sets, winning
strategies, or the textbook `Determined` predicate stated here.

## References

- [MFoGT, Def. 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A game is determined if one player has a winning strategy.
