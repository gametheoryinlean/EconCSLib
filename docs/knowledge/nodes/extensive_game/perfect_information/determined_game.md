---
id: game_theory.extensive_game.perfect_information.determined_game
title: Determined Game
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.simple_perfect_information_game
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Zermelo
  declarations:
    - GameTree.IsZeroSum
    - GameTree.value_zero_sum
    - GameTree.zermelo_determinacy
    - GameTree.value₀_eq_outcome_and_zeroSum
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - determinacy
---

# Determined Game

A simple two-player game is determined if one of the two players has a winning
strategy.

Because the winning sets $R_1$ and $R_2$ are disjoint, both players cannot have
winning strategies simultaneously.

## References

- [MFoGT, Def. 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A game is determined if one player has a winning strategy.
