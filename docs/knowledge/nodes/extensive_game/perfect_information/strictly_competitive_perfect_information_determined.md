---
id: game_theory.extensive_game.perfect_information.strictly_competitive_perfect_information_determined
title: Strictly Competitive Perfect-Information Determinacy
kind: theorem
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.zermelo_determinacy
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Zermelo
  declarations:
    - GameTree.zermelo_determinacy
    - GameTree.value_zero_sum
    - GameTree.value₀_eq_outcome_and_zeroSum
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - extensive-game
  - determinacy
  - zero-sum
---

# Strictly Competitive Perfect-Information Determinacy

Every finite strictly competitive game with perfect information is determined.

Equivalently, when terminal outcomes are interpreted as player 1 payoffs and
player 2 has the opposite preference order, the game has a pure-strategy value.

## Proof Sketch

Order outcomes by player 1's preference. Let $R_k$ be the smallest initial segment
of outcomes that player 1 can guarantee. Player 1 can guarantee $R_k$, while by
Zermelo determinacy player 2 can guarantee the complement of $R_{k-1}$. This
identifies the threshold outcome and gives determinacy.

## References

- [MFoGT, Cor. 6.2.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every finite strictly competitive perfect-information game is determined.
