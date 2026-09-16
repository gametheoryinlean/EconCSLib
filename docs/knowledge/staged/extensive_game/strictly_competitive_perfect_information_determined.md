---
id: game_theory.extensive_game.perfect_information.strictly_competitive_perfect_information_determined
title: Strictly Competitive Perfect-Information Determinacy
kind: theorem
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.zermelo_determinacy
verification:
  statement: accepted
  proof: gap
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

## Lean Status

`GameTree.zermelo_determinacy` proves a rational-payoff, two-player zero-sum
saddle theorem. A formal encoding from arbitrary strictly competitive outcome
orders to that representation, together with preservation of winning
strategies, is still missing. The general strictly competitive result remains
staged.

## References

- [MFoGT, Cor. 6.2.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every finite strictly competitive perfect-information game is determined.
