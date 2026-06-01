---
id: game_theory.extensive_game.examples.poker_game_value_example
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.examples
title: Poker Game Value Example
kind: example
status: staged
uses:
  - game_theory.extensive_game.core.nature_player
  - game_theory.extensive_game.imperfect_information.imperfect_information_extensive_game
  - game_theory.strategic_game.zero_sum.core.value
verification:
  proof: not_applicable
tags:
  - extensive-game
  - zero-sum
  - imperfect-information
  - exercise
---

# Poker Game Value Example

MFoGT Exercise 6.8.2 studies a two-card zero-sum poker game with Nature choosing
$H$ or $L$ uniformly and only player 1 observing the card.

After eliminating strictly dominated rows, the relevant normal-form zero-sum game
has value $1/3$. Player 1's unique optimal mixed strategy is
$$
  \frac13(CH,CL)+\frac23(CH,SL).
$$
Equivalently, player 1 always continues with a high card and bluffs with a low
card with probability $1/3$.

Player 2 checks with probability $2/3$ and stops with probability $1/3$.

## References

- [MFoGT, Exercise 6.8.2 and Hints for Chapter 6, Exercise 2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Zero-sum poker game, normal form, value, and optimal behavioral strategies.
