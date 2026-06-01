---
id: game_theory.extensive_game.examples.chomp_strategy_stealing
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.examples
title: Chomp Strategy Stealing
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.zermelo_determinacy
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - perfect-information
  - exercise
---

# Chomp Strategy Stealing

For finite $n,m\ge 1$, the $n\times m$ Chomp game is a finite perfect-information
game. The first player has a winning strategy.

When $n=m$, an explicit winning strategy is:

- first choose square $(2,2)$;
- after the opponent chooses $(1,k)$, choose $(k,1)$;
- after the opponent chooses $(k,1)$, choose $(1,k)$.

## Proof Sketch

By Zermelo determinacy, one of the two players has a winning strategy. If the
second player had one, the first player could make a harmless initial move and
then imitate the second player's winning response, contradicting the assumed
second-player win.

## References

- [MFoGT, Exercise 6.8.1 and Hints for Chapter 6, Exercise 1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite Chomp first-player win and square-board explicit mirror strategy.
