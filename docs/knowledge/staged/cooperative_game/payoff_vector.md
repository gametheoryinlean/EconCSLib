---
id: game_theory.cooperative_game.payoff_vector
title: Payoff Vector
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.tu_game
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Basic
  declarations:
    - CoalitionalGame.PayoffVector
    - CoalitionalGame.coalitionPayoff
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - payoff-vector
  - imputation
---

# Payoff Vector

Given a coalitional game on player set $N$, a **payoff vector** is a function
$$
  x : N \to \mathbb{R}.
$$
It specifies the final payoff allocated to each individual player.

The total payoff assigned to a coalition $S \subseteq N$ is
$$
  x(S) = \sum_{i \in S} x_i.
$$
Coalitional-game solution concepts compare this allocated amount with the
coalition worth $v(S)$.

## Role In The Blueprint

This is the common input object for imputations
([[game_theory.cooperative_game.imputation]]), the core
([[game_theory.cooperative_game.core]]), and the Shapley value
([[game_theory.cooperative_game.shapley_value]]).

## References

- [MSZ Ch.16, Def 16.1 and Def 16.13-16.16] Maschler, Solan, Zamir,
  *Game Theory*.
