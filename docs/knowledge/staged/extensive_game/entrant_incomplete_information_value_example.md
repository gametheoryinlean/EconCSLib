---
id: game_theory.extensive_game.examples.entrant_incomplete_information_value_example
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.examples
title: Entrant Incomplete Information Value Example
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
  - imperfect-information
  - value
  - exercise
---

# Entrant Incomplete Information Value Example

MFoGT Exercise 6.8.7 studies an entry game with Nature choosing whether firm 1
has an innovation, observed only by firm 1. The game is constant-sum and can be
solved through its normal form.

The normal-form payoff matrix in the hints has columns $E,L$ and rows
$SS,SQ,QS,QQ$:

- row $SS$ has payoffs $(2,2)$ and $(4,0)$;
- row $SQ$ has payoffs $(4,0)$ and $(2,2)$;
- row $QS$ has payoffs $(-2,6)$ and $(2,2)$;
- row $QQ$ has payoffs $(0,4)$ and $(0,4)$.

The rows $QS$ and $QQ$ are strictly dominated. In the remaining two-by-two game,
the unique equilibrium has each player randomize equally between the remaining
strategies.

## References

- [MFoGT, Exercise 6.8.7 and Hints for Chapter 6, Exercise 7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Entrant game with incomplete information and the reduced normal-form equilibrium.
