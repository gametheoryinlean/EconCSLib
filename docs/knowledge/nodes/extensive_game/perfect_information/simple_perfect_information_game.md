---
id: game_theory.extensive_game.perfect_information.simple_perfect_information_game
title: Simple Perfect-Information Game
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.perfect_information_extensive_game
lean:
  modules:
    - EconCSLib.Examples.SimpleGameTree
  declarations:
    - Examples.SimpleGameTree.sample
    - Examples.SimpleGameTree.sample_zero_sum
    - Examples.SimpleGameTree.sample_zermelo_spe
    - Examples.SimpleGameTree.sample_zermelo_ne
    - Examples.SimpleGameTree.sample_value_zero_sum
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - determinacy
---

# Simple Perfect-Information Game

A two-player perfect-information game is simple if its terminal outcomes are
partitioned into winning sets $(R_1,R_2)$, where reaching a terminal node in $R_i$
means player $i$ wins and the other player loses.

A winning strategy for player $i$ is a strategy $\sigma_i$ such that, for every
opponent strategy $\sigma_{-i}$,
$$
  F(\sigma_i,\sigma_{-i})\in R_i.
$$

## References

- [MFoGT, Section 6.2.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Two-player simple game with terminal outcomes partitioned into winners.
