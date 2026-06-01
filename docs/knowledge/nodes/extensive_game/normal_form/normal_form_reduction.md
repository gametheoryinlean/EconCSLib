---
id: game_theory.extensive_game.normal_form.normal_form_reduction
title: Normal Form Reduction
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.normal_form
uses:
  - game_theory.extensive_game.core.strategy_profile_induced_outcome
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - normal-form
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
  declarations:
    - GameTree.PlayerStrategy
    - GameTree.profileStrategy
    - GameTree.toStrategicGame
    - GameTree.toStrategicGame_nash_iff_isNashAt
---

# Normal Form Reduction

The normal form reduction of a perfect-information extensive game is the map
$$
  F:\prod_{i\in I} S_i\to R
$$
that sends each pure strategy profile to the unique terminal outcome it induces.
Composing $F$ with terminal payoff functions gives an ordinary strategic game in
normal form.

## References

- [MFoGT, Def. 6.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The normal or strategic form reduction associates each strategy profile to its induced outcome.
