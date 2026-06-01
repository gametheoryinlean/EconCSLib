---
id: game_theory.strategic_game.dominance.dominance_solvable_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Solvable Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.dominance.rationalizable_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.IESDS
  declarations:
    - StrategicGame.IsDominanceSolvable
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - rationalizability
---

# Solvable Game

A game is solvable if the set $S^\infty$ of rationalizable outcomes is reduced to
a singleton:
$$
  S^\infty=\{s^*\}.
$$
This captures games whose common-rationality elimination process predicts a
unique profile.

## References

- [MFoGT, Def. 4.4.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A game is solvable if the rationalizable outcome set is a singleton.
- [MFoGT, Section 1.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Earlier use of solvability for iterated elimination.
