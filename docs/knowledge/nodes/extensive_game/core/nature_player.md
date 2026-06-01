---
id: game_theory.extensive_game.core.nature_player
title: Nature In Extensive Games
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Basic
  declarations:
    - ExtensiveGame.isChanceState
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - nature
  - chance
---

# Nature In Extensive Games

An extensive game with Nature has chance nodes at which no strategic player
chooses an action. Instead, the game description specifies a probability
distribution over successors. A strategy profile of the strategic players then
induces a probability distribution over terminal outcomes.

## References

- [MFoGT, Section 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nature or hazard player chooses successors according to specified probability distributions.
