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
    - EconCSLib.GameTheory.ExtensiveGame.Observed.Chance
  declarations:
    - ExtensiveGame.ObservedChanceGame
    - ExtensiveGame.ObservedChanceGame.withChanceKernel
    - ExtensiveGame.ObservedChanceGame.withChanceKernel_chanceKernel
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

An `ObservedChanceGame` has chance histories at which `mover = none`, so no
strategic player chooses the next action. Its `chanceKernel` explicitly assigns
a normalized `PMF` to the legal dependent action type at every such history.
Combining this fixed chance kernel with a strategic behavioral profile yields
the finite stopped-history and payoff laws developed by the execution layer.

The raw `ExtensiveGame.isChanceState` predicate identifies the mover-free
branch only; it does not itself contain a probability distribution.

## References

- [MFoGT, Section 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nature or hazard player chooses successors according to specified probability distributions.
