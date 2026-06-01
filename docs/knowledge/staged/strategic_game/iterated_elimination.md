---
id: game_theory.strategic_game.dominance.iterated_elimination
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Iterated Elimination Of Strictly Dominated Strategies
kind: definition
status: staged
uses:
  - game_theory.strategic_game.dominance.dominated_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.IESDS
  declarations:
    - StrategicGame.Survives
    - StrategicGame.Survives.mono
    - StrategicGame.Survives.prev
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - dominance
  - rationality
---

# Iterated Elimination Of Strictly Dominated Strategies

Starting from a strategic game, remove all strictly dominated strategies. The
remaining strategy sets define a restricted game, in which new strategies may
become strictly dominated. Repeating this operation gives an iterated elimination
process.

A strategy survives to round $k$ if it has not been eliminated in the first $k$
rounds. The limiting survivor set is the set of strategies that survive all finite
rounds.

## References

- [MFoGT, Section 1.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Iterated elimination of strictly dominated strategies.
