---
id: game_theory.extensive_game.perfect_information.perfect_information_strategy
title: Strategy In A Perfect-Information Game
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
    - EconCSLib.GameTheory.ExtensiveGame.Strategy
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
  declarations:
    - ExtensiveGame.Strategy
    - GameTree.Strategy
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - strategy
---

# Strategy In A Perfect-Information Game

For a player $i$, a pure strategy is a function on $P_i$ that assigns to each
position $p\in P_i$ a successor in $S(p)$. Thus a strategy specifies what the
player would do at every position where that player might move, including
positions that are not reached by the realized play.

## References

- [MFoGT, Section 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy selects a successor at each position controlled by the player.
