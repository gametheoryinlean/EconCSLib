---
id: game_theory.extensive_game.perfect_information.zermelo_determinacy
title: Zermelo Determinacy For Finite Perfect-Information Games
kind: theorem
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.determined_game
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Zermelo
  declarations:
    - zermelo_determinacy
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - extensive-game
  - determinacy
  - zermelo
---

# Zermelo Determinacy For Finite Perfect-Information Games

Every simple finite game with perfect information is determined.

## Proof Sketch

The proof is by induction on the length of the tree. Each successor of the origin
defines a shorter subgame. By the induction hypothesis, each such subgame is
determined and has value $+1$ or $-1$ according to which player can force a win.
The player who moves at the origin chooses a successor with the best value; if that
value is favorable, that player wins, otherwise the opponent's winning strategy in
each successor subgame wins.

## References

- [MFoGT, Thm. 6.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every simple finite game with perfect information is determined.
