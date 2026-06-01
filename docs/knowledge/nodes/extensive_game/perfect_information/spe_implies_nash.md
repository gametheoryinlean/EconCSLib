---
id: game_theory.extensive_game.perfect_information.spe_implies_nash
title: Subgame-Perfect Equilibrium Implies Nash Equilibrium
kind: proposition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
  declarations:
    - IsSubgamePerfect.toNE
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - extensive-game
  - subgame-perfect-equilibrium
  - nash-equilibrium
---

# Subgame-Perfect Equilibrium Implies Nash Equilibrium

In a perfect-information game, every subgame-perfect equilibrium is a Nash
equilibrium of the whole game.

## Proof Sketch

The whole game is the subgame rooted at the origin. Since subgame perfection
requires the continuation profile to be Nash in every subgame, applying the
definition at the origin gives the Nash condition for the original game.

## References

- [MFoGT, Def. 6.2.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. SPE requires Nash equilibrium in every subgame, including the whole game at the origin.
