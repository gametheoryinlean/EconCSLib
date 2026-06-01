---
id: game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium
title: Subgame-Perfect Equilibrium In Perfect-Information Games
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.core.history_and_subgame
  - game_theory.strategic_game.nash_equilibrium
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
  declarations:
    - IsSubgamePerfect
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - subgame-perfect-equilibrium
---

# Subgame-Perfect Equilibrium In Perfect-Information Games

A strategy profile $\sigma$ is subgame-perfect if for every position $p$, the
continuation strategy profile $\sigma[p]$ induced by $\sigma$ is a Nash equilibrium
of the subgame $G[p]$.

This strengthens Nash equilibrium by requiring optimality after every possible
history, including histories not reached by the equilibrium play.

## References

- [MFoGT, Def. 6.2.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy profile is subgame-perfect if every continuation strategy is Nash in every subgame.
