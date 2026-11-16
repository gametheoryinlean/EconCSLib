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
    - EconCSLib.GameTheory.ExtensiveGame.Observed.SPE
  declarations:
    - ExtensiveGame.ObservedGame.IsLawfulSubgameRoot
    - ExtensiveGame.ObservedGame.SubgameSystem
    - ExtensiveGame.ObservedGame.CompleteSubgameSystem
    - ExtensiveGame.ObservedGame.IsPureStandardSubgamePerfect
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

This strengthens Nash equilibrium by requiring optimality after every lawful
subgame root, including off-path roots. In Lean the root convention is an
explicit `ObservedGame.IsLawfulSubgameRoot`: the initial history is the whole
game, a proper player root has singleton decision information, and information
sets met after entry cannot cross the continuation boundary.
`CompleteSubgameSystem` certifies that every such root is exposed, and
`IsPureStandardSubgamePerfect` tests all of them. A designated-root predicate
or a possibly conservative `SubgameSystem` is therefore not sufficient by
itself for the standard claim.

## References

- [MFoGT, Def. 6.2.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy profile is subgame-perfect if every continuation strategy is Nash in every subgame.
