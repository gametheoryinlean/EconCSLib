---
id: game_theory.extensive_game.imperfect_information.imperfect_information_extensive_game
title: Extensive Game With Imperfect Information
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.perfect_information.perfect_information_extensive_game
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - imperfect-information
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation
  declarations:
    - FiniteImperfectGame
    - FiniteImperfectGame.SameMoverOnInfo
    - FiniteImperfectGame.SameActionsOnInfo
    - FiniteImperfectGame.NoChanceOnDecisionInfo
    - FiniteImperfectGame.InfoWellFormed
---

# Extensive Game With Imperfect Information

An extensive game with imperfect information keeps the tree, player assignments,
and terminal payoffs of an extensive form, but also records what each player knows
when making a move. This is represented by information sets that group decision
nodes a player cannot distinguish.

## References

- [MFoGT, Section 6.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Imperfect information extends the extensive form model by adding information sets.
