---
id: game_theory.extensive_game.imperfect_information.imperfect_information_pure_strategy
title: Pure Strategy With Imperfect Information
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.action_at_information_set
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - imperfect-information
  - strategy
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation
  declarations:
    - FiniteImperfectGame.PureStrategy
    - FiniteImperfectGame.PureStrategyProfile
    - FiniteImperfectGame.PureStrategy.actionAt
---

# Pure Strategy With Imperfect Information

For player $i$ in an imperfect-information extensive game, a pure strategy is a
function assigning to every information set $P^i_k$ an action
$$
  a_i\in A_i(P^i_k).
$$
A pure strategy profile again induces a unique terminal outcome, so every finite
extensive game has an associated normal form.

## References

- [MFoGT, Section 6.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A pure strategy maps each information set to an available action.
