---
id: game_theory.extensive_game.imperfect_information.action_at_information_set
title: Action At An Information Set
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.information_set
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - information-set
  - action
lean:
  repository: econcslib
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation
  declarations:
    - FiniteImperfectGame.PureStrategy.actionAt
    - FiniteImperfectGame.actionAt_same_info_label
---

# Action At An Information Set

For an information set $P^i_k$, successors of nodes in $P^i_k$ are grouped into
equivalence classes representing the same physical action. The action set available
to player $i$ at $P^i_k$ is denoted
$$
  A_i(P^i_k).
$$
A strategy at imperfect information must choose an action in $A_i(P^i_k)$, not a
node-specific successor.

## References

- [MFoGT, Section 6.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Equivalence classes of successors are actions available at an information set.
