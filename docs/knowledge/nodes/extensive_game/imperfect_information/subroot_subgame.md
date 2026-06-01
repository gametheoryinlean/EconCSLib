---
id: game_theory.extensive_game.imperfect_information.subroot_subgame
title: Subroot And Subgame In Imperfect-Information Games
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.information_set
  - game_theory.extensive_game.core.history_and_subgame
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTree
  declarations:
    - GameTree.Subtree
    - GameTree.Subtree.self
    - GameTree.Subtree.head
    - GameTree.Subtree.tail_mem
    - GameTree.Subtree.child_mem
    - GameTree.Subtree.trans
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - subgame
  - imperfect-information
---

# Subroot And Subgame In Imperfect-Information Games

In a perfect-recall extensive game, a node $x$ is a subroot if:

1. $x$ is the unique node in its information set;
2. for every information set $Q$, either every node of $Q$ follows $x$, or no node
   of $Q$ follows $x$.

The followers of a subroot, together with inherited information sets and payoffs,
define a subgame.

## References

- [MFoGT, Def. 6.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Subroot definition for subgames in perfect-recall extensive games.
