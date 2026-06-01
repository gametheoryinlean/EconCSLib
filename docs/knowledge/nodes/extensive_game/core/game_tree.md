---
id: game_theory.extensive_game.core.game_tree
title: Game Tree
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTree
  declarations:
    - GameTree
    - GameTree.children
    - GameTree.size
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - game-tree
---

# Game Tree

The tree of a finite perfect-information extensive game is a finite connected
directed acyclic graph with a distinguished origin $\theta$. Every non-origin node
has a unique predecessor, and iterating predecessors eventually reaches $\theta$.

Terminal nodes are those with no successors. Decision positions are nonterminal
nodes. Each decision position has a nonempty successor set.

## References

- [MFoGT, Section 6.2.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Tree of nodes, origin, predecessor map, terminal nodes, and successors.
