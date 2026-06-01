---
id: game_theory.extensive_game.perfect_information.backward_induction_value
title: Backward Induction Value
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.core.game_tree
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.BackwardInduction
  declarations:
    - GameTree.value
    - GameTree.valueList
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - backward-induction
  - perfect-information
---

# Backward Induction Value

For a finite perfect-information game tree, the **backward-induction value** is
the payoff vector $\operatorname{value} : \texttt{GameTree} \to (\iota \to U)$
computed bottom-up:

- at a leaf, the value is its payoff vector;
- at a decision node with mover $m$, the value is that of the child the mover
  prefers, i.e. the child maximizing coordinate $m$.

The only structural requirement on the payoff type $U$ is a total preorder
(reflexivity, transitivity, totality); neither antisymmetry nor decidability is
used. The mover's own coordinate dominates every child's value
(`value_Node_ge`), and the chosen value is realized by some child
(`value_Node_eq_some_child_value`). This value function and its optimality
lemmas are the machinery behind Zermelo determinacy
([[node:game_theory.extensive_game.perfect_information.subgame_perfect_equilibrium]])
and Kuhn's subgame-perfect existence theorem.

## References

- [MSZ, Chapter 3] Maschler, Solan, and Zamir, *Game Theory*. Backward induction on finite perfect-information games.
