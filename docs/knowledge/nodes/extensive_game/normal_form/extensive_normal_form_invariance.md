---
id: game_theory.extensive_game.normal_form.extensive_normal_form_invariance
title: Normal Form Invariance Of Extensive Representations
kind: proposition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.normal_form
uses:
  - game_theory.extensive_game.imperfect_information.imperfect_information_pure_strategy
  - game_theory.extensive_game.normal_form.normal_form_reduction
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
  declarations:
    - GameTree.toStrategicGame_nash_iff_isNashAt
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - extensive-game
  - normal-form
  - invariance
---

# Normal Form Invariance Of Extensive Representations

Two extensive forms can have the same normal form even when their trees and
information sets look different. MFoGT records that extensive forms with the same
normal form can be linked by chains of elementary transformations: interchange of
simultaneous moves, coalescing of consecutive moves, and addition of superfluous
moves.

## Proof Sketch

The statement is structural rather than an equilibrium theorem. Each elementary
transformation preserves the pure strategy sets up to canonical identification and
preserves the outcome induced by every strategy profile. Chains of these moves
therefore preserve the normal form.

## References

- [MFoGT, Section 6.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Extensive forms with the same normal form are related by elementary transformations.
