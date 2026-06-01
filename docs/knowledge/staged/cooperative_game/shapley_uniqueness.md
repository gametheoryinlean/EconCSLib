---
id: game_theory.cooperative_game.shapley_uniqueness
title: Shapley Uniqueness Theorem
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.shapley_value
  - game_theory.cooperative_game.shapley_axioms
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.ShapleyValue
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - coalitional-game
  - shapley-value
  - uniqueness
---

# Shapley Uniqueness Theorem

**Theorem.** The Shapley value is the unique single-valued solution concept
that satisfies efficiency, symmetry, the null-player property, and
additivity.

## Proof Sketch

The usual proof expands arbitrary games in a basis of unanimity games.
The four axioms determine the value uniquely on unanimity games: players in
the winning coalition receive equal shares and players outside it are null.
Additivity then extends the determination to every game.

## Lean Status

The Lean module defines the Shapley value and its axioms. Uniqueness remains a
blueprint target with the unanimity-game proof route.

## References

- [MSZ Ch.18, Thm 18.13 and Thm 18.15] Maschler, Solan, Zamir,
  *Game Theory*.
