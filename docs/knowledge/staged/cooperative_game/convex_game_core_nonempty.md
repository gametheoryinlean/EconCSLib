---
id: game_theory.cooperative_game.convex_game_core_nonempty
title: Convex Games Have Nonempty Core
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.classes
uses:
  - game_theory.cooperative_game.convex_game
  - game_theory.cooperative_game.bondareva_shapley
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - coalitional-game
  - convex-game
  - core
---

# Convex Games Have Nonempty Core

**Theorem.** If a finite TU game is convex, then its core is nonempty.

## Proof Sketch

Convexity implies the balancedness inequalities required by
Bondareva-Shapley. Applying
[[game_theory.cooperative_game.bondareva_shapley]] then gives
nonemptiness of the core.

## Lean Status

The Lean module defines the relevant core and convex-game predicates. This
theorem remains a blueprint target depending on the Bondareva-Shapley route.

## References

- [MSZ Ch.17, Thm 17.55] Maschler, Solan, Zamir, *Game Theory*.
