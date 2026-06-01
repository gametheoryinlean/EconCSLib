---
id: game_theory.cooperative_game.shapley_in_core_convex
title: Shapley Value Lies In The Core Of A Convex Game
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.shapley_value
  - game_theory.cooperative_game.convex_game
  - game_theory.cooperative_game.core
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
  - convex-game
  - core
---

# Shapley Value Lies In The Core Of A Convex Game

**Theorem.** If a TU game is convex, then its Shapley value belongs to the
core.

Convexity means marginal contributions are increasing with coalition size.
This increasing-marginal-returns property makes the Shapley average satisfy
every coalitional rationality inequality:
$$
  \sum_{i \in S}\operatorname{Sh}_i(v) \ge v(S)
  \quad\text{for every } S \subseteq N.
$$
Together with Shapley efficiency, this places the Shapley payoff vector in
the core.

## Lean Status

The Lean module defines the Shapley value and core predicates. This theorem
remains a blueprint target.

## References

- [MSZ Ch.18, Thm 18.32] Maschler, Solan, Zamir, *Game Theory*.
