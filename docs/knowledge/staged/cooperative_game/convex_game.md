---
id: game_theory.cooperative_game.convex_game
title: Convex Coalitional Game
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.classes
uses:
  - game_theory.cooperative_game.tu_game
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Basic
  declarations:
    - CoalitionalGame.IsConvex
    - CoalitionalGame.IsConvex.isSuperadditive
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - coalitional-game
  - convex-game
  - supermodularity
---

# Convex Coalitional Game

A coalitional game is **convex** when its characteristic function is
supermodular:
$$
  v(S \cup T) + v(S \cap T) \ge v(S) + v(T)
$$
for all coalitions $S,T \subseteq N$.

Equivalently, a player's marginal contribution weakly increases as the
coalition they join becomes larger. Convexity is a strong regularity
condition: convex games have nonempty core, and their Shapley value lies in
the core.

## Lean Status

Lean defines convexity as `CoalitionalGame.IsConvex` and proves the basic
fact `CoalitionalGame.IsConvex.isSuperadditive`.

## References

- [MSZ Ch.17, Def 17.51 and Thm 17.54] Maschler, Solan, Zamir,
  *Game Theory*.
