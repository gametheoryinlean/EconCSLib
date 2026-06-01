---
id: game_theory.cooperative_game.superadditive_game
title: Superadditive Coalitional Game
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
    - CoalitionalGame.IsSuperadditive
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - superadditivity
---

# Superadditive Coalitional Game

A coalitional game is **superadditive** if disjoint coalitions can do at
least as well by merging. Formally, for disjoint coalitions
$S,T \subseteq N$,
$$
  v(S \cup T) \ge v(S) + v(T).
$$

Superadditivity is a basic economic compatibility condition: it says there
is no loss of worth merely from allowing two non-overlapping coalitions to
coordinate as one larger coalition.

## References

- [MSZ Ch.16, Def 16.8] Maschler, Solan, Zamir, *Game Theory*.
