---
id: game_theory.cooperative_game.simple_game
title: Simple Game
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
    - CoalitionalGame.IsSimple
    - CoalitionalGame.IsWinning
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - simple-game
  - voting
---

# Simple Game

A **simple game** is a coalitional game whose coalitions are classified as
losing or winning. In characteristic-function form,
$$
  v(S) \in \{0,1\}
$$
for every coalition $S \subseteq N$, and the grand coalition is winning:
$$
  v(N)=1.
$$

A coalition $S$ is **winning** when $v(S)=1$.

Simple games model yes/no collective decision rules. Later refinements such
as weighted majority games add an explicit quota-and-weight representation.

## References

- [MSZ Ch.16, Def 16.2] Maschler, Solan, Zamir, *Game Theory*.
