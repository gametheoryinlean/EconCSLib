---
id: game_theory.cooperative_game.balanced_game
title: Balanced Coalitional Game
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.balanced_collection
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
  declarations:
    - CoalitionalGame.IsBalancedGame
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - balancedness
  - bondareva-shapley
---

# Balanced Coalitional Game

A coalitional game is **balanced** if every balanced collection of
coalitions satisfies the weighted worth inequality
$$
  \sum_{S \in \mathcal{D}} \delta_S v(S) \le v(N),
$$
whenever the positive weights $\delta_S$ cover each player with total
weight one.

Intuitively, if a fractional schedule of coalitions uses each player once
in total, then the weighted value of that schedule cannot exceed the worth
of the grand coalition.

## References

- [MSZ Ch.17, Thm 17.14] Maschler, Solan, Zamir, *Game Theory*. Balancedness condition in the
  Bondareva-Shapley theorem.
