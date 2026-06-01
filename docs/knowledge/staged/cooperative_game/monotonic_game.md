---
id: game_theory.cooperative_game.monotonic_game
title: Monotonic Coalitional Game
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
    - CoalitionalGame.IsMonotonic
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - monotonicity
---

# Monotonic Coalitional Game

A coalitional game is **monotonic** if enlarging a coalition cannot reduce
its worth. For coalitions $S \subseteq T \subseteq N$,
$$
  v(S) \le v(T).
$$

This property is weaker than superadditivity in many standard settings but
captures the same basic direction: adding players should not make a
coalition worse off.

## References

- [MSZ Ch.16, Def 16.10] Maschler, Solan, Zamir, *Game Theory*.
