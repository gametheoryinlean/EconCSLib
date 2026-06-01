---
id: game_theory.strategic_game.continuous.monotone_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Monotone Smooth Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.continuous.smooth_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - monotone-game
---

# Monotone Smooth Game

A Hilbert smooth game is monotone if, for all profiles $s,t\in S$,
$$
  \sum_{i\in I}
  \langle \nabla_i g_i(s)-\nabla_i g_i(t),\,s_i-t_i\rangle
  \le 0.
$$
It is strictly monotone if the inequality is strict whenever $s\ne t$.

## References

- [MFoGT, Def. 4.7.9] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Rosen monotonicity condition for Hilbert smooth games.
