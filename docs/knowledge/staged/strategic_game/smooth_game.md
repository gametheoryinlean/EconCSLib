---
id: game_theory.strategic_game.continuous.smooth_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Smooth Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - smooth-game
---

# Smooth Game

For a game whose strategy sets are convex subsets of Hilbert spaces, the game is
smooth if, for every player $i$ and fixed $s_{-i}$, the map
$$
  s_i\mapsto g_i(s_i,s_{-i})
$$
is $C^1$. It is concave if these maps are concave.

## References

- [MFoGT, Def. 4.7.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Smooth and concave Hilbert games.
