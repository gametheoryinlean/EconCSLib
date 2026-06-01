---
id: game_theory.strategic_game.continuous.supermodular_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Supermodular Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - supermodular-game
  - lattice
---

# Supermodular Game

A strategic game $G=(I,(S_i),(g_i))$ is supermodular if each $S_i$ is a compact
nonempty lattice in some Euclidean space, each $g_i$ is upper semicontinuous in
$s_i$, and:

1. $g_i$ has increasing differences: for $s_i\ge s'_i$ and
   $s_{-i}\ge s'_{-i}$,
   $$
     g_i(s_i,s_{-i})-g_i(s'_i,s_{-i})
     \ge
     g_i(s_i,s'_{-i})-g_i(s'_i,s'_{-i});
   $$
2. $g_i$ is supermodular in $s_i$: for every fixed $s_{-i}$,
   $$
     g_i(s_i,s_{-i})+g_i(s'_i,s_{-i})
     \le
     g_i(s_i\vee s'_i,s_{-i})+g_i(s_i\wedge s'_i,s_{-i}).
   $$

## References

- [MFoGT, Section 4.12, Exercise 4(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Topkis supermodular games.
