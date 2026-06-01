---
id: game_theory.strategic_game.continuous.convex_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Convex Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - convex-game
---

# Convex Game

A convex game has strategy sets $S_i$ and payoff functions $G_i$ satisfying:

1. each $S_i$ is a compact convex subset of a Euclidean space;
2. $G_i(\cdot,s_{-i})$ is concave on $S_i$ for every $s_{-i}$;
3. $\sum_i G_i$ is continuous on $S=\prod_i S_i$;
4. $G_i(s_i,\cdot)$ is continuous on $S_{-i}$ for every $s_i$.

## References

- [MFoGT, Section 4.12, Exercise 7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Convex games in the sense of the exercise.
