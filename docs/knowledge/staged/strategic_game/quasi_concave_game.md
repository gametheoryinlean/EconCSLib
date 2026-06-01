---
id: game_theory.strategic_game.continuous.quasi_concave_game
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Quasi-Concave Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - continuous-game
---

# Quasi-Concave Game

Assume each strategy set $S_i$ is a convex subset of a topological vector space. A
strategic game is quasi-concave if, for every player $i$ and every fixed
$s_{-i}$, the function
$$
  s_i\mapsto g_i(s_i,s_{-i})
$$
is quasi-concave on $S_i$.

## References

- [MFoGT, Def. 4.7.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Quasi-concavity in each player's own strategy variable.
