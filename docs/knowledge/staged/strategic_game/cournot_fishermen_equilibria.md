---
id: game_theory.strategic_game.continuous.cournot_fishermen_equilibria
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Cournot Fishermen Equilibria
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - cournot
  - nash-equilibrium
---

# Cournot Fishermen Equilibria

In the $n$-fishermen Cournot game, player $i$ chooses $x_i\ge 0$, total output is
$X=\sum_i x_i$, unit price is
$$
  p=\max\{1-X,0\},
$$
and player $i$ maximizes revenue $x_i p$.

The pure Nash equilibria are exactly:

1. the symmetric Cournot profile
   $$
     x_i=\frac1{n+1}\quad\text{for every }i;
   $$
2. the overproduction profiles satisfying
   $$
     \sum_{j\ne i}x_j\ge 1\quad\text{for every }i.
   $$

## References

- [MFoGT, Section 4.12, Exercise 2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Cournot competition among n fishermen with zero production cost.
