---
id: math.fixed_point.kakutani_from_two_player_nash
title: Kakutani From Two-Player Nash Existence
kind: theorem
status: staged
primary_topic: game_theory.strategic_game.equilibrium
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
uses:
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
  - math.fixed_point.kakutani_fixed_point
verification:
  statement: accepted
  proof: gap
tags:
  - fixed-point
  - kakutani
  - nash-equilibrium
---

# Kakutani From Two-Player Nash Existence

The existence of Nash equilibria for all finite two-player games implies
Kakutani's fixed point theorem for upper semicontinuous compact-convex-valued
correspondences on compact convex subsets of Euclidean space.

MFoGT Exercise 4.12.6 constructs finite two-player games from finite families of
points $(x_i)$ and $(y_i)$, uses their Nash equilibria to generate approximate fixed
points, and then takes an accumulation point to obtain a fixed point of the
correspondence.

## References

- [MFoGT, Section 4.12, Exercise 6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. McLennan-Tourki derivation of Kakutani from finite two-player Nash equilibrium existence.
