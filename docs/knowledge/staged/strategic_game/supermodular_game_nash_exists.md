---
id: game_theory.strategic_game.continuous.supermodular_game_nash_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Nash Existence In Supermodular Games
kind: theorem
status: staged
uses:
  - math.lattice.tarski_fixed_point
  - game_theory.strategic_game.continuous.supermodular_best_response_lattice
  - game_theory.strategic_game.nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - supermodular-game
  - nash-equilibrium
  - existence
---

# Nash Existence In Supermodular Games

Every supermodular game, in the sense of MFoGT Exercise 4.12.4, has a Nash
equilibrium.

The intended proof applies Tarski's fixed point theorem to a monotone selection
from the players' best-response correspondences.

## References

- [MFoGT, Section 4.12, Exercise 4(2c)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of Nash equilibrium in supermodular games.
