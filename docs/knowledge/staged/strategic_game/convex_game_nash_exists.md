---
id: game_theory.strategic_game.continuous.convex_game_nash_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Nash Existence In Convex Games
kind: theorem
status: staged
uses:
  - math.fixed_point.brouwer_compact_convex
  - game_theory.strategic_game.continuous.convex_game_variational_characterization
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - convex-game
  - nash-equilibrium
  - existence
---

# Nash Existence In Convex Games

Every convex game in the sense of MFoGT Exercise 4.12.7 has a Nash equilibrium.

The exercise proves this by contradiction: if no $t$ satisfies the variational
characterization, a finite open cover and a partition-of-unity construction produce
a continuous self-map of the compact convex strategy space. Brouwer's theorem
gives a fixed point, contradicting the construction.

## References

- [MFoGT, Section 4.12, Exercise 7(2)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of equilibrium in convex games.
