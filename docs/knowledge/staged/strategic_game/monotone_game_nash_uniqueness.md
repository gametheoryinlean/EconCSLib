---
id: game_theory.strategic_game.continuous.monotone_game_nash_uniqueness
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Nash Characterization And Uniqueness In Monotone Games
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.continuous.first_order_nash_condition
  - game_theory.strategic_game.continuous.monotone_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - monotone-game
  - nash-equilibrium
---

# Nash Characterization And Uniqueness In Monotone Games

For a Hilbert smooth monotone game, a profile $s$ is a Nash equilibrium if and
only if
$$
  \sum_{i\in I}
  \langle \nabla_i g_i(t),\,s_i-t_i\rangle
  \ge 0
  \quad\text{for all }t\in S.
$$
If the game is strictly monotone, the Nash equilibrium is unique.

## Proof Sketch

The first-order Nash condition gives the inequality with $\nabla g(s)$. Monotonicity
transfers it to the inequality with $\nabla g(t)$. Conversely, testing only profiles
that deviate in one coordinate and using the mean value theorem recovers each
player's no-profitable-deviation condition. If two equilibria existed in a strictly
monotone game, applying the first-order condition in both directions would force a
nonnegative value for the monotonicity expression, contradicting strict negativity
unless the two profiles coincide.

## References

- [MFoGT, Thm. 4.7.10] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Variational characterization and uniqueness for monotone games.
