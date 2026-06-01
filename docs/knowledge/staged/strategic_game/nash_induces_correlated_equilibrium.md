---
id: game_theory.strategic_game.correlated.nash_induces_correlated_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Nash Equilibrium Induces Correlated Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.correlated_equilibrium
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - correlated-equilibrium
  - nash-equilibrium
---

# Nash Equilibrium Induces Correlated Equilibrium

Every mixed Nash equilibrium induces a correlated equilibrium by taking the
product distribution over pure strategy profiles.

## Proof Sketch

Under the product distribution induced by a mixed Nash equilibrium, a player's
conditional belief after a recommendation is consistent with the opponents'
mixed strategies. Since the player's mixed strategy is a best response, every
pure action used with positive probability is optimal against that conditional
distribution. Therefore obeying each recommendation satisfies the obedience
inequalities.

## References

- [MSZ, Chapter 8, Thm. 8.7] Maschler, Solan, and Zamir, *Game Theory*. Every Nash equilibrium induces a correlated equilibrium.
