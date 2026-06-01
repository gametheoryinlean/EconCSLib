---
id: game_theory.strategic_game.correlated.correlated_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Equilibrium Exists In Finite Games
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.nash_induces_correlated_equilibrium
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - correlated-equilibrium
  - existence
---

# Correlated Equilibrium Exists In Finite Games

Every finite strategic-form game has at least one correlated equilibrium.

## Proof Sketch

By Nash's theorem, every finite strategic-form game has a mixed Nash
equilibrium. Thm. 8.7 turns that mixed Nash equilibrium into a correlated
equilibrium by using the induced product distribution on pure strategy profiles.

## References

- [MSZ, Chapter 8, Cor. 8.8] Maschler, Solan, and Zamir, *Game Theory*. Every finite strategic-form game has a correlated equilibrium.
