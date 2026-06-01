---
id: game_theory.strategic_game.bayesian.finite_bayesian_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Finite Bayesian Equilibrium Exists
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.bayesian.bayesian_equilibrium_as_nash
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - bayesian-game
  - bayesian-equilibrium
  - existence
---

# Finite Bayesian Equilibrium Exists

Every finite Bayesian game with finite action sets, finite type sets, and a
common prior has a mixed Bayesian equilibrium.

## Proof Sketch

Construct the finite agent normal form of the Bayesian game. Nash's theorem
gives a mixed Nash equilibrium of that finite strategic-form game. By the
Bayesian-equilibrium-as-Nash correspondence, the same type-contingent mixed
profile is a Bayesian equilibrium of the original Bayesian game.

## References

- [MFoGT, Chapter 7, Section 7.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of Bayesian equilibrium for finite Bayesian games via the finite Nash theorem.
