---
id: game_theory.strategic_game.correlated.correlated_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.correlated.obedience_condition
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - correlated-equilibrium
---

# Correlated Equilibrium

A correlated equilibrium of a finite strategic-form game is a probability
distribution $\mu$ over pure strategy profiles such that the obedient
recommendation strategy is an equilibrium of the mediated game.

Equivalently, $\mu$ satisfies the obedience inequalities for every player, every
recommended action, and every unilateral replacement action.

This is different from an independent mixed profile: the distribution $\mu$ may
correlate the players' recommendations.

## References

- [MSZ, Chapter 8, Def. 8.6] Maschler, Solan, and Zamir, *Game Theory*. Correlated equilibrium as a distribution satisfying all obedience inequalities.
- [MFoGT, Chapter 7, Section 7.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Aumann correlated equilibrium in the chapter on correlated equilibria, learning, and Bayesian equilibria.
