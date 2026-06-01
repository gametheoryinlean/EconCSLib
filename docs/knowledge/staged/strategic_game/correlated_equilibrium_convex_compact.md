---
id: game_theory.strategic_game.correlated.correlated_equilibrium_convex_compact
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Equilibrium Set Is Convex And Compact
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.correlated_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - correlated-equilibrium
  - convexity
  - compactness
---

# Correlated Equilibrium Set Is Convex And Compact

In a finite strategic-form game, the set of correlated equilibria is a convex
and compact subset of the simplex of probability distributions over pure
strategy profiles.

## Proof Sketch

The simplex of all distributions over pure profiles is compact and convex. The
obedience constraints are finitely many weak linear inequalities in the
probabilities $\mu(s)$. Therefore the correlated-equilibrium set is the
intersection of the simplex with finitely many closed halfspaces, hence is
closed, compact, and convex.

## References

- [MSZ, Chapter 8, Thm. 8.9] Maschler, Solan, and Zamir, *Game Theory*. The set of correlated equilibria is convex and compact.
