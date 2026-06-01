---
id: game_theory.strategic_game.refinements.reny_solution_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Existence Of Reny Solutions
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.continuous.quasi_concave_game
  - game_theory.strategic_game.refinements.reny_solution
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - discontinuous-game
  - existence
---

# Existence Of Reny Solutions

Every compact quasi-concave game admits a Reny solution, and the set of Reny
solutions is compact.

## Proof Sketch

MFoGT rewrites existence as a finite-intersection problem over closed sets
$E(s)$ in the graph closure. For finitely many test profiles, it restricts to
finite-dimensional convex hulls and approximates lower semicontinuous payoff
regularizations from below by continuous functions. The resulting continuous
quasi-concave games have Nash equilibria. Compactness gives a convergent
subsequence whose limit satisfies the Reny inequalities.

## References

- [MFoGT, Thm. 4.8.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Any compact quasi-concave game admits a Reny solution.
