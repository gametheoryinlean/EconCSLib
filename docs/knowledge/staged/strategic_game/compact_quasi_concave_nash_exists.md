---
id: game_theory.strategic_game.continuous.compact_quasi_concave_nash_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Nash Existence In Compact Quasi-Concave Games
kind: theorem
status: staged
uses:
  - math.fixed_point.kakutani_fixed_point
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.continuous.quasi_concave_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - continuous-game
  - nash-equilibrium
  - existence
---

# Nash Existence In Compact Quasi-Concave Games

If $G$ is compact, continuous, and quasi-concave, then the set of Nash equilibria
is nonempty and compact.

## Proof Sketch

MFoGT uses the maximal-element formulation. For each potential deviation $t$,
let $A(t)$ be the compact set of profiles not dominated by $t$. A Nash equilibrium
is an element of $\bigcap_{t\in S}A(t)$. By compactness it suffices to prove the
finite intersection property. For finitely many deviations, restrict each player's
strategy set to the convex hull of their finitely many deviating strategies, obtain a
finite-dimensional compact convex game, and apply Kakutani's fixed point theorem
to the best-response correspondence.

## References

- [MFoGT, Thm. 4.7.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Compact continuous quasi-concave games have nonempty compact Nash set.
