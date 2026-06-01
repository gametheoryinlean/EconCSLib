---
id: game_theory.strategic_game.refinements.proper_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Existence Of Proper Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.refinements.proper_equilibrium
  - math.fixed_point.kakutani_fixed_point
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-refinement
  - existence
---

# Existence Of Proper Equilibrium

Every finite normal-form game has at least one proper equilibrium. Every proper
equilibrium is perfect, and hence every proper equilibrium is a Nash equilibrium.

## Proof Sketch

For a fixed $\epsilon\in(0,1)$, restrict each player's mixed simplex to strategies
that put at least a small lower bound $\eta_i$ on each pure strategy. Define a
correspondence $F$ that keeps only mixed strategies whose probabilities respect
the $\epsilon$-proper ordering condition.

The exercise constructs a nonempty, convex-valued, closed-graph correspondence
on a compact convex product of truncated simplices. Kakutani gives a fixed point,
which is an $\epsilon$-proper profile. Compactness then gives a limit as
$\epsilon\to 0$.

## References

- [MFoGT, Thm. 6.5.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every finite normal-form game has a proper equilibrium.
- [MFoGT, Exercise 6.8.3 and Hints for Chapter 6, Exercise 3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Kakutani construction of epsilon-proper equilibria.
