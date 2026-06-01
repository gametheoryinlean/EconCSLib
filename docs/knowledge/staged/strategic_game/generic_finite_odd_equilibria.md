---
id: game_theory.strategic_game.manifold.generic_finite_odd_equilibria
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Generic Finite Odd Equilibria
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.manifold.kohlberg_mertens_structure_theorem
  - game_theory.strategic_game.manifold.essential_component
  - game_theory.strategic_game.equilibrium.mixed_nash_semialgebraic
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-manifold
  - genericity
---

# Generic Finite Odd Equilibria

For finite games with fixed player and action sets:

1. generically, the mixed Nash equilibrium set is finite and has odd
   cardinality;
2. every game has at least one essential component of Nash equilibria.

MFoGT derives both facts from the degree-theoretic consequences of the
Kohlberg-Mertens structure theorem.

## References

- [MFoGT, Chapter 5, Prop. 5.3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Generic oddness and existence of an essential component.
