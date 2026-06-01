---
id: game_theory.strategic_game.equilibrium.mixed_nash_semialgebraic
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Semi-Algebraic Mixed Nash Set
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - nash-equilibrium
  - semi-algebraic
---

# Semi-Algebraic Mixed Nash Set

For a finite strategic game, the set of mixed Nash equilibria is defined by
finitely many polynomial weak inequalities. Consequently, the Nash equilibrium
set has finitely many connected components, each a closed semi-algebraic set.

## Proof Sketch

The simplex constraints are polynomial equalities and inequalities. Because
expected payoffs are multilinear in mixed strategy coordinates, the condition that
no pure deviation improves player $i$'s payoff is a finite family of polynomial
weak inequalities. This realizes the mixed Nash set as semi-algebraic. The finite
connected-component statement follows from the general theorem that closed
semi-algebraic subsets of Euclidean space have finitely many connected components.

## References

- [MFoGT, Prop. 4.9.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed Nash equilibria of a finite game are defined by finitely many polynomial weak inequalities.
- [MFoGT, Cor. 4.9.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite games have finitely many semi-algebraic Nash components.
