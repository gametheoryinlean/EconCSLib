---
id: game_theory.strategic_game.zero_sum.core.saddle_point
title: Saddle Point
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.mixed_extension
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.IsSaddlePoint
    - MatrixGame.IsMixedNashEq
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(d)"
      format: section
      note: "Saddle point inequality for matrix games"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - saddle-point
  - equilibrium
---

# Saddle Point

A pair of mixed strategies $(x^*,y^*)$ is a saddle point of a matrix game $A$
if for all $x \in \Delta(I)$ and $y \in \Delta(J)$,
$$
  x A y^* \le x^* A y^* \le x^* A y.
$$

For a zero-sum two-player matrix game, the saddle point predicate is
synonymous with the mixed Nash equilibrium predicate
[[node:game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium]] — the Lean development
defines `MatrixGame.IsSaddlePoint` as an `abbrev` for
`MatrixGame.IsMixedNashEq`.

## References

- [MFoGT, Prop. 2.4.1(d)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Saddle point inequality for matrix games.
