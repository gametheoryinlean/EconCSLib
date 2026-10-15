---
id: game_theory.strategic_game.zero_sum.learning.hannan_zero_sum_intersection
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Two Hannan Conditions Identify the Zero-Sum Value
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.hannan_set
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.EmpiricalDistribution
  declarations:
    - StrategicGame.jointFirstMarginal
    - StrategicGame.jointSecondMarginal
    - StrategicGame.ColumnHannanSet
    - StrategicGame.hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - hannan-set
  - optimal-strategy
  - value
---

# Two Hannan Conditions Identify the Zero-Sum Value

Let $z$ be a possibly correlated distribution over the row and column actions
of a finite zero-sum matrix game. If $z$ satisfies the Hannan inequalities of
both players, then its row and column marginals are optimal strategies.
Moreover, the product-marginal payoff, the correlated payoff under $z$, and
the value of the game are all equal.

No independence assumption on $z$ is made. This is the zero-sum consequence
stated immediately after MFoGT's Hannan-convergence proposition.

## References

- [MFoGT, discussion after Proposition 7.3.13] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Intersection of both players' Hannan sets in a zero-sum game.
