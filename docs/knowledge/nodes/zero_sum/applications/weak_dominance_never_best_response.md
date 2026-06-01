---
id: game_theory.strategic_game.zero_sum.applications.weak_dominance_never_best_response
title: Weak Domination And Completely Mixed Tests (via auxiliary zero-sum game)
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.dominance.dominated_strategy
  - game_theory.strategic_game.zero_sum.core.support_complementarity
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - dominance
  - best-response
---

# Weak Domination And Completely Mixed Tests

In a finite strategic game, a mixed strategy $m_i\in\Delta(S_i)$ is weakly
dominated if and only if it is never a best response against a completely
correlated strategy of the opponents.

Here "completely correlated" means a correlated strategy in the relative interior
of $\Delta(S_{-i})$, assigning positive probability to every opponent profile.

## Proof Sketch

Weak domination gives a strict expected-payoff improvement against every
full-support correlated opponent strategy, so $m_i$ is not a best response to any
of them. For the converse, MFoGT reduces to an auxiliary finite zero-sum game. If
the value is positive then strict domination follows. If the value is zero, optimal
support and best-response complementarity identify an opponent pure profile
against which an optimal strategy gives a strict improvement while never lowering
the payoff elsewhere.

## Why this lives under `zero_sum.applications`

This proposition is a strategic-game result, but the MFoGT 4.3.6 proof
route is structural in [[node:game_theory.strategic_game.zero_sum.core.support_complementarity]]:
the converse uses both the value of the auxiliary zero-sum game and
support/best-response complementarity to extract a separating opponent
profile. Filing the node under `zero_sum.applications` reflects the
proof technique and keeps the top-level `strategic_games` topic from
depending back on `zero_sum`. A separation-theorem proof à la Pearce
1984, which would let the result live under
`strategic_games.dominance` while citing only
`math.linear_algebra.theorem_of_alternative`, is an alternative route.

## References

- [MFoGT, Prop. 4.3.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Weak domination is equivalent to never being a best response against a completely correlated strategy.
