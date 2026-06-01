---
id: game_theory.strategic_game.zero_sum.applications.strict_dominance_never_best_response
title: Strict Domination And Never Best Response (via auxiliary zero-sum game)
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.dominance.dominated_strategy
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - dominance
  - best-response
---

# Strict Domination And Never Best Response

In a finite strategic game, a mixed strategy $m_i\in\Delta(S_i)$ is strictly
dominated if and only if it is never a best response against any correlated
strategy of the opponents.

## Proof Sketch

If $m_i$ is strictly dominated by $\sigma_i$, linearity of expected payoff extends
the strict inequality to every correlated strategy of the opponents, so $m_i$
cannot be a best response.

Conversely, form the two-player zero-sum game in which player $i$ compares the
payoff of a pure action $t_i$ with the payoff of the fixed mixed strategy $m_i$.
The hypothesis that $m_i$ is never a best response implies that the auxiliary
zero-sum game has strictly positive value. An optimal strategy in that game then
strictly dominates $m_i$ in the original game.

## Why this lives under `zero_sum.applications`

This proposition is a strategic-game result, but the MFoGT proof route
is structural in [[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]: the
"$m_i$ is never a best response $\Rightarrow$ strictly dominated"
direction is established by constructing an auxiliary two-player
zero-sum game and extracting a dominating strategy from its
minimax-optimal strategy. Filing the node under `zero_sum.applications`
reflects the proof technique and keeps the top-level `strategic_games`
topic from depending back on `zero_sum`. A separation-theorem proof à
la Pearce 1984 is available as an alternative and would substitute a
Theorem-of-the-Alternative citation in `math.linear_algebra`; the
MFoGT route is chosen here for alignment with the rest of the library's
zero-sum infrastructure.

## References

- [MFoGT, Prop. 4.3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strict domination is equivalent to never being a best response against a correlated strategy.
