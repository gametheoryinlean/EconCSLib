---
id: game_theory.extensive_game.equilibrium.reached_subgame_nash_restriction
title: Reached Subgame Nash Restriction
kind: theorem
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.imperfect_information.behavioral_equilibrium
  - game_theory.extensive_game.imperfect_information.reached_information_set
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
  - subgame-perfect-equilibrium
---

# Reached Subgame Nash Restriction

Let $\Gamma$ be an extensive-form game, let $\sigma^\ast$ be a Nash equilibrium
in mixed strategies or behavior strategies, and let $\Gamma(x)$ be a subgame.
If the probability of reaching $x$ under $\sigma^\ast$ is positive, then the
restriction of $\sigma^\ast$ to $\Gamma(x)$ is a Nash equilibrium of the subgame
$\Gamma(x)$.

## Lean Scope

This theorem is not currently implemented. The former state-indexed
`BehaviorStrategy` implementation was removed because it assigned zero
probability to chance actions and merged distinct history occurrences that
reached the same state.

A faithful replacement should use the history-indexed
`ObservedGame.BehavioralProfile` API, define reach probabilities from the
induced stochastic history policy, restrict and lift strategies at a
structurally lawful subgame root, and prove the payoff decomposition rather than
assuming it as an affine transfer interface. The existing bounded continuation
game forms and `IsBehavioralSubgamePerfectOnAtFuel` predicate provide the target
equilibrium vocabulary, but they do not yet prove this positive-reach
restriction theorem.

## References

- [MSZ, Thm. 7.5] Maschler, Solan, and Zamir, *Game Theory*. A Nash equilibrium restricted to a subgame reached with positive probability remains a Nash equilibrium of that subgame.
