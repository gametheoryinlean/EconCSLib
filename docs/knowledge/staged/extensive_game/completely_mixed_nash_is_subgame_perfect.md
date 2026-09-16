---
id: game_theory.extensive_game.equilibrium.completely_mixed_nash_is_subgame_perfect
title: Completely Mixed Nash Is Subgame Perfect
kind: theorem
status: staged
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
uses:
  - game_theory.extensive_game.equilibrium.reached_subgame_nash_restriction
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - behavioral-strategy
  - nash-equilibrium
  - subgame-perfect-equilibrium
  - completely-mixed
---

# Completely Mixed Nash Is Subgame Perfect

Let $\Gamma$ be a finite extensive-form game in which Nature assigns positive
probability to every legal chance action. If a completely mixed behavioral
profile is a Nash equilibrium, then it is a subgame-perfect equilibrium.

## Lean Scope

This theorem is not currently implemented. Complete mixing together with
full-support chance laws makes every finite history, hence every subgame root,
positively reachable. Reached-subgame Nash restriction then gives Nash
equilibrium in every structurally lawful subgame.

A Lean proof should be stated in the occurrence-sensitive observed-game layer,
using `ObservedGame.BehavioralProfile` and
`ObservedChanceGame.IsBehavioralStandardSubgamePerfectAtFuel` (or an eventual
unbounded terminating analogue). It must derive positive reach from the
finite-history product law and the full-support assumptions. The deleted
state-indexed implementation merely bundled positive reach and affine payoff
transfer as hypotheses, so it did not establish the advertised theorem.

## References

- [MSZ, Cor. 7.7] Maschler, Solan, and Zamir, *Game Theory*. A completely mixed Nash equilibrium is subgame-perfect.
