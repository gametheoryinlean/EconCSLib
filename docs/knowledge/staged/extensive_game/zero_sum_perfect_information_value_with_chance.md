---
id: game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_with_chance
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Value In Finite Zero-Sum Perfect-Information Games (With Chance)
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_no_chance
  - game_theory.extensive_game.core.nature_player
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance
  declarations:
    - ZeroSumChance.GameTree
    - ZeroSumChance.GameTree.value
    - ZeroSumChance.GameTree.DStrategy
    - ZeroSumChance.GameTree.outcome
    - ZeroSumChance.GameTree.value_prop
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - extensive-game
  - zero-sum
  - value
  - chance
---

# Value In Finite Zero-Sum Perfect-Information Games (With Chance)

Every finite zero-sum perfect-information game **with Nature / chance moves**
has a value, and both players have pure optimal strategies. At a chance node,
the value equals the probability-weighted average of the successor subgame
values.

## Proof Sketch

Same forward / backward induction as
[[zero_sum_perfect_information_value_no_chance]], with one extra case: at a
Nature node the value is the probability-weighted expectation over the
successor values. The minimax / maximin equality at player nodes is unaffected
because expectation is linear and player choice still optimizes over a finite
set.

## Lean status

Implemented in `EconCSLib.ExtensiveGame.ZeroSumGameTreeWithChance` (EG-L6, #220).
The key declarations are:

- `ZeroSumChance.GameTree` — binary game tree with `Leaf`, `Pnode`, `Nnode`.
- `ZeroSumChance.GameTree.value` — backward-induction value (computable).
- `ZeroSumChance.GameTree.DStrategy` — A's dominant strategy.
- `ZeroSumChance.GameTree.outcome` — payoff under a strategy pair.
- `ZeroSumChance.GameTree.value_prop` — `t.value ≤ t.outcome DStrategy SB`.

The ℚ-valued port requires no vNM theorem; rational arithmetic handles chance
averaging directly. The fully general n-player + arbitrary utility version
remains in `EconCSLib.ExtensiveGame.StochasticGameTree` and is blocked on
vNM (EG-L3 #181).

## References

- [MFoGT, Prop. 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Original "with or without Nature" form.
