---
id: game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_with_chance
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Value In Binary Rational Zero-Sum Games With Chance
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
    - ZeroSumChance.GameTree.MinStrategy
    - ZeroSumChance.GameTree.outcome
    - ZeroSumChance.GameTree.value_prop
    - ZeroSumChance.GameTree.outcome_MinStrategy_le_value
    - ZeroSumChance.GameTree.saddle_bounds
    - ZeroSumChance.GameTree.saddle_value
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

# Value In Binary Rational Zero-Sum Games With Chance

Every finite binary two-player zero-sum perfect-information tree with rational
terminal payoffs and rational Nature probabilities has a value, and both
players have pure optimal strategies. At a chance node, the value equals the
probability-weighted average of the two successor values.

## Proof Sketch

The proof is the same backward induction as
[[zero_sum_perfect_information_value_no_chance]], with one extra case: at a
Nature node the value is the probability-weighted expectation over the
successor values. The minimax / maximin equality at player nodes is unaffected
because expectation is linear and player choice optimizes over two successors.

## Lean status

Implemented in
`EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance`. The key
declarations are:

- `ZeroSumChance.GameTree` — binary game tree with `Leaf`, `Pnode`, `Nnode`.
- `ZeroSumChance.GameTree.value` — backward-induction value (computable).
- `ZeroSumChance.GameTree.DStrategy` — A's maximin strategy.
- `ZeroSumChance.GameTree.MinStrategy` — B's minimax strategy.
- `ZeroSumChance.GameTree.outcome` — payoff under a strategy pair.
- `ZeroSumChance.GameTree.value_prop` — `t.value ≤ t.outcome DStrategy SB`.
- `ZeroSumChance.GameTree.outcome_MinStrategy_le_value` —
  `t.outcome SA MinStrategy ≤ t.value`.
- `ZeroSumChance.GameTree.saddle_value` — the canonical pair realizes
  `t.value` exactly.

The ℚ-valued port uses rational arithmetic for chance averaging. The separate
n-player real-payoff `StochasticGameTree` supplies normalized chance laws and
finite-horizon evaluation, but its general equilibrium-existence theorem
remains a proof gap.

This formalized result is the binary rational specialization of the broader
finite-tree proposition in the reference below; no claim is made here that the
current Lean declaration already covers arbitrary finite branching or
irrational chance probabilities.

## References

- [MFoGT, Prop. 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Original "with or without Nature" form.
