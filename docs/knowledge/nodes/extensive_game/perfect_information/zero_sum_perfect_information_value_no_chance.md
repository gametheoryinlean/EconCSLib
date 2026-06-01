---
id: game_theory.extensive_game.perfect_information.zero_sum_perfect_information_value_no_chance
title: Value In Finite Zero-Sum Perfect-Information Games (No-Chance)
kind: theorem
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Zermelo
  declarations:
    - GameTree.zermelo_determinacy
    - GameTree.value₀_eq_outcome_and_zeroSum
verification:
  statement: accepted
  proof: gap
  alignment: aligned
tags:
  - extensive-game
  - zero-sum
  - value
---

# Value In Finite Zero-Sum Perfect-Information Games (No-Chance)

Every finite zero-sum perfect-information game **without chance moves** has a
value, and both players have pure optimal strategies. On `GameTree (Fin 2) ℚ`
satisfying `IsZeroSum`, the player-0 root value (obtained via backward
induction) coincides with the max-min / min-max value, and player-1's value is
its negation.

## Proof Sketch

Backward induction over the tree. If player 1 moves at a node, the value there
is the maximum over successor values; if player 2 moves, the minimum. Leaves
contribute their payoff directly. Optimal pure strategies are obtained by
choosing an optimal successor at each own-move node and then following optimal
strategies in the selected subgame.

The Lean theorem `zermelo_determinacy` makes the value/optimality precise:
playing `optStrategy`, player 0 secures at least `value₀ g` and player 1 holds
player 0 to at most `value₀ g`, so `value₀ g` is the (max-min = min-max) value
attained by a pure strategy on both sides. The packaging lemma
`value₀_eq_outcome_and_zeroSum` records that `optStrategy` realizes `value₀ g`
and that the value vector is zero-sum (`value g 1 = -value₀ g`).

## Scope

This is the no-chance specialization of the MFoGT proposition cited below
(stated there in "with or without Nature" form). The variant with chance /
Nature nodes lives at [[zero_sum_perfect_information_value_with_chance]] and is
gated on [EG-L3 / #181](https://github.com/gametheoryinlean/EconCSLib/issues/181).

## References

- [MFoGT, Prop. 6.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Stated in the more general with-or-without-Nature form.
- [Zermelo 1913] *Über eine Anwendung der Mengenlehre auf die Theorie des Schachspiels*.
