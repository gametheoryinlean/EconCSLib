---
id: game_theory.extensive_game.perfect_information.zermelo_determinacy
title: Zermelo Saddle Determinacy For Rational Zero-Sum GameTrees
kind: theorem
status: proved
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
uses:
  - game_theory.extensive_game.perfect_information.backward_induction_value
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Zermelo
  declarations:
    - GameTree.zermelo_determinacy
    - GameTree.value₀_eq_outcome_and_zeroSum
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - extensive-game
  - determinacy
  - zermelo
---

# Zermelo Saddle Determinacy For Rational Zero-Sum GameTrees

For a finite `GameTree (Fin 2) ℚ` whose two payoff coordinates sum to zero at
every leaf, backward induction constructs a pure strategy profile and a
rational value `value₀ g` such that player 0 can secure at least that value
against every unilateral deviation and player 1 can hold player 0 to at most
that value. The backward-induction profile realizes the value, and player 1's
payoff is its negation.

## Proof Sketch

The proof is by structural backward induction. At player-0 nodes the selected
child maximizes coordinate zero. At player-1 nodes, zero-sum converts player
1's payoff maximization into minimization of coordinate zero. The resulting
profile supplies both saddle inequalities. The theorem is deliberately
narrower than the textbook winning-set formulation: it does not yet encode an
arbitrary simple win/lose game or a general strictly competitive outcome
order.

## References

- [MFoGT, Thm. 6.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every simple finite game with perfect information is determined.
