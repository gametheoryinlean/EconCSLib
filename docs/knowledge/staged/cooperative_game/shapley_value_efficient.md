---
id: game_theory.cooperative_game.shapley_value_efficient
title: Shapley Value Is Efficient
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.shapley_value
  - game_theory.cooperative_game.shapley_axioms
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.ShapleyValue
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - coalitional-game
  - shapley-value
  - efficiency
---

# Shapley Value Is Efficient

**Theorem.** The Shapley value distributes the worth of the grand coalition:
$$
  \sum_{i \in N} \operatorname{Sh}_i(v)=v(N).
$$

## Proof Sketch

Expand the Shapley formula and exchange the sums over players and predecessor
coalitions. Each coalition marginal contribution appears with the number of
orders in which it is the relevant predecessor set. The resulting telescoping
over permutations leaves exactly $v(N)-v(\varnothing)=v(N)$.

## Lean Status

The Lean module defines the Shapley value. Efficiency remains a blueprint
target with a combinatorial proof route.

## References

- [MSZ Ch.18, Thm 18.18] Maschler, Solan, Zamir, *Game Theory*.
