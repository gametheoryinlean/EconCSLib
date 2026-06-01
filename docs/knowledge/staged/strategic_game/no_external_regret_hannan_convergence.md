---
id: game_theory.strategic_game.zero_sum.learning.no_external_regret_hannan_convergence
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: No External Regret Converges To Hannan Set
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.hannan_set
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - learning
  - regret
  - convergence
---

# No External Regret Converges To Hannan Set

In repeated play of a finite game, if player $i$ follows a procedure with no
external regret, then the empirical distribution of realized action profiles
approaches player $i$'s Hannan set almost surely.

Equivalently, every limit point of the empirical distributions satisfies the
fixed-action hindsight inequalities defining the Hannan set for player $i$.

## Proof Sketch

The empirical distribution rewrites each fixed-action external regret as a
linear functional of the empirical distribution. No external regret says that
the positive part of each of these finitely many linear violations vanishes.
Therefore the distance to the intersection of the corresponding closed
halfspaces, namely the Hannan set, tends to zero.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Empirical distributions under no-external-regret procedures converge almost surely to the corresponding Hannan set.
