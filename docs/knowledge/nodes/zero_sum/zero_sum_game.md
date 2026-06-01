---
id: game_theory.strategic_game.zero_sum.zero_sum_game
title: Zero-Sum Game
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
  declarations:
    - StrategicGame.IsZeroSum
    - StrategicGame.IsConstantSum
    - StrategicGame.IsZeroSum.toIsConstantSum
    - StrategicGame.IsZeroSum.welfare_eq_zero
    - StrategicGame.IsConstantSum.welfare_eq
    - StrategicGame.IsConstantSum.zero_isZeroSum
    - StrategicGame.isZeroSum_iff_isConstantSum_zero
source:
  spans:
    - artifact: msz-game-theory
      locator: "Chapter 4, Section 4.4"
      format: section
      note: "Zero-sum and constant-sum two-player games"
    - artifact: mfogt
      locator: "Definition 2.2.1"
      format: section
      note: "Zero-sum strategic-form game as a triple (I, J, g)"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "What algebraic assumptions are needed for the zero-sum predicate?"
  verdict: "The predicate only needs addition and zero on payoffs; order is only needed for equilibrium comparison theorems."
tags:
  - zero-sum
  - strategic-game
  - foundational
---

# Zero-Sum Game

A two-player strategic game is zero-sum if, at every strategy profile $\sigma$,
the two players' payoffs add to zero:

$$u_0(\sigma) + u_1(\sigma) = 0.$$

A constant-sum game fixes the same sum to a constant $c$ instead of zero.  In a
zero-sum game, player 1's payoff is the negative of player 0's payoff, so the
game can be studied through a single payoff function.

## References

- [MSZ, Chapter 4, Section 4.4] Maschler, Solan, and Zamir, *Game Theory*. Zero-sum and constant-sum two-player games.
