---
id: game_theory.cooperative_game.imputation
title: Imputation
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.payoff_vector
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Basic
  declarations:
    - CoalitionalGame.IsEfficient
    - CoalitionalGame.IsIndividuallyRational
    - CoalitionalGame.IsImputation
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - imputation
  - efficiency
  - individual-rationality
---

# Imputation

An **imputation** is a payoff vector that distributes all worth of the grand
coalition and gives every player at least their singleton worth.

For a TU game $(N,v)$, a payoff vector $x : N \to \mathbb{R}$ is an
imputation when:
$$
  \sum_{i \in N} x_i = v(N)
$$
and, for every player $i \in N$,
$$
  x_i \ge v(\{i\}).
$$

The first condition is **efficiency**; the second is **individual
rationality**.

## Lean Status

Lean separates the two predicates as `CoalitionalGame.IsEfficient` and
`CoalitionalGame.IsIndividuallyRational`, then combines them in
`CoalitionalGame.IsImputation`.

## References

- [MSZ Ch.17, Def 17.1] Maschler, Solan, Zamir, *Game Theory*.
