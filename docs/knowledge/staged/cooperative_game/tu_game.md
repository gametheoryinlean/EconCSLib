---
id: game_theory.cooperative_game.tu_game
title: Transferable-Utility Coalitional Game
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Basic
  declarations:
    - CoalitionalGame
    - CoalitionalGame.coalitionPayoff
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - transferable-utility
  - characteristic-function
---

# Transferable-Utility Coalitional Game

A **transferable-utility coalitional game** consists of a finite player set
$N$ and a characteristic function
$$
  v : 2^N \to \mathbb{R}
$$
with $v(\varnothing)=0$. For each coalition $S \subseteq N$, the number
$v(S)$ is the total payoff that members of $S$ can secure by coordinating
among themselves.

For a payoff vector $x : N \to \mathbb{R}$, the payoff assigned to a
coalition is
$$
  x(S) = \sum_{i \in S} x_i.
$$
This derived coalition payoff is the quantity compared with $v(S)$ in
imputation, core, and balancedness conditions.

## Lean Status

The Lean structure `CoalitionalGame N U` is intentionally parameterized by
the utility type `U`; real-valued assumptions are introduced only for
theorems such as Bondareva-Shapley and Shapley-value results. The declaration
`CoalitionalGame.coalitionPayoff` supplies the finite sum
$\sum_{i \in S} x_i$.

## References

- [MSZ Ch.16, Def 16.1] Maschler, Solan, Zamir, *Game Theory*.
