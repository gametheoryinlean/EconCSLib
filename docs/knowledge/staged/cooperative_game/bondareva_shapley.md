---
id: game_theory.cooperative_game.bondareva_shapley
title: Bondareva-Shapley Theorem
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.shapley_value
uses:
  - game_theory.cooperative_game.core
  - game_theory.cooperative_game.balanced_game
  - math.linear_programming.strong_duality
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
verification:
  statement: accepted
  proof: gap
  alignment: pending
tags:
  - coalitional-game
  - core
  - balancedness
  - bondareva-shapley
---

# Bondareva-Shapley Theorem

**Theorem.** A finite transferable-utility coalitional game has nonempty
core if and only if it is balanced:
$$
  \operatorname{Core}(v) \ne \varnothing
  \quad\Longleftrightarrow\quad
  v \text{ is balanced}.
$$

## Proof Route

The standard proof is a theorem-of-the-alternative or linear-programming
duality argument. Core nonemptiness is feasibility of the linear system
consisting of efficiency and the coalition inequalities
$$
  \sum_{i \in S} x_i \ge v(S).
$$
The dual certificates for infeasibility are exactly balanced collections
whose weighted worth exceeds $v(N)$. Therefore no such certificate exists
precisely when all balanced collections satisfy the balanced-game
inequality.

## Lean Status

The Lean module defines the core and balanced-game predicates. This theorem
remains a blueprint target with an LP-duality proof route.

## References

- [MSZ Ch.17, Thm 17.14 and Thm 17.19] Maschler, Solan, Zamir,
  *Game Theory*.
