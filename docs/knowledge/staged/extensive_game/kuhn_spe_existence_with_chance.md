---
id: game_theory.extensive_game.perfect_information.kuhn_spe_existence_with_chance
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Kuhn Existence Of Pure Subgame-Perfect Equilibrium (With Chance)
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance
  - game_theory.extensive_game.core.nature_player
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - subgame-perfect-equilibrium
  - backward-induction
  - chance
---

# Kuhn Existence Of Pure Subgame-Perfect Equilibrium (With Chance)

Every finite perfect-information game **with Nature / chance moves** has a
subgame-perfect equilibrium in pure strategies. At a chance node the value is
the probability-weighted average of the successor subgame values under any
fixed strategy profile.

## Proof Sketch

Same backward-induction skeleton as [[kuhn_spe_existence_no_chance]], extended
to handle Nature nodes: at a chance position the player payoffs at that node
are defined as the probability-weighted expectation of the successor payoffs,
and the induction step is unchanged.

The expectation step requires von Neumann–Morgenstern utility theory so that
"expected payoff" is meaningful for a general preference relation. With cash /
ℝ-valued payoffs the expectation is well-defined directly.

## Lean status

Not yet implemented. Tracked by [EG-L3
(#181)](https://github.com/gametheoryinlean/EconCSLib/issues/181), which is
itself blocked on the vNM theorem in `EconCSLib/Utility/Lottery.lean`. The
target Lean module is `EconCSLib.ExtensiveGame.StochasticGameTree`; current
state is a type definition + `fairCoinGame` example, no general theorem.

## References

- [MFoGT, Thm. 6.2.7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Original "with or without Nature" form.
- [MSZ, Thm. 3.13] Maschler, Solan, Zamir, *Game Theory*.
