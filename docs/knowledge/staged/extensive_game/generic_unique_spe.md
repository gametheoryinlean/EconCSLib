---
id: game_theory.extensive_game.perfect_information.generic_unique_spe
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Generic Uniqueness Of Subgame-Perfect Equilibrium
kind: proposition
status: staged
uses:
  - game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - subgame-perfect-equilibrium
  - genericity
---

# Generic Uniqueness Of Subgame-Perfect Equilibrium

A finite perfect-information game, with or without Nature, with $K$ terminal nodes
and $I$ players has generically a unique subgame-perfect equilibrium with respect
to Lebesgue measure on the terminal payoff space.

## Proof Sketch

After excluding payoff parameters that create indifference during backward
induction, every decision point has a unique optimal continuation. The excluded
parameters lie in lower-dimensional equality sets. Therefore, for generic terminal
payoffs, backward induction selects a unique continuation at every node and hence
a unique subgame-perfect equilibrium.

## References

- [MFoGT, Prop. 6.2.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite perfect-information games generically have a unique SPE.
