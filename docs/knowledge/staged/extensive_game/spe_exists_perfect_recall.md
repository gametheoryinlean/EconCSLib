---
id: game_theory.extensive_game.imperfect_information.spe_exists_perfect_recall
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Existence Of Subgame-Perfect Equilibrium With Perfect Recall
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.spe_imperfect_information
  - game_theory.extensive_game.imperfect_information.behavioral_equilibrium_exists
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - subgame-perfect-equilibrium
  - perfect-recall
  - existence
---

# Existence Of Subgame-Perfect Equilibrium With Perfect Recall

Every finite extensive form game with perfect recall admits a subgame-perfect
equilibrium.

## Proof Sketch

Induct on the number of subgames. If there is no proper subgame, behavioral
equilibrium existence gives the result. Otherwise, solve all proper subgames by
the induction hypothesis, replace each subgame root by its equilibrium payoff, and
solve the reduced game by behavioral equilibrium existence. Concatenating the
reduced-game equilibrium with the equilibria of the proper subgames gives a
subgame-perfect equilibrium.

## References

- [MFoGT, Thm. 6.4.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Every finite extensive form game with perfect recall admits an SPE.
