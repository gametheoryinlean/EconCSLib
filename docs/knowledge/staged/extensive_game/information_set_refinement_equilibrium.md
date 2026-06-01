---
id: game_theory.extensive_game.imperfect_information.information_set_refinement_equilibrium
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Information Set Refinement And Equilibrium
kind: proposition
status: staged
uses:
  - game_theory.extensive_game.imperfect_information.perfect_recall
  - game_theory.strategic_game.nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - information-set
  - exercise
---

# Information Set Refinement And Equilibrium

Let $G'$ be obtained from a finite perfect-recall extensive game $G$ by refining
some information sets. If $\sigma$ is a pure Nash equilibrium of $G$ and there are
no chance moves, then $\sigma$ is also a Nash equilibrium of $G'$.

The conclusion does not extend to mixed equilibria or to games with chance moves.
MFoGT gives two counterexamples: matching pennies in extensive form after player
2 observes player 1's move, and a variant where player 1 is replaced by Nature.

## Proof Sketch

A pure strategy profile without chance moves induces a unique play. Any profitable
deviation at a reached refined information set would also be a profitable deviation
in the coarser game.

## References

- [MFoGT, Exercise 6.8.5 and Hints for Chapter 6, Exercise 5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Pure no-chance equilibria survive information-set refinement; mixed or chance cases need not.
