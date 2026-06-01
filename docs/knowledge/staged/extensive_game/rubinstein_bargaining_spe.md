---
id: game_theory.extensive_game.examples.rubinstein_bargaining_spe
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.examples
title: Rubinstein Bargaining Subgame Perfect Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.kuhn_spe_existence_no_chance
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - subgame-perfect-equilibrium
  - bargaining
  - exercise
---

# Rubinstein Bargaining Subgame Perfect Equilibrium

In the ultimatum game with amount $M>0$, the unique subgame-perfect equilibrium
has player 1 offer $0$ to player 2 and player 2 accept every positive offer.

In the finite alternating-offer game with discount factor $\delta\in(0,1)$, let
$a_n$ be the fraction of the current surplus kept by the current proposer when
there are $n$ rounds remaining. Then
$$
  a_1=1,
  \qquad
  a_n=1-\delta a_{n-1}.
$$
Thus
$$
  a_n=\frac{1-(-\delta)^n}{1+\delta}.
$$

In the infinite discounted alternating-offer game, the unique subgame-perfect
equilibrium has each proposer offer the other player the fraction
$$
  \frac{\delta}{1+\delta}
$$
of the current surplus, and the offer is accepted. The proposer keeps
$1/(1+\delta)$ of the current surplus.

## References

- [MFoGT, Exercise 6.8.4 and Hints for Chapter 6, Exercise 4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Ultimatum, finite alternating-offer, and infinite discounted bargaining SPE formulas.
