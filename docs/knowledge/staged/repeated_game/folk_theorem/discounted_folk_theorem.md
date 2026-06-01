---
id: game_theory.repeated_game.folk_theorem.discounted_folk_theorem
title: Discounted Folk Theorem
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.folk_theorem
uses:
  - game_theory.repeated_game.core.discounted_game
  - game_theory.repeated_game.core.feasible_individually_rational_payoffs
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - repeated-game
  - folk-theorem
  - discounting
---

# Discounted Folk Theorem

Let $E_\lambda$ be the set of Nash equilibrium payoffs of the discounted repeated
game. If either there are two players or there exists a feasible individually
rational payoff that is strictly above every player's minmax level, then
$$
  E_\lambda\to E
  \quad\text{as }\lambda\to 0
$$
in Hausdorff distance.

MFoGT emphasizes that the stated hypotheses matter: without them, convergence
can fail in games with three or more players.

## References

- [MFoGT, Chapter 8, Thm. 8.5.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Hausdorff convergence of discounted equilibrium payoffs under MFoGT hypotheses.
