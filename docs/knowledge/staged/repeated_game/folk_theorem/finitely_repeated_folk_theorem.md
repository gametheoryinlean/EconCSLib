---
id: game_theory.repeated_game.folk_theorem.finitely_repeated_folk_theorem
title: Finitely Repeated Folk Theorem
kind: theorem
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.folk_theorem
uses:
  - game_theory.repeated_game.core.finitely_repeated_game
  - game_theory.repeated_game.core.feasible_individually_rational_payoffs
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - repeated-game
  - folk-theorem
---

# Finitely Repeated Folk Theorem

Assume that, for each player $i$, some one-shot Nash equilibrium payoff gives
player $i$ strictly more than their minmax level. Then the Nash equilibrium
payoff sets of the $T$-stage repeated games converge to the feasible individually
rational set:
$$
  E_T\to E
  \quad\text{as }T\to\infty.
$$

The proof appends one-shot equilibrium reward phases after a long feasible main
path, so that deviations during the main path are not profitable.

## References

- [MFoGT, Chapter 8, Thm. 8.5.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Large finite-horizon folk theorem with terminal equilibrium rewards.
