---
id: game_theory.repeated_game.core.uniform_equilibrium
title: Uniform Equilibrium
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.finitely_repeated_game
  - game_theory.repeated_game.core.discounted_game
verification:
  definition: accepted
  proof: gap
tags:
  - strategic-game
  - repeated-game
  - uniform-equilibrium
---

# Uniform Equilibrium

A strategy profile $\sigma$ is a uniform equilibrium if:

1. for every $\epsilon>0$, there is $T_0$ such that $\sigma$ is an
   $\epsilon$-Nash equilibrium of $G^T$ for every $T\ge T_0$; and
2. the average payoff vector $\gamma_T(\sigma)$ converges as $T\to\infty$.

The limit payoff is a uniform equilibrium payoff. MFoGT also records the
Cesaro-Abel robustness: the same profile is approximately optimal for low enough
discount rates, and the discounted payoffs converge to the same limit.

## References

- [MFoGT, Chapter 8, Def. 8.3.4 and Lem. 8.3.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Uniform equilibrium and Cesaro-Abel robustness.
