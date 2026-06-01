---
id: game_theory.repeated_game.core.finitely_repeated_game
title: Finitely Repeated Game
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
---

# Finitely Repeated Game

For $T\ge 1$, the $T$-stage repeated game $G^T$ evaluates a strategy profile by
the expected average payoff
$$
  \gamma_T^i(\sigma)
  =
  \mathbb E_\sigma\left[
    \frac1T\sum_{t=1}^T g_i(a_t)
  \right].
$$

Because only the first $T$ stages matter, $G^T$ may be treated as a finite
extensive-form game.

## References

- [MFoGT, Chapter 8, Def. 8.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. T-stage repeated game with average payoff.
