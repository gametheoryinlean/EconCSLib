---
id: game_theory.repeated_game.core.discounted_game
title: Discounted Repeated Game
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
  - discounting
---

# Discounted Repeated Game

For discount rate $\lambda\in(0,1]$, the discounted repeated game $G^\lambda$
evaluates player $i$ by
$$
  \gamma_\lambda^i(\sigma)
  =
  \mathbb E_\sigma\left[
    \lambda\sum_{t=1}^\infty (1-\lambda)^{t-1}g_i(a_t)
  \right].
$$

Small $\lambda$ corresponds to patient players. MFoGT uses normalized discounted
payoffs, so a constant stream $c$ has value $c$.

## References

- [MFoGT, Chapter 8, Def. 8.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Infinite repeated game with normalized discount rate.
