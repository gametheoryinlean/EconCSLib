---
id: game_theory.repeated_game.core.strategy
title: Repeated Game Strategy
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.standard_repeated_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
  - strategy
---

# Repeated Game Strategy

In a standard repeated game, a strategy of player $i$ is a map
$$
  \sigma_i:H\to\Delta(A_i),
$$
where $H=\bigcup_{t\ge 0}H_t$ is the set of finite public histories.

After history $h\in H_t$, the mixed action $\sigma_i(h)$ is used at stage
$t+1$. A strategy profile induces a probability distribution on finite histories
and, by extension, on infinite plays.

## References

- [MFoGT, Chapter 8, Def. 8.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Behavior strategies in standard repeated games.
