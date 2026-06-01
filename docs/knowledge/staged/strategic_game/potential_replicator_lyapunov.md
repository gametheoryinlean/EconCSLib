---
id: game_theory.strategic_game.dynamics.potential_replicator_lyapunov
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Potential Is Lyapunov For Replicator Dynamics
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.potential.potential_game
  - game_theory.strategic_game.dynamics.replicator_dynamics
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - potential-game
  - dynamics
---

# Potential Is Lyapunov For Replicator Dynamics

In a finite potential game, the potential is a strict Lyapunov function for the
replicator dynamics and its stationary set.

Along a replicator trajectory $\sigma_t$, the derivative of the potential can be
written as a sum of squares
$$
  \sum_i\sum_{s\in S_i}\sigma_i(s)
  (P(s,\sigma_{-i})-P(\sigma))^2,
$$
so it is nonnegative and vanishes exactly at rest points.

## References

- [MFoGT, Chapter 5, Prop. 5.5.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Potential is a strict Lyapunov function for replicator dynamics in potential games.
