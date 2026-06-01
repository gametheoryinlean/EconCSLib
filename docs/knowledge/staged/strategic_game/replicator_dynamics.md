---
id: game_theory.strategic_game.dynamics.replicator_dynamics
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Replicator Dynamics
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.symmetric_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - dynamics
  - evolution
---

# Replicator Dynamics

For a symmetric two-player game with payoff matrix $A$, a population
$p\in\Delta(K)$ is stationary if every type used with positive mass has average
fitness:
$$
  p_k>0\quad\text{implies}\quad e_kAp=pAp.
$$

The one-population replicator dynamics is
$$
  \dot p_k=p_k(e_kAp-pAp).
$$
It preserves the simplex because the total derivative of $\sum_k p_k$ is zero.

## References

- [MFoGT, Chapter 5, Definitions 5.5.1 and 5.5.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Stationary populations and one-population replicator dynamics.
