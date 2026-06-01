---
id: game_theory.strategic_game.evolution.ess_uniform_invasion_barrier
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: ESS Uniform Invasion Barrier
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.evolution.evolutionarily_stable_strategy
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - evolution
  - ess
---

# ESS Uniform Invasion Barrier

For an evolutionarily stable strategy $p$, the invasion threshold can be chosen
uniformly over all mutants: there is $\epsilon_0>0$ such that every
$q\ne p$ is beaten for every $\epsilon\in(0,\epsilon_0)$.

Equivalently, there is a neighborhood $V(p)$ such that
$$
  pAq>qAq
  \quad\text{for every }q\in V(p),\ q\ne p.
$$

This local form is the bridge from the static ESS condition to stability under
the replicator dynamics.

## References

- [MFoGT, Chapter 5, Prop. 5.5.8] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Uniform threshold and local neighborhood characterizations of ESS.
