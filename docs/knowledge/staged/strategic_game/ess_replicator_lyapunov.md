---
id: game_theory.strategic_game.evolution.ess_replicator_lyapunov
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: ESS Replicator Lyapunov Function
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.evolution.ess_uniform_invasion_barrier
  - game_theory.strategic_game.dynamics.replicator_dynamics
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - evolution
  - replicator-dynamics
---

# ESS Replicator Lyapunov Function

A mixed type $p$ is an evolutionarily stable strategy if and only if
$$
  V(x)=\prod_i x_i^{p_i}
$$
is locally a strict Lyapunov function for the replicator dynamics.

MFoGT proves this by differentiating the logarithm of $V(x_t)$ along a
replicator trajectory: the derivative is $pAx_t-x_tAx_t$, which is positive
near $p$ precisely by the local ESS characterization.

## References

- [MFoGT, Chapter 5, Prop. 5.5.9] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. ESS characterized by a local strict Lyapunov function for replicator dynamics.
