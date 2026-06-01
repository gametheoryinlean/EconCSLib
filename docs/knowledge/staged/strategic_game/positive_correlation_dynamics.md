---
id: game_theory.strategic_game.dynamics.positive_correlation
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Positive Correlation Dynamics
kind: definition
status: staged
uses:
  - game_theory.strategic_game.variational.evaluation_game_equilibrium
verification:
  definition: accepted
  proof: gap
tags:
  - strategic-game
  - dynamics
  - potential-game
---

# Positive Correlation Dynamics

A dynamics $\dot\sigma=B_\Phi(\sigma)$ satisfies positive correlation if, for each
player $i$ and configuration $\sigma$, whenever player $i$'s component of the
vector field is nonzero,
$$
  \langle B_\Phi^i(\sigma),\Phi_i(\sigma)\rangle>0
$$

This formalizes myopic adjustment: moving along the dynamics locally improves
the current evaluation. In a potential game, positive correlation implies that the
potential is a strict Lyapunov function for the dynamics.

## References

- [MFoGT, Chapter 5, Def. 5.5.5 and Prop. 5.5.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Positive correlation and Lyapunov property for potential games.
