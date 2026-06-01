---
id: game_theory.strategic_game.dynamics.nash_field
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dynamics
title: Nash Field
kind: definition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - dynamics
  - nash-equilibrium
---

# Nash Field

A Nash field is a continuous map, or an upper semicontinuous correspondence,
$$
  \Psi:G\times\Sigma\to\Sigma
$$
such that for every finite game $g$,
$$
  NE(g)=\{\sigma\in\Sigma:\Psi(g,\sigma)=\sigma\}.
$$

Each Nash field induces a dynamical system
$$
  \dot\sigma=\Psi(g,\sigma)-\sigma
$$
whose rest points are exactly the Nash equilibria of $g$.

## References

- [MFoGT, Chapter 5, Def. 5.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nash fields whose fixed points are Nash equilibria.
