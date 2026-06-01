---
id: game_theory.strategic_game.manifold.equilibrium_manifold
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Equilibrium Manifold
kind: definition
status: staged
uses:
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-manifold
  - nash-equilibrium
---

# Equilibrium Manifold

Fix finite player and action sets. The space of games is the Euclidean space of
payoff tensors. The equilibrium manifold is the graph of the mixed Nash
equilibrium correspondence:
$$
  E=\{(g,\sigma):\sigma\text{ is a Nash equilibrium of }g\}.
$$

MFoGT studies the projection from this graph to the payoff space in order to
understand robustness, index, and generic structure of equilibrium components.

## References

- [MFoGT, Chapter 5, Section 5.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Graph of the Nash equilibrium correspondence as payoffs vary.
