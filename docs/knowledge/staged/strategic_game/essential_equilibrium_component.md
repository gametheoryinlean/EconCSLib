---
id: game_theory.strategic_game.manifold.essential_component
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Essential Equilibrium Component
kind: definition
status: staged
uses:
  - game_theory.strategic_game.manifold.equilibrium_manifold
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-manifold
  - robustness
---

# Essential Equilibrium Component

Let $C$ be a connected component of the Nash equilibrium set of a finite game
$g$. The component $C$ is essential if every neighborhood $V$ of $C$ contains an
equilibrium of every game in some sufficiently small neighborhood of $g$.

Equivalently, the component cannot be removed by arbitrarily small payoff
perturbations.

## References

- [MFoGT, Chapter 5, Def. 5.3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Essential component of Nash equilibria.
