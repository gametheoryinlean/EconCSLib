---
id: game_theory.strategic_game.manifold.kohlberg_mertens_structure_theorem
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Kohlberg Mertens Structure Theorem
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.manifold.equilibrium_manifold
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - equilibrium-manifold
  - topology
---

# Kohlberg Mertens Structure Theorem

For finite games with fixed player and action sets, let $\overline E$ and
$\overline G$ denote the compactified equilibrium graph and game space. The
projection
$$
  \pi:\overline E\to\overline G
$$
is homotopic to a homeomorphism.

MFoGT uses this structural theorem to derive robustness and genericity facts
for Nash equilibrium components.

## References

- [MFoGT, Chapter 5, Thm. 5.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Projection from the compactified equilibrium graph is homotopic to a homeomorphism.
