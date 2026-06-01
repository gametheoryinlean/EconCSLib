---
id: game_theory.extensive_game.normal_form.sequential_equilibrium_exists
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.normal_form
title: Existence Of Sequential Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.normal_form.agent_normal_form
  - game_theory.extensive_game.imperfect_information.sequential_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - sequential-equilibrium
  - existence
---

# Existence Of Sequential Equilibrium

Every finite extensive form game with perfect recall has at least one sequential
equilibrium.

## Proof Sketch

MFoGT defers the proof to the following normal-form refinement section. The
strategy is to use fully mixed perturbations and compactness: perturbed games have
equilibria, limits of perturbed behavioral profiles give sequentially rational
strategies, and the limiting beliefs are obtained as limits of Bayes-rule beliefs
from the fully mixed profiles.

## References

- [MFoGT, Thm. 6.4.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. The set of sequential equilibria of a finite perfect-recall extensive game is nonempty.
- [MFoGT, Thm. 6.6.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence proof via Selten perturbations of the agent normal form.
