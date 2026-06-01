---
id: game_theory.strategic_game.refinements.proper_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Proper Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.refinements.epsilon_proper_equilibrium
  - game_theory.strategic_game.refinements.perfect_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-refinement
  - proper-equilibrium
---

# Proper Equilibrium

A mixed profile $\sigma\in\Sigma$ is a proper equilibrium of a finite normal-form
game if there are completely mixed profiles $\sigma^n\in\operatorname{int}\Sigma$
and numbers $\epsilon_n\to 0$ such that:

- each $\sigma^n$ is $\epsilon_n$-proper;
- $\sigma^n\to\sigma$.

Proper equilibrium refines perfect equilibrium by ranking mistakes: worse
deviations must become infinitely less likely than better deviations.

## References

- [MFoGT, Def. 6.5.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Myerson proper equilibrium as a limit of epsilon-proper completely mixed profiles.
