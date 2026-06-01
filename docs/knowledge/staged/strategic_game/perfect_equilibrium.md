---
id: game_theory.strategic_game.refinements.perfect_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Perfect Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.refinements.epsilon_perfect_equilibrium
  - game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-refinement
  - perfection
---

# Perfect Equilibrium

A mixed profile $\sigma\in\Sigma$ is a perfect equilibrium of a finite normal-form
game if there are completely mixed profiles $\sigma^n\in\operatorname{int}\Sigma$
and numbers $\epsilon_n\to 0$ such that:

- each $\sigma^n$ is $\epsilon_n$-perfect;
- $\sigma^n\to\sigma$.

Thus a perfect equilibrium is a limit of equilibria of games in which every pure
strategy has positive tremble probability and non-best responses vanish in the
limit.

## References

- [MFoGT, Def. 6.5.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Selten perfect equilibrium as a limit of epsilon-perfect completely mixed profiles.
