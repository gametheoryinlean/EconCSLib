---
id: game_theory.strategic_game.equilibrium.symmetric_mixed_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Symmetric Mixed Equilibrium
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
  - game_theory.strategic_game.core.symmetric_game
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - symmetry
  - nash-equilibrium
---

# Symmetric Mixed Equilibrium

If a finite strategic game has a symmetry $\phi$, then it admits a mixed
equilibrium $\sigma$ with the same symmetry:
$$
  \sigma=\phi(\sigma).
$$

## Proof Sketch

Let $X$ be the closed convex subset of mixed profiles fixed by $\phi$. The uniform
mixed profile lies in $X$, so $X$ is nonempty. Nash's fixed-point map respects the
symmetry, hence maps $X$ to itself. Brouwer's fixed point theorem applied on $X$
gives a symmetric fixed point, which is a mixed equilibrium by Nash's argument.

## References

- [MFoGT, Thm. 4.6.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A finite game with symmetry admits a mixed equilibrium with that symmetry.
