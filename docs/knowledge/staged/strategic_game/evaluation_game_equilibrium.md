---
id: game_theory.strategic_game.variational.evaluation_game_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Evaluation Game Equilibrium
kind: definition
status: staged
uses:
  - math.fixed_point.brouwer_compact_convex
verification:
  definition: accepted
  proof: gap
tags:
  - strategic-game
  - variational-inequality
  - fixed-point
---

# Evaluation Game Equilibrium

Let $(X_i)_{i\in I}$ be nonempty convex compact subsets of Hilbert spaces and
let $\Phi_i:X\to H_i$ be evaluation maps on $X=\prod_i X_i$. The equilibrium set
$NE(\Phi)$ consists of all $x\in X$ such that
$$
  \langle \Phi(x),x-y\rangle\ge 0
  \quad\text{for every }y\in X.
$$

Equivalently, if $\Pi_X$ is the projection onto $X$, then $NE(\Phi)$ is the fixed
point set of
$$
  T(x)=\Pi_X(x+\Phi(x)).
$$
When $\Phi$ is continuous, Brouwer's theorem gives nonemptiness.

## References

- [MFoGT, Chapter 5, Def. 5.2.4 and Prop. 5.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. General evaluation equilibrium as a variational inequality.
