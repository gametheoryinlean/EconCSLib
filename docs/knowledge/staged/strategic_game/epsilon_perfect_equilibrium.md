---
id: game_theory.strategic_game.refinements.epsilon_perfect_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Epsilon Perfect Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-refinement
  - perfection
---

# Epsilon Perfect Equilibrium

Let $G$ be a finite normal-form game and let
$\Sigma_i=\Delta(S_i)$. For $\epsilon>0$, a completely mixed profile
$\sigma^\epsilon\in\operatorname{int}\Sigma$ is $\epsilon$-perfect if, for every
player $i$ and every pure strategy $s_i\in S_i$,
$$
  s_i\notin BR_i(\sigma^\epsilon_{-i})
  \quad\Rightarrow\quad
  \sigma^\epsilon_i(s_i)\le \epsilon.
$$

Suboptimal pure strategies may still be played, but only with very small
probability.

## References

- [MFoGT, Def. 6.5.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Completely mixed epsilon-perfect profiles in finite normal-form games.
