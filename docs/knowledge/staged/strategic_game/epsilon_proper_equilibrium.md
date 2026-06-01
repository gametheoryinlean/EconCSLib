---
id: game_theory.strategic_game.refinements.epsilon_proper_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.refinements
title: Epsilon Proper Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.refinements.epsilon_perfect_equilibrium
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - equilibrium-refinement
  - proper-equilibrium
---

# Epsilon Proper Equilibrium

Let $G$ be a finite normal-form game. For $\epsilon>0$, a completely mixed
profile $\sigma^\epsilon\in\operatorname{int}\Sigma$ is $\epsilon$-proper if, for
every player $i$ and pure strategies $s_i,t_i\in S_i$,
$$
  g_i(s_i,\sigma^\epsilon_{-i})
  <
  g_i(t_i,\sigma^\epsilon_{-i})
  \quad\Rightarrow\quad
  \sigma^\epsilon_i(s_i)\le
  \epsilon\,\sigma^\epsilon_i(t_i).
$$

More costly mistakes must be played with probabilities that are smaller by a
factor of at least $\epsilon$. Every $\epsilon$-proper profile is
$\epsilon$-perfect.

## References

- [MFoGT, Def. 6.5.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Completely mixed epsilon-proper profiles in finite normal-form games.
