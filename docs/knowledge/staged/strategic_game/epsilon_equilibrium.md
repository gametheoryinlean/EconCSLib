---
id: game_theory.strategic_game.equilibrium.epsilon_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Epsilon Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.best_response
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - approximate-equilibrium
---

# Epsilon Equilibrium

For $\epsilon\ge 0$, a profile $s\in S$ is an $\epsilon$-equilibrium if every
player is within $\epsilon$ of a best response:
$$
  g_i(t_i,s_{-i})\le g_i(s)+\epsilon
  \quad\text{for all } i\in I,\ t_i\in S_i.
$$
A Nash equilibrium is the special case $\epsilon=0$.

## References

- [MFoGT, Def. 4.5.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. epsilon-equilibrium in a strategic game.
