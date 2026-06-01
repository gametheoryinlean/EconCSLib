---
id: game_theory.strategic_game.continuous.cournot_duopoly_supermodular_existence
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Cournot Duopoly Equilibrium From Supermodularity
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.continuous.supermodular_game_nash_exists
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - supermodular-game
  - cournot
---

# Cournot Duopoly Equilibrium From Supermodularity

Consider two firms choosing quantities $q_i\in[0,Q_i]$ with payoff
$$
  g_i(q_i,q_j)=q_iP_i(q_i+q_j)-C_i(q_i).
$$
Assume $P_i$ and $C_i$ are $C^1$, and the marginal revenue
$$
  P_i+q_i\frac{\partial P_i}{\partial q_i}
$$
is decreasing in $q_j$. Then the Cournot duopoly has a Cournot-Nash equilibrium.

## References

- [MFoGT, Section 4.12, Exercise 4(3)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Cournot duopoly application of supermodular game existence.
