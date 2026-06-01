---
id: game_theory.strategic_game.continuous.convex_game_variational_characterization
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Convex Game Nash Variational Characterization
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.continuous.convex_game
  - game_theory.strategic_game.nash_equilibrium
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - convex-game
  - nash-equilibrium
---

# Convex Game Nash Variational Characterization

For a convex game, define
$$
  \Phi(s,t)=\sum_i G_i(s_i,t_{-i}).
$$
Then $t$ is a Nash equilibrium if and only if
$$
  \Phi(s,t)\le \Phi(t,t)
  \quad\text{for every }s\in S.
$$

## References

- [MFoGT, Section 4.12, Exercise 7(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nash equilibrium characterization using Phi(s,t).
