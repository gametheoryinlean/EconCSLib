---
id: game_theory.strategic_game.zero_sum.learning.fictitious_play
title: Fictitious Play
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.learning.empirical_frequency
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay
  declarations:
    - MatrixGame.IsFictitiousPlay
source:
  spans:
    - artifact: mfogt
      locator: "Definition 2.7.1"
      format: section
      note: "Realization of fictitious play for a matrix game"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - learning
  - fictitious-play
---

# Fictitious Play

A sequence $(i_n,j_n)_{n\ge1}$ in $I\times J$ is a realization of fictitious
play for a matrix game $A$ if, at each stage $n+1$, both players best respond to
the empirical frequencies of the opponent's past actions.

Write
$$
  x_n=\frac1n\sum_{t=1}^n e_{i_t}\in\Delta(I),
  \qquad
  y_n=\frac1n\sum_{t=1}^n e_{j_t}\in\Delta(J).
$$
Then fictitious play requires
$$
  i_{n+1}\in BR_1(y_n)
  =\{i\in I: e_iAy_n\ge e_kAy_n\ \text{for all }k\in I\},
$$
and, dually,
$$
  j_{n+1}\in BR_2(x_n)
  =\{j\in J: x_nAe_j\le x_nAe_\ell\ \text{for all }\ell\in J\}.
$$
Thus each player behaves as if the opponent's empirical distribution were the
opponent's stationary mixed strategy.

## References

- [MFoGT, Def. 2.7.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Realization of fictitious play for a matrix game.
