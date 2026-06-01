---
id: game_theory.strategic_game.zero_sum.learning.empirical_frequency
title: Empirical Frequency Of Play
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
uses:
  - game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay
  declarations:
    - MatrixGame.empiricalFrequency
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.7, before Definition 2.7.1"
      format: section
      note: "Empirical distributions x_n and y_n of previously played pure actions"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - learning
  - fictitious-play
---

# Empirical Frequency Of Play

Let $(i_t)_{t\ge1}$ be a sequence of pure actions in a finite action set $I$.
After $n$ stages, its empirical frequency is the mixed strategy
$$
  x_n=\frac1n\sum_{t=1}^n e_{i_t}\in\Delta(I),
$$
where $e_i$ is the Dirac mass on action $i$.

For a two-player matrix game with realized pure actions $(i_t,j_t)$, write
$$
  x_n=\frac1n\sum_{t=1}^n e_{i_t}\in\Delta(I),
  \qquad
  y_n=\frac1n\sum_{t=1}^n e_{j_t}\in\Delta(J).
$$
Fictitious play is defined by requiring each player's next action to be a best
response to the opponent's current empirical frequency.

## References

- [MFoGT, Section 2.7, before Def. 2.7.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Empirical distributions x_n and y_n of previously played pure actions.
