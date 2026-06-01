---
id: game_theory.strategic_game.zero_sum.core.epsilon_optimal_strategy
title: Epsilon-Optimal Strategy
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.value
  - game_theory.strategic_game.zero_sum.core.player_guarantee
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.IsEpsilonOptimalRow
    - MatrixGame.IsEpsilonOptimalColumn
source:
  spans:
    - artifact: mfogt
      locator: "Definition 2.2.6"
      format: section
      note: "Epsilon-optimal and optimal strategies"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - optimal-strategy
  - value
---

# Epsilon-Optimal Strategy

Given $\varepsilon>0$, a row strategy $x \in \Delta(I)$ is **maxmin
$\varepsilon$-optimal** if its guarantee meets at least
$\operatorname{val}(A) - \varepsilon$:
$$
  \min_{j \in J} E_A(x, j) \ge \operatorname{val}(A) - \varepsilon.
$$
A $0$-optimal strategy is an optimal strategy. The dual definition (a column
strategy $y$ is $\varepsilon$-optimal when
$\max_{i \in I} E_A(i, y) \le \operatorname{val}(A) + \varepsilon$) applies to
player 2.

## References

- [MFoGT, Def. 2.2.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Epsilon-optimal and optimal strategies.
