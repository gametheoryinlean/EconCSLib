---
id: game_theory.strategic_game.zero_sum.learning.hannan_three_cycle_example
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Three-Cycle Hannan Distribution Is Not Internally Consistent
kind: example
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.hannan_zero_sum_intersection
  - game_theory.strategic_game.zero_sum.learning.no_c_regret_set
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.HannanThreeCycle
  declarations:
    - StrategicGame.Examples.hannanThreeCycleDiagonal_mem_rowHannan
    - StrategicGame.Examples.hannanThreeCycleDiagonal_mem_columnHannan
    - StrategicGame.Examples.hannanThreeCycleDiagonal_marginals_optimal_and_payoff_eq_value
    - StrategicGame.Examples.hannanThreeCycleDiagonal_comparisonGain_zero_two
    - StrategicGame.Examples.hannanThreeCycleDiagonal_not_mem_noCRegretSet
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - hannan-set
  - internal-regret
  - counterexample
---

# Three-Cycle Hannan Distribution Is Not Internally Consistent

For the antisymmetric matrix
$$
  \begin{pmatrix}
    0&1&-1\\
    -1&0&1\\
    1&-1&0
  \end{pmatrix},
$$
put probability $1/3$ on each diagonal action pair. This distribution
satisfies both players' Hannan inequalities; its marginals are optimal and its
payoff is the value $0$. Nevertheless, changing row action $0$ to row action
$2$ on the dates when $0$ was played has comparison gain $1/3$. Hence the
distribution is not in the row player's no-$C$-regret set.

This formalizes MFoGT's three-cycle example and exhibits the gap between external and
internal consistency.

## References

- [MFoGT, Example 7.3.14] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Diagonal distribution in the three-cycle zero-sum game.
