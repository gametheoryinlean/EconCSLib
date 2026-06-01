---
id: game_theory.strategic_game.zero_sum.examples.computation_three_by_two_example
title: Three-By-Two Matrix Game Computation
kind: example
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.ThreeByTwo
  declarations:
    - EconCSLib.StrategicGame.Examples.threeByTwoExample
    - EconCSLib.StrategicGame.Examples.threeByTwoRowOpt
    - EconCSLib.StrategicGame.Examples.threeByTwoColOpt
    - EconCSLib.StrategicGame.Examples.threeByTwoExample_value
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 5"
      format: section
      note: "Compute the value and optimal strategies of a displayed 3 by 2 matrix game"
    - artifact: mfogt
      locator: "Section 9.2, Exercise 5 hints"
      format: section
      note: "Gives the reduced game and the optimal strategies"
verification:
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - matrix-game
  - computation
  - example
---

# Three-By-Two Matrix Game Computation

MFoGT Exercise 2.8.5 asks for the value and optimal strategies of
$$
  A=
  \begin{pmatrix}
    3 & -1\\
    0 & 0\\
    -2 & 1
  \end{pmatrix}.
$$

The middle row is strictly dominated by the mixed row
$0.49\,a_1+0.51\,a_3$, so the computation reduces to the two-row game using
rows $a_1$ and $a_3$:
$$
  \begin{pmatrix}
    3 & -1\\
    -2 & 1
  \end{pmatrix}.
$$

The value is
$$
  \operatorname{val}(A)=\frac17.
$$
An optimal strategy for player 1 plays rows $(a_1,a_2,a_3)$ with probabilities
$$
  \left(\frac37,0,\frac47\right),
$$
and an optimal strategy for player 2 plays columns $(b_1,b_2)$ with
probabilities
$$
  \left(\frac27,\frac57\right).
$$

This example is a useful small test case for dominance elimination,
equalizing-strategy computations, and matrix-game value formulas.

## References

- [MFoGT, Section 2.8, Exercise 5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Compute the value and optimal strategies of a displayed 3 by 2 matrix game.
- [MFoGT, Section 9.2, Exercise 5 hints] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Gives the reduced game and the optimal strategies.
