---
id: math.minimax.antisymmetric_matrix_game_value
title: Antisymmetric Matrix Games Have Value
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.Antisymmetric
  declarations:
    - EconCSLib.StrategicGame.MatrixGame.antisymmetric_value_zero
    - EconCSLib.StrategicGame.MatrixGame.antisymmetric_exists_optimal_strategy
    - EconCSLib.StrategicGame.IsAntisymmetric
    - EconCSLib.StrategicGame.IsAntisymmetric.diag_zero
    - EconCSLib.StrategicGame.IsAntisymmetric.quadform_zero
    - EconCSLib.StrategicGame.antisymmetric_self_pairing_zero
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 10(1)"
      format: section
      note: "Brown-von Neumann theorem for antisymmetric games"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - matrix-game
  - antisymmetric
---

# Antisymmetric Matrix Games Have Value

Let $B$ be a real square matrix satisfying $B=-B^T$. Then the matrix game $B$ has
a value. Equivalently, there exists $x\in\Delta(I)$ such that
$$
  Bx\le 0.
$$

*Proof.* The finite minimax theorem gives a mixed value for the square matrix
game. Since $B=-B^T$, every mixed strategy $z$ satisfies
$$
  zBz=0.
$$
For any row mixed strategy $x$, the average of the column payoffs $xBe_j$ under
$x$ is $xBx=0$, so some column gives payoff at most $0$ to player $1$ and the
row player cannot guarantee more than $0$. Dually, for any column mixed strategy
$y$, the average of the row payoffs $e_iBy$ under $y$ is $yBy=0$, so some row
gives payoff at least $0$ and the column player cannot hold the payoff below $0$.
Equality of maxmin and minmax therefore forces the value to be $0$.

If $x$ is an optimal column strategy for player $2$, then it holds every row
payoff to at most $0$, i.e. $(Bx)_i\le0$ for all $i$. This is the displayed
equivalent form.

## References

- [MFoGT, Section 2.8, Exercise 10(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Brown-von Neumann theorem for antisymmetric games.
