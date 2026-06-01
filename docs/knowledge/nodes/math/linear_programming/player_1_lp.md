---
id: math.linear_programming.minimax_bridge.player_1_lp
title: Player-1 LP Formulation of a Matrix Game
kind: definition
status: admitted
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.minimax_bridge
uses:
  - game_theory.strategic_game.zero_sum.matrix_game
  - game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex
  - game_theory.strategic_game.zero_sum.core.value
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - linear-programming
  - lp-primal
---

# Player-1 LP Formulation of a Matrix Game

For a matrix game $A : I \times J \to \mathbb{R}$ played row-by-column,
the **player-1 (maxmin) linear program** seeks a mixed strategy
$x \in \Delta(I)$ ([[game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex]]) and a
scalar $v$ such that every pure column response of player 2 yields at
least $v$:

$$
\boxed{\begin{aligned}
\text{maximise} \quad & v \\
\text{subject to} \quad & \sum_{i \in I} x_i \, A_{ij} \;\ge\; v &&\text{for every } j \in J, \\
                & \sum_{i \in I} x_i = 1, \\
                & x_i \ge 0 &&\text{for every } i \in I.
\end{aligned}}
$$

The decision variables are $(x, v) \in \mathbb{R}^{I} \times \mathbb{R}$;
the constraints encode "$x A \ge v \cdot \mathbf{1}_J$" plus probability
normalisation.

## Standard reformulations

- Eliminate $v$ via $v = \min_j (x A)_j$; the LP becomes
  $\max_{x \in \Delta(I)} \min_{j \in J} (x A)_j$, which is the
  matrix-game **maxmin** definition.
- Add slack variables $s_j \ge 0$ with $\sum_i x_i A_{ij} - s_j = v$ to
  put the LP in standard form for the simplex algorithm.

## Solution interpretation

At any feasible $(x, v)$, $v$ is a *guaranteed* lower bound on player
1's expected payoff against any pure column. At an optimal $(x^*, v^*)$:

- $v^* = \operatorname{val}(A)$ ([[game_theory.strategic_game.zero_sum.core.value]]).
- $x^*$ is a maxmin (Nash) strategy for player 1
  ([[game_theory.strategic_game.zero_sum.core.optimal_strategy_sets]]).

The dual LP corresponds to player 2's minmax LP
([[math.linear_programming.minimax_bridge.player_2_lp]]); strong duality
([[math.linear_programming.strong_duality]]) gives the minimax theorem
([[game_theory.strategic_game.zero_sum.von_neumann_minimax]]).

## References

- [AGT Section 1.4.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*. LP formulation of matrix games.
- [MFoGT Section 2.5] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
- Owen, G. (1995). *Game Theory*. Ch. 3 on LP and matrix games.
