---
id: math.linear_programming.minimax_bridge.player_2_lp
title: Player-2 LP Formulation of a Matrix Game
kind: definition
status: admitted
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.minimax_bridge
uses:
  - game_theory.strategic_game.zero_sum.matrix_game
  - math.linear_programming.minimax_bridge.player_1_lp
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - linear-programming
  - lp-dual
---

# Player-2 LP Formulation of a Matrix Game

For a matrix game $A : I \times J \to \mathbb{R}$ played row-by-column,
the **player-2 (minmax) linear program** seeks a mixed strategy
$y \in \Delta(J)$ ([[game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex]]) and a
scalar $w$ such that every pure row response of player 1 yields at most
$w$:

$$
\boxed{\begin{aligned}
\text{minimise} \quad & w \\
\text{subject to} \quad & \sum_{j \in J} A_{ij}\, y_j \;\le\; w &&\text{for every } i \in I, \\
                & \sum_{j \in J} y_j = 1, \\
                & y_j \ge 0 &&\text{for every } j \in J.
\end{aligned}}
$$

The constraints encode "$A y \le w \cdot \mathbf{1}_I$" plus
probability normalisation on $y$.

## Duality with player 1's LP

The player-2 LP is **exactly the dual** of player 1's LP
([[math.linear_programming.minimax_bridge.player_1_lp]]) in the standard LP duality sense
(write player 1's LP in equality / slack form; take the LP dual; the
result is player 2's LP after relabelling).

Strong LP duality
([[math.linear_programming.strong_duality]]) then yields:

- *Feasibility on both sides*: both LPs are feasible — player 1's LP
  has $v = \min_j A_{ij}$ for $x = e_i$; player 2's LP has analogous
  feasibility.
- *Optimal value equality*: $v^* = w^* = \operatorname{val}(A)$
  ([[game_theory.strategic_game.zero_sum.core.value]]) — the minimax theorem
  ([[game_theory.strategic_game.zero_sum.von_neumann_minimax]]) re-derived from LP
  duality.
- *Complementary slackness*: optimal solutions $(x^*, y^*)$ satisfy
  support / complementarity conditions
  ([[math.minimax.support_complementarity]],
  [[math.minimax.strong_complementarity]]).

## See also

- [[math.linear_programming.minimax_bridge.lp_optimal_iff_optimal_strategy]] formalises the
  bijection between LP optima and game-theoretic optimal strategies.
- [[math.minimax.lp_duality_minimax_proof]] is the explicit
  proof-plan turning LP duality into the matrix-game minimax theorem.
- [[math.linear_programming.minimax_bridge.zero_sum_lp_bridge]] discusses the AGT-style
  presentation of the same equivalence.

## References

- [AGT Section 1.4.2] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
- [MFoGT Section 2.5] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
