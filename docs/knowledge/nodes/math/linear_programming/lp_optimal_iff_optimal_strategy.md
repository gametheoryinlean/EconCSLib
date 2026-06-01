---
id: math.linear_programming.minimax_bridge.lp_optimal_iff_optimal_strategy
title: LP Optimum ↔ Game-Theoretic Optimal Strategy
kind: theorem
status: admitted
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.minimax_bridge
uses:
  - math.linear_programming.minimax_bridge.player_2_lp
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
  - game_theory.strategic_game.zero_sum.core.saddle_point
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - linear-programming
  - optimal-strategy
  - bijection
---

# LP Optimum ↔ Game-Theoretic Optimal Strategy

**Theorem.** Let $A : I \times J \to \mathbb{R}$ be a finite matrix
game with value $\operatorname{val}(A) \in \mathbb{R}$
([[game_theory.strategic_game.zero_sum.core.value]]).

1. The pair $(x^*, v^*)$ is optimal for player 1's LP
   ([[math.linear_programming.minimax_bridge.player_1_lp]]) **if and only if** $x^*$ is a maxmin
   (optimal) mixed strategy for player 1 and $v^* = \operatorname{val}(A)$.

2. The pair $(y^*, w^*)$ is optimal for player 2's LP
   ([[math.linear_programming.minimax_bridge.player_2_lp]]) **if and only if** $y^*$ is a minmax
   (optimal) mixed strategy for player 2 and $w^* = \operatorname{val}(A)$.

3. Any pair $(x^*, y^*)$ obtained from LP optima is a saddle point of
   $A$ ([[game_theory.strategic_game.zero_sum.core.saddle_point]]); conversely every saddle point
   gives optimal LP solutions.

## Proof

**(⇒)** *LP optimum gives optimal strategy.* If $(x^*, v^*)$ is
optimal for player 1's LP, then by the constraint
$xA \ge v^* \cdot \mathbf{1}_J$ at $(x^*, v^*)$, player 1's mixed
strategy $x^*$ guarantees at least $v^*$ against every pure column,
hence against every mixed column. By LP-duality with
[[math.linear_programming.minimax_bridge.player_2_lp]] and
[[math.linear_programming.strong_duality]], $v^* = w^*$ equals the LP
common value, which is also $\operatorname{val}(A)$ by the standard
maxmin-minmax characterisation.

**(⇐)** *Optimal strategy gives LP optimum.* If $x^*$ achieves
$\max_x \min_j (xA)_j = \operatorname{val}(A)$, then
$(x^*, \operatorname{val}(A))$ satisfies all LP constraints and
attains the objective at $v = \operatorname{val}(A)$. Symmetric for
player 2.

The saddle-point statement (3) follows by combining (1) and (2):
optimal $(x^*, y^*)$ jointly satisfy
$x^* A \ge \operatorname{val}(A) \cdot \mathbf{1}_J$ and
$A y^* \le \operatorname{val}(A) \cdot \mathbf{1}_I$, which is exactly
the saddle-point characterisation
([[game_theory.strategic_game.zero_sum.core.optimal_pairs_are_saddle_points]]).

## Significance

This theorem is the *clean conversion* between the LP and game-theoretic
viewpoints:

- **Algorithmically**, it lets us compute optimal mixed strategies with
  any LP solver (simplex, interior-point, ...) — the entire
  computational complexity of zero-sum games is exactly the LP
  complexity.
- **Mathematically**, it says LP-duality and the minimax theorem are
  equivalent statements
  ([[math.minimax.lp_duality_minimax_proof]]).
- **Structurally**, support and strong-complementarity properties
  ([[math.minimax.support_complementarity]],
  [[math.minimax.strong_complementarity]]) transfer cleanly
  between the two pictures.

## References

- [AGT Section 1.4.2, Thm. 1.11] Nisan, Roughgarden, Tardos, and Vazirani,
  *Algorithmic Game Theory*.
- [MFoGT Section 2.5] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*.
