---
id: game_theory.strategic_game.zero_sum.applications.stochastic_matrix_invariant_distribution
title: Stochastic Matrix Has An Invariant Distribution
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
  - game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix
  declarations:
    - EconCSLib.StrategicGame.MatrixGame.exists_invariant_distribution
    - EconCSLib.StrategicGame.IsStochasticMatrix
    - EconCSLib.StrategicGame.uniformDist
    - EconCSLib.StrategicGame.MatrixGame.disp
    - EconCSLib.StrategicGame.IsStochasticMatrix.total_mass_preserved
    - EconCSLib.StrategicGame.MatrixGame.disp_Ei
    - EconCSLib.StrategicGame.MatrixGame.disp_Ej
    - EconCSLib.StrategicGame.MatrixGame.disp_Ei_uniform
    - EconCSLib.StrategicGame.MatrixGame.disp_Ei_argmin_nonneg
    - EconCSLib.StrategicGame.MatrixGame.disp_value_eq_zero
    - EconCSLib.StrategicGame.MatrixGame.disp_value_ge_zero
    - EconCSLib.StrategicGame.MatrixGame.disp_value_le_zero
source:
  spans:
    - artifact: mfogt
      locator: "Corollary 2.5.2"
      format: section
      note: "Invariant distribution of a stochastic matrix from minimax"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - stochastic-matrix
  - invariant-distribution
---

# Stochastic Matrix Has An Invariant Distribution

## Statement

Let $A : I \times I \to \mathbb{R}$ be a (row-)stochastic matrix: every
entry is non-negative and every row sums to $1$. Then there exists a
mixed strategy $x \in \Delta(I)$ such that

$$
  \forall j,\quad \sum_i x_i \, A_{ij} = x_j
$$

— i.e. $x A = x$, an **invariant distribution** of $A$.

## Proof

Let $B := A - \operatorname{Id}$, i.e. $B_{ij} = A_{ij} - [i=j]$, and
consider the matrix game with payoff matrix $B$.

### Step 1 — The displacement game has value $0$

**Upper bound $v \le 0$.** Take Player 2's uniform mixed strategy
$y_{\mathrm{unif}}$ with $y_j = 1 / |I|$. For every pure row $i$:
$$
  E_i(i, y_{\mathrm{unif}}) = \sum_j B_{ij} \cdot \tfrac{1}{|I|}
    = \tfrac{1}{|I|} \big(\!\sum_j A_{ij}\big) - \tfrac{1}{|I|}
    = \tfrac{1}{|I|} - \tfrac{1}{|I|} = 0,
$$
using $\sum_j A_{ij} = 1$. Hence Player 2's guarantee under
$y_{\mathrm{unif}}$ is $\sup_i E_i(i, y_{\mathrm{unif}}) = 0$. Since
$\mathrm{value} = \mathrm{minimax} = \inf_y \mathrm{guarantee}_{II}(y)$,
we get $\mathrm{value} \le 0$.

**Lower bound $v \ge 0$.** For any column strategy $y$, pick
$i_0 \in \arg\min_j y_j$. Since $A_{i_0 j} \ge 0$, $y_j \ge y_{i_0}$,
and $\sum_j A_{i_0 j} = 1$:
$$
  (A y)_{i_0} \;=\; \sum_j A_{i_0 j}\, y_j
                \;\ge\; \sum_j A_{i_0 j}\, y_{i_0}
                \;=\; y_{i_0} \cdot 1 \;=\; y_{i_0}.
$$
Therefore $E_i(i_0, y) = (Ay)_{i_0} - y_{i_0} \ge 0$, and
$\mathrm{guarantee}_{II}(y) = \sup_i E_i(i, y) \ge 0$ for every $y$.
Hence $\mathrm{minimax} = \inf_y \mathrm{guarantee}_{II}(y) \ge 0$.

Combining, $\mathrm{value} = 0$.

### Step 2 — A row-optimal strategy is invariant

Take any row-optimal $x^* \in X(A)$ — existence via
[[node:game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium]] combined with
[[node:game_theory.strategic_game.zero_sum.core.optimal_strategy_sets]]. Then for every pure column $j$,
$$
  E_j(x^*, j) \;\ge\; \mathrm{value} \;=\; 0.
$$
Expanding $E_j(x^*, j) = (x^* A)_j - x^*_j$, we get
$(x^* A)_j \ge x^*_j$ for every $j$, i.e. $x^* A \ge x^*$
componentwise.

### Step 3 — Total mass forces componentwise equality

Sum over $j$. Using $\sum_j A_{ij} = 1$ and $\sum_i x^*_i = 1$:
$$
  \sum_j (x^* A)_j = \sum_i x^*_i \!\sum_j A_{ij} = \sum_i x^*_i = 1
    = \sum_j x^*_j.
$$
Hence $\sum_j ((x^* A)_j - x^*_j) = 0$, with every term $\ge 0$, so
every term is exactly $0$:
$$
  \forall j,\quad (x^* A)_j = x^*_j.
$$

So $x^*$ is an invariant distribution. $\square$

## Remarks

- The argument is constructive once an optimal pair is given by
  the minimax existence theorem ([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]).
- The choice $B = A - \operatorname{Id}$ converts "$x A = x$" into the
  saddle-point condition for the matrix game with payoff $B$.
- The Lean implementation lives in
  `EconCSLib.StrategicGame.StochasticMatrix` and consists of:
  - `IsStochasticMatrix` — predicate (rows sum to 1, entries ≥ 0).
  - `uniformDist` — uniform mixed strategy on a `Nonempty` `Fintype`.
  - `MatrixGame.exists_invariant_distribution` — main theorem.

## References

- [MFoGT, Cor. 2.5.2] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Invariant distribution of a stochastic matrix from minimax.
