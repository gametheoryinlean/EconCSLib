---
id: math.minimax.strong_complementarity
title: Strong Complementarity
kind: proposition
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - game_theory.strategic_game.zero_sum.core.support_complementarity
  - game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium
  - math.linear_programming.strong_complementarity
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.StrongComplementarity
  declarations:
    - MatrixGame.exists_strong_complementary_pair
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(c)"
      format: section
      note: "Existence of a strongly complementary optimal pair"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - complementarity
  - linear-programming
---

# Strong Complementarity

## Statement

For a finite zero-sum matrix game $A : I \times J \to \mathbb{R}$, there
exists an optimal pair $(x^*, y^*) \in X(A) \times Y(A)$ such that

- for every row $i$: $x^*_i > 0 \iff A.\mathrm{Ei}\,i\,y^* = A.\mathrm{value}$
  (i.e. row $i$ is a best response to $y^*$);
- for every column $j$: $y^*_j > 0 \iff A.\mathrm{Ej}\,x^*\,j = A.\mathrm{value}$
  (i.e. column $j$ is a best response to $x^*$).

## Proof

*The forward direction* of each biconditional is
[[node:game_theory.strategic_game.zero_sum.core.support_complementarity]] (Prop. 2.4.1(b)) and
holds for every optimal pair: if $x^*_i > 0$, then row $i$ obtains the
value against $y^*$; dually for columns.

*The reverse direction — existence of an optimal pair where every
best-response row has positive probability* — comes from
[[node:math.linear_programming.strong_complementarity]] applied to the
matrix-game LP. The Lean implementation
(`MatrixGame.exists_strong_complementary_pair`) carries out:

### Step 1 — Shift to make payoffs strictly positive

Choose $K := 1 + |A.\mathrm{value}| + \max_{i,j} |A_{ij}|$. Then
$A'_{ij} := A_{ij} + K > 0$ for every $i, j$, and the shifted value
$v' := A.\mathrm{value} + K > 0$. The shift is required because the
standard-form LP we apply expects nonneg variables and finite
optimum; with positive payoffs the value-LP has a clean primal form.

### Step 2 — Encode the row LP in standard form

The shifted row LP is

$$
  \min \sum_i x'_i \quad
  \text{s.t.} \quad (A'^{\mathsf T} x')_j \ge 1\ (\forall j \in J),
  \quad x'_i \ge 0\ (\forall i \in I).
$$

Optimal $x'$ rescales to a mixed strategy via $x_i = x'_i \cdot v'$
(since $\sum_i x'_i = 1/v'$ at optimum).

### Step 3 — Build LP-feasible primal and dual from a matrix-game optimal pair

From an existing matrix-game optimal pair $(x^0, y^0)$ (via
[[node:game_theory.strategic_game.zero_sum.matrix_game_nash_equilibrium]]), define
$x'^0 := x^0 / v'$ and $u'^0 := y^0 / v'$. Both have LP objective
$1/v'$, hence are LP-optimal by weak duality.

### Step 4 — Apply LP strong complementarity

Invoke [[node:math.linear_programming.strong_complementarity]] to obtain a
strong-CS optimal LP pair $(x'^*, u'^*)$.

### Step 5 — Rescale back and translate the biconditional

Set $x^*_i := x'^*(e\,i) \cdot v'$ and $y^*_j := u'^*_j \cdot v'$
(where $e : I \simeq \mathrm{Fin}\,(\#I)$ is the standard equivalence
used so the LP variables fit `Fin n → \mathbb{R}`). Verify:

- $(A^{\mathsf T} x^*)_j = A.\mathrm{Ej}\,x^*\,j$ and
  $(A^{\mathsf T} x^* + K)_j = (A'^{\mathsf T} x^*)_j = (A'^{\mathsf T} x'^*)_j \cdot v'
  \ge 1 \cdot v' = v'$,
  so $A.\mathrm{Ej}\,x^*\,j \ge A.\mathrm{value}$ — i.e. $x^*$ is
  row-optimal. Symmetrically $y^*$ is column-optimal.

The LP strict complementarity at the column index $i$ (in the strong
pair) is the assertion
$x'^*(e\,i) + (1 - \sum_j u'^*_j \cdot A'_{i,j}) > 0$. Multiplying
through by $v'$ and using $v' = A.\mathrm{value} + K$, this becomes

$$
  x^*_i + (A.\mathrm{value} - A.\mathrm{Ei}\,i\,y^*) > 0.
$$

Both summands are non-negative (by primal/dual feasibility), so at
least one is strictly positive: $x^*_i > 0$ **or**
$A.\mathrm{Ei}\,i\,y^* < A.\mathrm{value}$. The contrapositive is
exactly the missing direction: if $A.\mathrm{Ei}\,i\,y^* = A.\mathrm{value}$
then $x^*_i > 0$. Symmetric argument for columns. $\square$

## Remarks

- The shift in Step 1 is essential for the standard-form LP reduction;
  without it the value LP "max $v$" has $v$ free, which doesn't fit
  the `min ⟨c, x⟩ s.t. Ax ≥ b, x ≥ 0` form of
  [[node:math.linear_programming.strong_complementarity]].
- The Lean implementation restricts `I J : Type` (= `Type 0`) so the
  `Fintype.sum_equiv` adapter that bridges `I` and `Fin (#I)` lines up
  with the LP theorem's universe ($\mathbb{R} : \mathrm{Type}\,0$).
- Combined with [[node:game_theory.strategic_game.zero_sum.core.support_complementarity]] this
  produces a *fully two-sided* biconditional in the strong pair: every
  best-response row has positive probability and every positive-probability
  row is a best response.

## References

- [MFoGT, Prop. 2.4.1(c)] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Existence of a strongly complementary optimal pair.
