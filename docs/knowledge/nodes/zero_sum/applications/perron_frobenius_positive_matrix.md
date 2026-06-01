---
id: game_theory.strategic_game.zero_sum.applications.perron_frobenius_positive_matrix
title: Perron-Frobenius For Positive Matrices
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
uses:
  - math.minimax.loomis_theorem
lean:
  modules:
    - EconCSLib.Math.LinearAlgebra.PerronFrobenius
  declarations:
    - EconCSLib.LinearAlgebra.perron_frobenius
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 1(2)"
      format: section
      note: "Application of Loomis theorem to positive matrices"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-algebra
  - perron-frobenius
  - zero-sum
---

# Perron-Frobenius For Positive Matrices

## Statement

Let $M \in \mathbb{R}^{n \times n}$ be a square matrix whose entries are
strictly positive: $M_{ij} > 0$ for every $i, j$. Then there exist
$x \in \Delta(\mathrm{Fin}\,n)$, $y \in \Delta(\mathrm{Fin}\,n)$, and
$\lambda > 0$ such that

- $x$ and $y$ have **strictly positive components**;
- $xM = \lambda\, x$ (so $x$ is a left eigenvector of $M$ with eigenvalue $\lambda$);
- $My = \lambda\, y$ (so $y$ is a right eigenvector of $M$ with eigenvalue $\lambda$).

The Loomis value $v$ of the pair $(I, M)$ (identity matrix vs. $M$)
provides $\lambda = 1/v$.

## Proof

Apply the general-$B$ Loomis theorem
([[node:math.minimax.loomis_theorem]]) with $A := I$ (the $n \times n$
identity matrix) and $B := M$. Since $M_{ij} > 0$, the hypothesis
`IsPositive M` is satisfied. Loomis produces
$x \in \Delta(\mathrm{Fin}\,n)$, $y \in \Delta(\mathrm{Fin}\,n)$, and
$v \in \mathbb{R}$ such that

- $(1)\quad \forall j,\quad v \cdot (xM)_j \le x_j$  (from $xI \ge v \cdot xM$,
  using $xI = x$);
- $(2)\quad \forall i,\quad y_i \le v \cdot (My)_i$  (from $Iy \le v \cdot My$,
  using $Iy = y$).

**Step 1: $v > 0$.** Pick $i_0$ with $y_{i_0} > 0$ (which exists because
$\sum y_i = 1$). Inequality (2) at $i_0$ gives
$y_{i_0} \le v \cdot (My)_{i_0}$. Since $M > 0$ entrywise and $y \ge 0$ has
$y_{i_0} > 0$ (hence $\sum y_j M_{i_0, j} > 0$), $(My)_{i_0} > 0$.
Therefore $0 < y_{i_0} \le v \cdot (My)_{i_0}$ forces $v > 0$.

**Step 2: $x$ and $y$ are strictly positive.** For every $j$,
$(xM)_j = \sum_i x_i M_{ij} > 0$ because $x \in \Delta$ has at least one
positive entry and $M > 0$ entrywise. Combined with (1), $x_j \ge v \cdot
(xM)_j > 0$. So $x_j > 0$ for all $j$. By the same argument applied to (2)
and $y$, $(My)_i > 0$ and $y_i > 0$ for all $i$.

**Step 3: Tight inner-product sandwich.** Compute
$$
  \langle x, y\rangle - v\cdot \langle xM, y\rangle
  = \sum_j (x_j - v \cdot (xM)_j) \cdot y_j \ge 0
$$
(each summand is nonneg by (1) and $y_j \ge 0$). And by
$\langle xM, y\rangle = \sum_j \sum_i x_i M_{ij} y_j = \langle x, My\rangle$,
$$
  v \cdot \langle x, My\rangle - \langle x, y\rangle
  = v \cdot \langle x, My\rangle - \langle x, y\rangle.
$$
Weighting (2) by $x \ge 0$ and summing,
$\langle x, y\rangle \le v \cdot \langle x, My\rangle$. Therefore
$$
  \langle x, y\rangle \;\ge\; v \cdot \langle xM, y\rangle \;=\; v \cdot \langle x, My\rangle \;\ge\; \langle x, y\rangle,
$$
so both inequalities are tight.

**Step 4: Componentwise equality.** From Step 3,
$\sum_j (x_j - v \cdot (xM)_j) \cdot y_j = 0$. Each summand is nonneg (by
(1)) and $y_j > 0$ strict (by Step 2). For the nonneg sum to vanish, each
summand must vanish, so $x_j - v \cdot (xM)_j = 0$, i.e., $x_j = v \cdot
(xM)_j$ for every $j$. As a row-vector identity, $xM = (1/v) \cdot x$.

Dually, $\sum_i (v \cdot (My)_i - y_i) \cdot x_i = 0$ with each summand
nonneg and $x_i > 0$ strict, so $y_i = v \cdot (My)_i$, i.e.,
$My = (1/v) \cdot y$.

Setting $\lambda := 1/v > 0$, we have $xM = \lambda \cdot x$ (left
eigenvector) and $My = \lambda \cdot y$ (right eigenvector), both with
$x, y$ strictly positive. $\square$

## Remarks

- The argument is purely algebraic and works over $\mathbb{R}$ (where
  general-$B$ Loomis is formalised in `EconCSLib.StrategicGame.Loomis`).
- Strict positivity of $x$ and $y$ is automatic given strict positivity of
  $M$, **without** needing a separate "irreducibility" argument.
- The same Loomis instance simultaneously produces the **left** eigenvector
  $x$ and the **right** eigenvector $y$ at the same eigenvalue $\lambda
  = 1/v$. This eigenvalue is the **Perron-Frobenius eigenvalue** of $M$.

## References

- [MFoGT, Section 2.8, Exercise 1(2)] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Application of Loomis theorem
  to positive matrices.
