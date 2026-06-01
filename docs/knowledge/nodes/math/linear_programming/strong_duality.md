---
id: math.linear_programming.strong_duality
title: Strong Duality For Linear Programming
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.duality
uses:
  - math.linear_algebra.farkas_lemma
lean:
  modules:
    - EconCSLib.Math.LinearProgramming.StrongDuality
  declarations:
    - EconCSLib.LinearProgramming.PrimalFeasible
    - EconCSLib.LinearProgramming.DualFeasible
    - EconCSLib.LinearProgramming.lp_weak_duality
    - EconCSLib.LinearProgramming.DualAugRow
    - EconCSLib.LinearProgramming.dualAugA
    - EconCSLib.LinearProgramming.dualAugB
    - EconCSLib.LinearProgramming.isFeasible_dualAug_iff
    - EconCSLib.LinearProgramming.lp_strong_duality
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 9"
      format: section
      note: "Primal-dual strong duality for linear programming"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-programming
  - duality
---

# Strong Duality For Linear Programming

## Setup

Fix a linearly ordered field $\mathbb{K}$, a finite nonempty index type $I$,
and $n \in \mathbb{N}$. Let $A \colon I \times \mathrm{Fin}\,n \to \mathbb{K}$,
$b \colon I \to \mathbb{K}$, $c \colon \mathrm{Fin}\,n \to \mathbb{K}$.
Consider the **standard-form linear programming pair**:

- **Primal** $\mathrm{P}$:  $\min \langle c, x\rangle$ subject to
  $A x \ge b$ and $x \ge 0$ (i.e. $x_j \ge 0$ for every $j \in \mathrm{Fin}\,n$).
- **Dual** $\mathrm{D}$:  $\max \langle u, b\rangle$ subject to
  $u^{\mathsf T} A \le c$ (componentwise, i.e. $\sum_i u_i A_{ij} \le c_j$ for
  every $j$) and $u \ge 0$.

## Statements

**Weak duality.** For every primal-feasible $x$ and dual-feasible $u$,
$\langle c, x\rangle \ge \langle u, b\rangle$.

**Strong duality.** If the primal is feasible and bounded below by
$d \in \mathbb{K}$ (i.e. $\langle c, x\rangle \ge d$ for every primal-feasible
$x$), then there exists a dual-feasible $u$ with $\langle u, b\rangle \ge d$.

Combining the two yields that the optimal primal and dual values coincide when
either exists.

## Proof

### Weak duality

Let $x$ be primal-feasible and $u$ dual-feasible. Weighting the primal
constraints by $u \ge 0$:
$$
  \langle u, A x\rangle = \langle u^{\mathsf T} A, x\rangle \le \langle c, x\rangle
$$
(using $u^{\mathsf T} A \le c$ and $x \ge 0$, so weighting term by term
preserves $\le$). And $\langle u, A x\rangle \ge \langle u, b\rangle$ from
$A x \ge b$ and $u \ge 0$. Hence $\langle c, x\rangle \ge \langle u, b\rangle$.

### Strong duality

Apply the Farkas lemma ([[node:math.linear_algebra.farkas_lemma]]) to the
**augmented system** that combines $A x \ge b$ and $x \ge 0$. Concretely,
define $A_{\mathrm{aug}} \colon (I \sqcup \mathrm{Fin}\,n) \times \mathrm{Fin}\,n
\to \mathbb{K}$ and $b_{\mathrm{aug}} \colon I \sqcup \mathrm{Fin}\,n \to \mathbb{K}$
by

- $A_{\mathrm{aug}}(\mathrm{inl}\,i,\, j) = A_{i,j}$,
  $b_{\mathrm{aug}}(\mathrm{inl}\,i) = b_i$ for $i \in I$ (the original rows);
- $A_{\mathrm{aug}}(\mathrm{inr}\,j',\, j) = [j = j']$
  (Kronecker delta) and $b_{\mathrm{aug}}(\mathrm{inr}\,j') = 0$ for
  $j' \in \mathrm{Fin}\,n$ (the unit rows $x_{j'} \ge 0$).

Primal feasibility coincides with feasibility of $A_{\mathrm{aug}}\,x \ge
b_{\mathrm{aug}}$. By hypothesis, the primal is feasible and bounded below by
$d$. Farkas yields $u_{\mathrm{aug}} \colon I \sqcup \mathrm{Fin}\,n \to \mathbb{K}$
with $u_{\mathrm{aug}} \ge 0$, $u_{\mathrm{aug}}^{\mathsf T} A_{\mathrm{aug}} = c$,
and $\langle u_{\mathrm{aug}}, b_{\mathrm{aug}}\rangle \ge d$.

Decompose $u_{\mathrm{aug}} = (u, v)$ with $u \colon I \to \mathbb{K}$ and
$v \colon \mathrm{Fin}\,n \to \mathbb{K}$. The column conditions read

- For each $j \in \mathrm{Fin}\,n$:
  $\sum_i u_i A_{i,j} + \sum_{j'} v_{j'} [j = j'] = c_j$, i.e.
  $u^{\mathsf T} A\, j + v_j = c_j$, i.e. $u^{\mathsf T} A = c - v$. Since
  $v \ge 0$, $u^{\mathsf T} A \le c$.

The RHS condition reads
$$
  \langle u_{\mathrm{aug}}, b_{\mathrm{aug}}\rangle
    = \langle u, b\rangle + \langle v, 0\rangle = \langle u, b\rangle \ge d.
$$

So $u \ge 0$, $u^{\mathsf T} A \le c$ (dual feasibility), and
$\langle u, b\rangle \ge d$. This is the required dual-feasible point with
dual objective at least $d$.

## Remarks

- The proof is purely algebraic and constructive: the dual certificate $u$ is
  built explicitly from the Farkas certificate of the augmented system.
- Works over any linearly ordered field (in particular $\mathbb{Q}$).
- "Optimal value" is not used as a primitive; instead, the theorem is phrased
  for any lower bound $d$. The primal optimum is recovered by combining strong
  duality with weak duality:
  $$
    \sup_{u \text{ dual-feasible}} \langle u, b\rangle
      \;\ge\; d \quad\text{whenever}\quad d \le \inf_{x \text{ primal-feasible}}\langle c, x\rangle,
  $$
  and weak duality gives the converse inequality.

## Consequences

- **Complementary slackness**: optimal primal-dual pairs satisfy strict slack
  conditions on every variable (downstream from this theorem).
- **Matrix-game value**: zero-sum value computed via row and column LPs
  (downstream from this theorem).

## References

- [MFoGT, Section 2.8, Exercise 9] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Primal-dual strong duality for linear programming.
