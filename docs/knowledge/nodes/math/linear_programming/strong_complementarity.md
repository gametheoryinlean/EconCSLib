---
id: math.linear_programming.strong_complementarity
title: Strong Complementarity For Linear Programming
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.linear_programming
  - math.linear_programming.duality
uses:
  - math.linear_programming.strong_duality
  - math.linear_algebra.farkas_lemma
lean:
  modules:
    - EconCSLib.Math.LinearProgramming.StrongComplementarity
  declarations:
    - EconCSLib.LinearProgramming.lp_weak_complementarity_row
    - EconCSLib.LinearProgramming.lp_weak_complementarity_col
    - EconCSLib.LinearProgramming.exists_row_strict_pair
    - EconCSLib.LinearProgramming.exists_col_strict_pair
    - EconCSLib.LinearProgramming.exists_strong_complementary_pair
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 11"
      format: section
      note: "Strong complementarity for feasible primal-dual linear programs"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-programming
  - duality
  - complementarity
---

# Strong Complementarity For Linear Programming

## Setup

For the standard-form primal/dual pair over a linearly ordered field
$\mathbb{K}$:

- **Primal** $\mathrm{P}$: $\min \langle c, x\rangle$ subject to $Ax \ge b$ and $x \ge 0$.
- **Dual** $\mathrm{D}$: $\max \langle u, b\rangle$ subject to $u^{\mathsf T} A \le c$ and $u \ge 0$.

## Statements

### Weak complementary slackness

For **every** optimal primal–dual pair $(x, u)$ (i.e. $x$ primal-feasible,
$u$ dual-feasible, $\langle c, x\rangle = \langle u, b\rangle$), the
componentwise products vanish:

- for every row $i$: $u_i \cdot (A_i x - b_i) = 0$;
- for every column $j$: $x_j \cdot (c_j - u^{\mathsf T} A_j) = 0$.

Equivalently, strict primal slack at row $i$ forces $u_i = 0$, and strict
dual slack at column $j$ forces $x_j = 0$.

### Strong complementary slackness

If both $\mathrm{P}$ and $\mathrm{D}$ are feasible (so that strong duality
gives a matching optimal pair), then there **exist** optimal $(x^*, u^*)$
satisfying the strict biconditional:

- for every row $i$: $(A_i x^* - b_i) > 0 \iff u^*_i = 0$;
- for every column $j$: $(c_j - (u^*)^{\mathsf T} A_j) > 0 \iff x^*_j = 0$.

Equivalently, **exactly one** of each complementary pair is strictly
positive in the strong pair. Combined with weak CS, this is the same as
the "strict sum" form

$$
  (A_i x^* - b_i) + u^*_i > 0
  \quad \text{and} \quad
  x^*_j + (c_j - (u^*)^{\mathsf T} A_j) > 0
  \quad \text{for every } i, j,
$$

which is the shape stated in the Lean theorem
`EconCSLib.LinearProgramming.exists_strong_complementary_pair`. The Lean
theorem is parametrized by an explicit optimal pair $(x_0, u_0)$ with
matching value $v$ (rather than "P and D feasible") to keep the lemma
reusable; the "feasibility" hypothesis form follows by composing with
[[node:math.linear_programming.strong_duality]].

## Proof

### Weak CS

Take any optimal pair $(x, u)$. Compute
$$
  \sum_i u_i\,(A_i x - b_i) + \sum_j x_j\,(c_j - u^{\mathsf T} A_j)
   = \langle u, Ax\rangle - \langle u, b\rangle
     + \langle c, x\rangle - \langle u^{\mathsf T} A, x\rangle
   = \langle c, x\rangle - \langle u, b\rangle = 0,
$$
using bilinearity (the cross terms cancel) and primal/dual optimality.
Each summand on the left is $\ge 0$ (a nonneg variable times a nonneg
slack), so each is exactly $0$.

### Strong CS

The proof has two parts: a **per-index dichotomy** (one optimal pair
strictly positive on the chosen complementary pair) and an **averaging
step** that combines $|I| + n$ per-index pairs.

**Per-row dichotomy.** Fix $i_0 \in I$. Consider the sub-LP

$$
  \alpha_{i_0} \;:=\; \sup\{\,(Ax - b)_{i_0} \;:\; Ax \ge b,\; x \ge 0,\; \langle c, x\rangle \le v^*\,\}
$$

where $v^*$ is the common primal–dual optimum. Either:

- **Case A**: $\alpha_{i_0} > 0$. Then there is a primal-optimal $x^*$
  with $(A x^* - b)_{i_0} > 0$. Pair $(x^*, u^0)$ with any dual-optimal
  $u^0$.
- **Case B**: $\alpha_{i_0} = 0$. Then $(Ax-b)_{i_0} \le 0$ on every
  primal-optimal $x$. Apply
  [[node:math.linear_algebra.farkas_lemma]] to the system $\{Ax \ge b,
  x \ge 0, -\langle c, x\rangle \ge -v^*\}$ with the implied bound
  $(Ax - b)_{i_0} \le 0$. The Farkas certificate produces multipliers
  $(\mu, \nu, \lambda) \ge 0$ with
  $$
    (\mu + e_{i_0})^{\mathsf T} A \le \lambda \cdot c, \quad
    \langle \mu, b\rangle + b_{i_0} \ge \lambda \cdot v^*.
  $$
  If $\lambda > 0$, set $u'' := (\mu + e_{i_0})/\lambda$: dual-feasible
  with $u''_{i_0} \ge 1/\lambda > 0$ and $\langle u'', b\rangle \ge v^*$.
  If $\lambda = 0$, set $u' := u^0 + (\mu + e_{i_0})$ for any
  dual-optimal $u^0$: dual-feasible with $u'_{i_0} \ge 1 > 0$ and
  $\langle u', b\rangle = v^* + \langle \mu, b\rangle + b_{i_0} \ge v^*$.
  In each case, combined with weak duality the new $u$ is dual-optimal,
  and pair $(x^0, u)$ with any primal-optimal $x^0$ is the desired pair.

**Per-column dichotomy.** Symmetric, exchanging roles of $x$ and $u$.

**Averaging.** Take the witness pairs $(x^{(i)}, u^{(i)})$ for each
$i \in I$ and $(x^{(j)}, u^{(j)})$ for each $j \in \mathrm{Fin}\,n$ — a
total of $|I| + n$ optimal pairs. Define

$$
  x^* := \frac{1}{|I| + n} \sum_{\text{indices}} x^{(\cdot)}, \qquad
  u^* := \frac{1}{|I| + n} \sum_{\text{indices}} u^{(\cdot)}.
$$

Each set of optimal primal (resp. dual) solutions is convex (a polytope
in the standard-form LP), so $x^*, u^*$ are optimal. For any fixed row
$k$, at index $i_0 = k$ we picked a pair with
$(Ax^{(k)} - b)_k + u^{(k)}_k > 0$. Hence

$$
  (A x^* - b)_k + u^*_k \;=\; \frac{1}{|I|+n} \sum (A x^{(\cdot)} - b)_k + u^{(\cdot)}_k
  \;\ge\; \frac{1}{|I|+n} \cdot \big((A x^{(k)} - b)_k + u^{(k)}_k\big) > 0,
$$

with the other terms nonneg. Symmetric for columns. So $(x^*, u^*)$ is
strictly complementary on every row and column pair. By weak CS, exactly
one side of each complementary pair is positive — the desired
biconditional. $\square$

## Remarks

- The proof is purely algebraic and constructive. The dual certificates
  in the per-index step come from
  [[node:math.linear_algebra.farkas_lemma]] (which in turn rests on
  Fourier–Motzkin elimination, in `EconCSLib.LinearAlgebra`).
- Works over any linearly ordered field — same generality as
  [[node:math.linear_programming.strong_duality]].
- The weak-CS direction (`exactly one of each pair is positive`) is
  immediate; the strong content is the *existence of a pair where
  every complementary pair has at least one strict side*.

## Consequences

- **Matrix-game strong complementarity** (downstream node
  `zero_sum.minimax.strong_complementarity`, [MFoGT Prop. 2.4.1(c)]): in a
  finite zero-sum matrix game, there is an optimal pair $(x^*, y^*)$
  with the strict biconditional `x*_i > 0 ↔ row i is a best response to y*`
  and dually. Obtained by applying this theorem to the matrix-game LP
  (after shifting payoffs to be positive and rescaling).

## References

- [MFoGT, Section 2.8, Exercise 11] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Strong complementarity
  for feasible primal-dual linear programs.
