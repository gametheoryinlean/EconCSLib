---
id: math.linear_algebra.farkas_lemma
title: Farkas Lemma
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.linear_algebra
  - math.linear_algebra.alternatives
uses:
  - math.linear_algebra.theorem_of_alternative
lean:
  modules:
    - EconCSLib.Math.LinearAlgebra.Farkas
  declarations:
    - FarkasAugRow
    - farkasAugA
    - farkasAugB
    - farkas_lemma
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 8"
      format: section
      note: "Farkas lemma derived from the theorem of the alternative"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-algebra
  - convexity
  - farkas
---

# Farkas Lemma

## Setup

Fix a linearly ordered field $\mathbb{K}$ and finite nonempty index types
$I$ (rows) and $J$ (columns). Let $A \colon I \times J \to \mathbb{K}$,
$b \colon I \to \mathbb{K}$, $c \colon J \to \mathbb{K}$, and
$d \in \mathbb{K}$. Set
$$
  S(A, b) \;=\; \{\, x \colon J \to \mathbb{K} \mid A x \ge b \,\}
$$
(componentwise weak inequality) and assume $S(A, b) \ne \emptyset$.

## Statement

The following are equivalent:

1. (Primal bound.) For every $x \in S(A, b)$, the objective $\langle c, x\rangle
   \ge d$.

2. (Dual certificate.) There exists $u \colon I \to \mathbb{K}$ with
   $u \ge 0$, $u^{\mathsf T} A = c$, and $\langle u, b\rangle \ge d$.

## Proof

The two directions:

*(2) $\Rightarrow$ (1).* Let $x \in S(A, b)$ and $u$ as in (2). Weighting
$A x \ge b$ by the nonnegative $u$ componentwise and summing,
$\langle u, A x\rangle \ge \langle u, b\rangle$. The left-hand side
rearranges to $\langle u^{\mathsf T} A, x\rangle = \langle c, x\rangle$ (by
$u^{\mathsf T} A = c$). The right-hand side is $\ge d$. Therefore
$\langle c, x\rangle \ge d$.

*(1) $\Rightarrow$ (2).* This is the substantive direction; the proof
homogenises the system and applies the Theorem of the Alternative
([[node:math.linear_algebra.theorem_of_alternative]]).

Consider the augmented system on $(x, t) \in (J \to \mathbb{K})
\times \mathbb{K}$ with row index $I \sqcup \{ t_+, c_+ \}$ (the original $I$
plus two extra rows):

- For each $i \in I$: $A_i x - b_i\, t \ge 0$.
- ($t_+$) $t \ge 0$.
- ($c_+$) $-\langle c, x\rangle + d\, t \ge 1$.

**Claim.** This augmented system is infeasible.

*Proof of claim.* Suppose $(x, t)$ satisfies all three. Two cases on $t$:

- $t = 0$. Then $A x \ge 0$ and $-\langle c, x\rangle \ge 1$, hence
  $\langle c, x\rangle \le -1$. Pick $y \in S(A, b)$ (using the hypothesis
  $S \ne \emptyset$). For every $\lambda > 0$ in $\mathbb{K}$,
  $A(y + \lambda x) = A y + \lambda A x \ge b + 0 = b$, so
  $y + \lambda x \in S(A, b)$. By (1),
  $\langle c, y + \lambda x\rangle = \langle c, y\rangle + \lambda
  \langle c, x\rangle \ge d$. But $\langle c, x\rangle \le -1$, so
  $\langle c, y\rangle - \lambda \ge d$, i.e.,
  $\lambda \le \langle c, y\rangle - d$. This bound is independent of
  $\lambda$ — taking any $\lambda > \langle c, y\rangle - d$ contradicts
  the inequality. Hence the case $t = 0$ is impossible.

- $t > 0$. Then $x' := x / t \colon J \to \mathbb{K}$ satisfies
  $A x' = A x / t \ge b$ (divide $A x \ge b\, t$ by $t > 0$), so
  $x' \in S(A, b)$. By (1), $\langle c, x'\rangle \ge d$. But $(c_+)$ gives
  $-\langle c, x\rangle + d\, t \ge 1$, so
  $\langle c, x'\rangle = \langle c, x\rangle / t \le d - 1/t < d$ (since
  $t > 0$, so $1/t > 0$). Contradiction.

Hence the augmented system is infeasible.

**Apply ToA.** By [[node:math.linear_algebra.theorem_of_alternative]], there is a
Farkas-style certificate $u' \colon I \sqcup \{t_+, c_+\} \to \mathbb{K}$
with $u' \ge 0$, $(u')^{\mathsf T} (A_{\mathrm{aug}}) = 0$ on every column
of the augmented system, and $\langle u', b_{\mathrm{aug}}\rangle > 0$
(where $b_{\mathrm{aug}}$ has $0$ on the $I$ and $t_+$ rows and $1$ on the
$c_+$ row).

Decompose $u' = (u, \alpha, \beta)$ with $u \colon I \to \mathbb{K}$,
$\alpha = u'(t_+)$, $\beta = u'(c_+)$.

Read off the column conditions:

- (column $j$ for $x_j$, $j \in J$):
  $\sum_i u_i A_{i,j} + \alpha \cdot 0 + \beta \cdot (-c_j) = 0$, i.e.,
  $u^{\mathsf T} A = \beta \cdot c$.
- (column for $t$): $\sum_i u_i (-b_i) + \alpha \cdot 1 + \beta \cdot d = 0$,
  i.e., $\langle u, b\rangle = \alpha + \beta\, d$.

RHS positivity reads $\beta > 0$ (the $I$ and $t_+$ rows contribute $0$
to the inner product, and the $c_+$ row contributes $\beta \cdot 1$).

Since $\beta > 0$, divide: set $\tilde u := u / \beta$. Then

- $\tilde u \ge 0$ (from $u \ge 0$ and $\beta > 0$),
- $\tilde u^{\mathsf T} A = c$ (from $u^{\mathsf T} A = \beta\, c$),
- $\langle \tilde u, b\rangle = \langle u, b\rangle / \beta
  = \alpha / \beta + d \ge d$ (since $\alpha \ge 0$ and $\beta > 0$).

So $\tilde u$ witnesses (2). $\square$

## Remarks

- The proof is purely algebraic and constructive: the Farkas certificate
  $\tilde u$ is built explicitly from the Theorem of the Alternative
  witness produced by Fourier-Motzkin elimination.
- Works over any linearly ordered field, in particular over $\mathbb{Q}$
  (with rational matrix and objective, the certificate is rational).
- The hypothesis $S(A, b) \ne \emptyset$ is essential: if $S$ is empty, the
  primal-bound condition (1) is vacuously true for any $d$, but the dual
  certificate (2) need not exist (it would need to additionally certify
  infeasibility of the primal). The non-emptiness hypothesis is the
  standard Farkas "feasibility precondition".

## Consequences

This is the gateway to:

- LP strong duality: the primal LP $\min \langle c, x\rangle$ subject to
  $A x \ge b$ has the same optimal value as the dual LP
  $\max \langle u, b\rangle$ subject to $u \ge 0$, $u^{\mathsf T} A = c$.
- LP strong complementarity: existence of optimal primal-dual pairs with
  strict complementary slackness.
- Matrix-game polytope structure: optimal strategy sets are polytopes
  (intersections of the simplex with finitely many half-spaces, each of
  which has a Farkas-style certificate).

## References

- [MFoGT, Section 2.8, Exercise 8] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Farkas lemma derived from
  the theorem of the alternative.
