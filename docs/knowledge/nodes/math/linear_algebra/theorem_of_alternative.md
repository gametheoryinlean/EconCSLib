---
id: math.linear_algebra.theorem_of_alternative
title: Theorem Of The Alternative
kind: theorem
status: proved
primary_topic: math
topics:
  - math
  - math.linear_algebra
  - math.linear_algebra.alternatives
uses:
  - math.linear_algebra.theorem_of_alternative.fourier_motzkin
lean:
  modules:
    - EconCSLib.Math.LinearAlgebra.FourierMotzkin
  declarations:
    - EconCSLib.LinearAlgebra.rowEval
    - EconCSLib.LinearAlgebra.IsFeasible
    - EconCSLib.LinearAlgebra.IsCertificate
    - EconCSLib.LinearAlgebra.HasCertificate
    - EconCSLib.LinearAlgebra.feas_cert_disjoint
    - EconCSLib.LinearAlgebra.theorem_of_alternative
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 7"
      format: section
      note: "Fourier elimination theorem of the alternative"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-algebra
  - convexity
  - alternatives
  - fourier-motzkin
---

# Theorem Of The Alternative

## Setup

Fix a linearly ordered field $\mathbb{K}$ and finite nonempty index types
$I$ and $J$. Let $A \colon I \times J \to \mathbb{K}$ be a matrix and
$b \colon I \to \mathbb{K}$ a right-hand side vector. Define the
**primal feasibility region** and **Farkas certificate set**
$$
  S = S(A, b) \;=\; \{\, x \colon J \to \mathbb{K} \mid \forall i \in I,\;
      \textstyle\sum_{j \in J} A_{ij}\, x_j \ge b_i \,\},
$$
$$
  T = T(A, b) \;=\; \bigl\{\, u \colon I \to \mathbb{K} \,\big|\, u \ge 0,\;
      \forall j \in J,\, \textstyle\sum_{i \in I} u_i A_{ij} = 0,\;
      \textstyle\sum_{i \in I} u_i b_i > 0 \,\bigr\}.
$$

## Statement

**Theorem (of the alternative).** Exactly one of $S$ and $T$ is nonempty.

In particular,
$$
  S = \emptyset \quad\Longleftrightarrow\quad T \ne \emptyset.
$$

## Proof

The two halves are independent.

*Disjointness ($S$ and $T$ cannot both be nonempty).* Suppose $x \in S$ and
$u \in T$. Weighting the $I$ inequalities $Ax \ge b$ by the nonnegative
weights $u_i$ and summing:
$$
  \textstyle\sum_i u_i \sum_j A_{ij}\, x_j \;\ge\; \sum_i u_i b_i.
$$
The left-hand side rewrites as
$\sum_j x_j \sum_i u_i A_{ij} = \sum_j x_j \cdot 0 = 0$ (using
$u^{\mathsf T}A = 0$ from $u \in T$). The right-hand side is $> 0$ from
$\langle u, b\rangle > 0$. So $0 \ge \sum_i u_i b_i > 0$, contradiction.

*Existence (at least one of $S$, $T$ is nonempty).* By strong induction on
$n = |J|$.

**Base $n = 0$.** $J = \emptyset$, so the empty sum gives
$\sum_{j \in \emptyset} A_{ij}\,x_j = 0$ for every $i$. The constraints
$Ax \ge b$ become $0 \ge b_i$ for every $i$, i.e. $b \le 0$ componentwise.
The unique $x \colon \emptyset \to \mathbb{K}$ lives in $S$ iff $b \le 0$.

If $b \le 0$ then $S \ne \emptyset$. Otherwise, some $b_{i_0} > 0$; pick
$u = e_{i_0}$ (the indicator at $i_0$). Then $u \ge 0$, the matrix
constraint $u^{\mathsf T} A = 0$ is vacuous (no columns), and
$\sum_i u_i b_i = b_{i_0} > 0$, so $u \in T$ and $T \ne \emptyset$.

**Inductive step.** Suppose the theorem holds for any system on $n$
columns. Given a system $(A, b)$ on $J$ with $|J| = n + 1$, pick any
$j^\star \in J$ and apply Fourier-Motzkin elimination
([[node:math.linear_algebra.theorem_of_alternative.fourier_motzkin]]) to obtain
a reduced system $(A', b')$ on $J' = J \setminus \{j^\star\}$ (which has
$n$ columns) together with two transfer properties:

1. **Feasibility iff.** $S(A, b) \ne \emptyset \iff S(A', b') \ne \emptyset$.
2. **Certificate lift.** Every $u' \in T(A', b')$ explicitly produces a
   $u \in T(A, b)$.

By the inductive hypothesis applied to $(A', b')$, either $S(A', b')$ or
$T(A', b')$ is nonempty.

- If $S(A', b') \ne \emptyset$, then by (1) $S(A, b) \ne \emptyset$.
- If $T(A', b') \ne \emptyset$, then by (2) $T(A, b) \ne \emptyset$.

Either way, at least one of $S(A, b)$, $T(A, b)$ is nonempty. $\square$

## Remarks

- The proof is **constructive over $\mathbb{K}$**: the FM reduction is an
  explicit rational construction, and the certificate lift is an explicit
  nonnegative combination of the reduced certificate with finite-many
  matrix-entry coefficients. So if $A$, $b$ have entries in $\mathbb{K}$,
  the witness ($x$ or $u$) lives in $\mathbb{K}$ as well.
- No topology, completeness, or compactness is invoked. The theorem holds
  uniformly over every linearly ordered field, including $\mathbb{Q}$.
- The "exactly one" phrasing is the conjunction of disjointness and
  existence. In Lean it is convenient to state the equivalence
  $\neg\,S\text{-nonempty} \iff T\text{-nonempty}$.

## Consequences

This theorem is the gateway to several downstream results in the
LP / linear-algebra cluster:

- *Farkas' lemma*: re-expression in terms of "for every $x$, $Ax \ge b$
  implies $\langle c, x\rangle \ge d$ iff there is a dual certificate".
- *LP strong duality*: once Farkas is available, duality follows by
  combining primal feasibility and bounded objective.
- *Matrix-game polytope structure*: optimal strategy sets are
  intersections of the simplex with finitely many half-spaces.

## References

- [MFoGT, Section 2.8, Exercise 7] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Fourier elimination theorem
  of the alternative.
