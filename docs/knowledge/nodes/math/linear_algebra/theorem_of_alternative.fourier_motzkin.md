---
id: math.linear_algebra.theorem_of_alternative.fourier_motzkin
title: Fourier-Motzkin Elimination Step
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.linear_algebra
  - math.linear_algebra.alternatives
lean:
  modules:
    - EconCSLib.Math.LinearAlgebra.FourierMotzkin
  declarations:
    - ZeroRows
    - PosRows
    - NegRows
    - FMRowIndex
    - fmA
    - fmB
    - fm_feasible_of_feasible
    - feasible_of_fm_feasible
    - liftCoeff
    - liftCert
    - fm_cert_lift
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 7"
      format: section
      note: "Single-variable Fourier-Motzkin elimination underlying the theorem of the alternative"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - linear-algebra
  - fourier-motzkin
  - alternatives
  - elimination
---

# Fourier-Motzkin Elimination Step

The combinatorial workhorse of the theorem of the alternative
([[node:math.linear_algebra.theorem_of_alternative]]): a single Fourier-Motzkin
elimination step replaces one variable by an enlarged but lower-dimensional
system whose feasibility coincides with the original's, and whose Farkas
certificates lift constructively to the original.

## Setup

Fix a linearly ordered field $\mathbb{K}$, a finite index $I$, and a
finite column set $J$ with a distinguished column $j^\star \in J$. Set
$J' = J \setminus \{j^\star\}$. Given $A \colon I \times J \to \mathbb{K}$
and $b \colon I \to \mathbb{K}$, partition $I$ by the sign of the
$j^\star$-coefficient:
$$
  I^0 = \{ i : A_{i, j^\star} = 0 \},\quad
  I^+ = \{ i : A_{i, j^\star} > 0 \},\quad
  I^- = \{ i : A_{i, j^\star} < 0 \}.
$$
Define the **reduced index** $I' = I^0 \sqcup (I^+ \times I^-)$, the
reduced matrix $A' \colon I' \times J' \to \mathbb{K}$, and the reduced
RHS $b' \colon I' \to \mathbb{K}$ by

- **$I^0$ rows** (pass-through). For $k \in I^0$ and $j \in J'$,
  $$
    A'_{k, j} \;=\; A_{k, j}, \qquad b'_k \;=\; b_k.
  $$

- **$I^+ \times I^-$ rows** (combination). For $(p, q) \in I^+ \times I^-$
  and $j \in J'$, set $\alpha_q = -A_{q, j^\star} > 0$ and
  $\beta_p = A_{p, j^\star} > 0$; then
  $$
    A'_{(p,q), j} \;=\; \alpha_q\, A_{p, j} + \beta_p\, A_{q, j},
    \qquad
    b'_{(p,q)} \;=\; \alpha_q\, b_p + \beta_p\, b_q.
  $$

By construction, the $j^\star$-coefficient of any combination row is
$\alpha_q\, A_{p, j^\star} + \beta_p\, A_{q, j^\star}
= -A_{q, j^\star}\, A_{p, j^\star} + A_{p, j^\star}\, A_{q, j^\star} = 0$,
so the reduced matrix really has columns indexed only by $J'$.

## Statement

(i) **Feasibility transfer.** $S(A, b) \ne \emptyset \iff S(A', b') \ne
\emptyset$, where $S(\cdot, \cdot)$ denotes the primal feasibility region
of [[node:math.linear_algebra.theorem_of_alternative]].

(ii) **Certificate lift.** For every $u' \in T(A', b')$ there exists an
explicit $u \in T(A, b)$ given by
$$
  u_i \;=\; \begin{cases}
    u'_{\mathrm{inl}(i)} & \text{if } i \in I^0,\\
    \displaystyle\sum_{q \in I^-} \alpha_q \cdot u'_{(i, q)} & \text{if } i \in I^+,\\
    \displaystyle\sum_{p \in I^+} \beta_p \cdot u'_{(p, i)} & \text{if } i \in I^-,
  \end{cases}
$$
where the sums use the $\alpha_q$, $\beta_p$ coefficients defined above
(i.e. with $q$ ranging over $I^-$ and $p$ over $I^+$).

## Proof of (i): feasibility transfer

*($\Rightarrow$)* If $x \in S(A, b)$, set $x' = x|_{J'}$. Then for each
reduced row:

- For $k \in I^0$: $\sum_{j \in J'} A_{k,j}\, x'_j
  = \sum_{j \in J} A_{k,j}\, x_j$ (because $A_{k, j^\star} = 0$), so
  the $I^0$ inequality $\sum A_{k,j}\, x'_j \ge b'_k$ matches the original
  inequality at row $k$. ✓

- For $(p, q) \in I^+ \times I^-$: by linearity, the combined sum is
  $\alpha_q \cdot \sum_{j \in J} A_{p,j}\, x_j +
  \beta_p \cdot \sum_{j \in J} A_{q,j}\, x_j$ (the $j^\star$ terms cancel
  by construction). Bounding each by its RHS (rows $p$ and $q$ of $Ax \ge
  b$, with nonneg multipliers $\alpha_q, \beta_p > 0$):
  $\alpha_q \cdot b_p + \beta_p \cdot b_q = b'_{(p,q)}$. ✓

So $x' \in S(A', b')$.

*($\Leftarrow$)* Suppose $x' \in S(A', b')$. For each $i \in I^+$ set
$L_i(x') = (b_i - \sum_{j \in J'} A_{i,j}\, x'_j)/A_{i, j^\star}$; for
each $i \in I^-$ set $U_i(x') = (b_i - \sum_{j \in J'} A_{i,j}\, x'_j)/A_{i, j^\star}$
(division by a strictly negative scalar flips the corresponding
inequality direction; see below).

Define
$$
  L^\star = \max_{p \in I^+} L_p(x') \quad (-\infty\text{ if } I^+ = \emptyset),
  \qquad
  U^\star = \min_{q \in I^-} U_q(x') \quad (+\infty\text{ if } I^- = \emptyset).
$$
*Claim:* $L^\star \le U^\star$.

If $I^+$ or $I^-$ is empty the inequality is vacuous. Otherwise, fix any
$(p, q) \in I^+ \times I^-$; the reduced inequality at $(p, q)$ is
$\alpha_q\, A_{p,\cdot}\, x' + \beta_p\, A_{q,\cdot}\, x' \ge \alpha_q
b_p + \beta_p b_q$. Rearranging (using $\alpha_q = -A_{q,j^\star} > 0$ and
$\beta_p = A_{p, j^\star} > 0$):
$$
  \beta_p\, (b_q - A_{q,\cdot}\, x') \;\le\; -\alpha_q\, (b_p - A_{p,\cdot}\, x'),
$$
which, dividing by $\beta_p\, A_{p,j^\star}$ on one side and
$-\alpha_q\, A_{q, j^\star}$ on the other (both *positive* products since
$A_{p, j^\star} > 0$ and $A_{q, j^\star} < 0$ makes $-A_{q, j^\star} > 0$),
gives $L_p(x') \le U_q(x')$. Maximising over $p \in I^+$ and minimising
over $q \in I^-$ yields $L^\star \le U^\star$.

Pick any $x_{j^\star} \in [L^\star, U^\star]$ (nonempty by the claim).
For every $p \in I^+$: $x_{j^\star} \ge L_p(x')$, which (since
$A_{p, j^\star} > 0$) rearranges to $\sum_{j \in J} A_{p, j}\, x_j \ge
b_p$. Symmetrically for $q \in I^-$ (using $A_{q, j^\star} < 0$). For
$k \in I^0$, the row inequality is independent of $x_{j^\star}$ and was
already $\ge b_k = b'_k$ by hypothesis on $x'$.

So $x := (x', x_{j^\star}) \in S(A, b)$.

## Proof of (ii): certificate lift

Suppose $u' \in T(A', b')$: $u' \ge 0$, $(u')^{\mathsf T} A' = 0$, and
$\langle u', b'\rangle > 0$. Define $u$ as in the statement. We verify the
three Farkas conditions for $u$:

**$u \ge 0$.** Each $u_i$ is a sum of products of $u' \ge 0$ entries with
$\alpha_q, \beta_p > 0$ (or simply $u'_{\mathrm{inl}(i)} \ge 0$ for
$i \in I^0$). So $u_i \ge 0$.

**$u^{\mathsf T} A = 0$, i.e., $\sum_i u_i A_{i, j} = 0$ for every
$j \in J$.**

*Case $j \in J'$.* Expand the sum splitting $I = I^0 \cup I^+ \cup I^-$.
The $I^0$ part contributes $\sum_{k \in I^0} u'_{\mathrm{inl}(k)} A_{k,j}
= \sum_{k \in I^0} u'_{\mathrm{inl}(k)} A'_{\mathrm{inl}(k), j}$. The
$I^+$ part contributes $\sum_{p \in I^+} \left(\sum_{q \in I^-} \alpha_q
u'_{(p,q)}\right) A_{p, j}$, and the $I^-$ part contributes
$\sum_{q \in I^-} \left(\sum_{p \in I^+} \beta_p u'_{(p,q)}\right)
A_{q, j}$. Combining the latter two:
$$
  \sum_{(p,q) \in I^+\times I^-} u'_{(p,q)} \bigl(\alpha_q A_{p, j}
    + \beta_p A_{q, j}\bigr)
  = \sum_{(p,q)} u'_{(p,q)} A'_{(p,q), j}.
$$
The total is $(u')^{\mathsf T} A'$ at column $j$, which is $0$ since
$u' \in T(A', b')$. ✓

*Case $j = j^\star$.* The $I^0$ summands have $A_{k, j^\star} = 0$, so
contribute $0$. The $I^+$ contribution is
$\sum_{p \in I^+} \sum_{q \in I^-} \alpha_q u'_{(p,q)} A_{p, j^\star}
= \sum_{(p,q)} u'_{(p,q)} \alpha_q \beta_p$ (using
$\beta_p = A_{p, j^\star}$). The $I^-$ contribution is
$\sum_{q \in I^-} \sum_{p \in I^+} \beta_p u'_{(p,q)} A_{q, j^\star}
= \sum_{(p,q)} u'_{(p,q)} \beta_p \, (-\alpha_q)$ (using
$A_{q, j^\star} = -\alpha_q$). Sum: $\sum_{(p,q)} u'_{(p,q)} \alpha_q \beta_p
- \sum_{(p,q)} u'_{(p,q)} \alpha_q \beta_p = 0$. ✓

**$\langle u, b\rangle > 0$.** Repeat the $j$-by-$j$ argument with $b$ in
place of the $j$-column of $A$: the result is $\langle u', b'\rangle$,
which is $> 0$ by hypothesis.

This completes both transfer properties, hence the theorem of the
alternative is closed by induction on $|J|$. $\square$

## References

- [MFoGT, Section 2.8, Exercise 7] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Single-variable
  Fourier-Motzkin elimination as the inductive step of the theorem of
  the alternative.
