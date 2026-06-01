---
id: math.minimax.loomis_induction_proof.row_drop
title: Row-Drop Step of Loomis Induction
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - math.minimax.loomis_induction_proof.positive_aggregate
  - math.minimax.loomis_induction_proof.column_drop
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.loomis_value_eq_aux
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 1"
      format: section
      note: "Row-drop inductive step in the direct Loomis proof"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - induction
---

# Row-Drop Step of Loomis Induction

Dual to [[node:math.minimax.loomis_induction_proof.column_drop]]: a
strict row inequality in the optimiser of $A$ forces a contradiction by
mixing with the inductive optimiser of a row-restricted game.

## Setup

Fix $A, B \colon I \times J \to \mathbb{R}$ with $B$ entrywise positive and
$|I| + |J| \ge 3$. Use $x_0, y_0, \lambda_0, \mu_0$ as in
[[node:math.minimax.loomis_induction_proof.value_existence]].

**Induction hypothesis.** Every pair $(A', B')$ on $(I', J)$ with
$I' \subsetneq I$ satisfies $\lambda_0(A', B') = \mu_0(A', B')$.

## Statement

Suppose $\lambda_0 < \mu_0$ and there exists $i_0 \in I$ with
$$
  (A y_0)_{i_0} \;<\; \mu_0 \,(B y_0)_{i_0}.
$$
Then a contradiction follows.

## Proof

The argument is dual to
[[node:math.minimax.loomis_induction_proof.column_drop]]. We sketch the
correspondences and record the sign flips:

- $|I| \ge 2$: if $|I| = 1$ then $i_0$ is the unique row and
  $\mu_\mathrm{aux}(y_0) = (A y_0)_{i_0} / (B y_0)_{i_0} < \mu_0$,
  contradicting $\mu_\mathrm{aux}(y_0) \ge \mu_0$. So $I' := I \setminus
  \{i_0\}$ is nonempty.

- Restricted game $(A', B')$ on $(I', J)$. $B'$ stays entrywise positive
  and $|I'| + |J| < |I| + |J|$, so the induction hypothesis applies:
  $\lambda_0' = \mu_0'$.

- Extending $x' \in \Delta(I')$ by $0$ at $i_0$ yields $\tilde x \in
  \Delta(I)$ with
  $$
    (\tilde x A)_j = (x' A')_j,\qquad
    (\tilde x B)_j = (x' B')_j.
  $$
  So $\lambda_\mathrm{aux}(\tilde x) = \lambda_\mathrm{aux}^{(A',B')}(x')$ and
  $\lambda_0' \le \lambda_0$.

- Combined with the inductive equality and the hypothesis,
  $\mu_0' = \lambda_0' \le \lambda_0 < \mu_0$, so $\mu_0' < \mu_0$.

- Let $y' \in \Delta(J)$ be the inductive optimiser of $(A', B')$, so
  $(A' y')_i \le \mu_0' (B' y')_i$ for every $i \in I'$. Set
  $y_\alpha = \alpha y' + (1 - \alpha) y_0 \in \Delta(J)$.

  *For $i \in I'$:*
  $$
    (A y_\alpha)_i
    \le \alpha \mu_0'(B y')_i + (1 - \alpha)\mu_0 (B y_0)_i
    = \mu_0 (B y_\alpha)_i - \alpha (\mu_0 - \mu_0')(B y')_i.
  $$
  The subtracted term is strictly positive when $\alpha > 0$ (using
  $\mu_0 > \mu_0'$ and $(By')_i > 0$ by
  [[node:math.minimax.loomis_induction_proof.positive_aggregate]]), so
  $(A y_\alpha)_i < \mu_0 (B y_\alpha)_i$.

  *For $i = i_0$:* the affine function
  $\alpha \mapsto (A y_\alpha)_{i_0} - \mu_0 (B y_\alpha)_{i_0}$ is
  continuous and strictly negative at $\alpha = 0$, so it remains strictly
  negative on a neighborhood $[0, \alpha^*)$. Pick any
  $\alpha \in (0, \min(\alpha^*, 1))$.

- For the chosen $\alpha$, $(A y_\alpha)_i < \mu_0 (B y_\alpha)_i$ for every
  $i \in I$, giving $\mu_\mathrm{aux}(y_\alpha) < \mu_0$ and contradicting
  the definition of $\mu_0$ as an infimum.

$\square$

## References

- [MFoGT, Section 2.8, Exercise 1] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Row-drop inductive step in the direct Loomis proof.
