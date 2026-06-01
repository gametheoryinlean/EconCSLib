---
id: math.minimax.loomis_induction_proof.column_drop
title: Column-Drop Step of Loomis Induction
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - math.minimax.loomis_induction_proof.positive_aggregate
  - math.minimax.loomis_induction_proof.value_existence
  - math.minimax.loomis_induction_proof.weak_duality
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
      note: "Column-drop inductive step in the direct Loomis proof"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - induction
---

# Column-Drop Step of Loomis Induction

The first of the two symmetric inductive steps in
[[node:math.minimax.loomis_induction_proof]]: a strict column inequality
in the optimiser of $A$ forces a contradiction by mixing with the inductive
optimiser of a column-restricted game.

## Setup

Fix $A, B \colon I \times J \to \mathbb{R}$ with $B$ entrywise positive and
$|I| + |J| \ge 3$. Let $x_0 \in \Delta(I)$ and $y_0 \in \Delta(J)$ be the
optimisers from
[[node:math.minimax.loomis_induction_proof.value_existence]], and use
$\lambda_0, \mu_0$ as defined there.

**Induction hypothesis.** Every pair $(A', B')$ on smaller index types — in
particular on $(I, J')$ with $J' \subsetneq J$ — satisfies the equality
$\lambda_0(A', B') = \mu_0(A', B')$.

## Statement

Suppose $\lambda_0 < \mu_0$ and there exists $j_0 \in J$ with
$$
  (x_0 A)_{j_0} \;>\; \lambda_0 \,(x_0 B)_{j_0}.
$$
Then a contradiction follows. (Symmetrically: this strict-column situation
cannot coexist with $\lambda_0 < \mu_0$.)

## Proof

**Step 1: $|J| \ge 2$.** If $|J| = 1$ then $j_0$ is the unique column and
$$
  \lambda_\mathrm{aux}(x_0) = \frac{(x_0 A)_{j_0}}{(x_0 B)_{j_0}}
  > \lambda_0,
$$
contradicting $\lambda_\mathrm{aux}(x_0) \le \lambda_0$. So $|J| \ge 2$ and
$J' := J \setminus \{j_0\}$ is nonempty.

**Step 2: Restricted game.** Let $A', B' \colon I \times J' \to \mathbb{R}$
be the restrictions of $A, B$ to $J'$. Then $B'$ is still entrywise
positive, and $|I| + |J'| = |I| + |J| - 1 < |I| + |J|$. By induction
hypothesis, $\lambda_0' = \mu_0'$ where $\lambda_0', \mu_0'$ are the Loomis
scalars of $(A', B')$.

**Step 3: $\mu_0 \le \mu_0'$.** For any $y' \in \Delta(J')$, define
$\tilde y \in \Delta(J)$ by extending $y'$ with $0$ at $j_0$. Then
$$
  (A \tilde y)_i = \sum_{j \in J'} A_{ij}\, y'_j = (A' y')_i,
  \qquad
  (B \tilde y)_i = (B' y')_i,
$$
so $\mu_\mathrm{aux}(\tilde y) = \mu_\mathrm{aux}^{(A',B')}(y')$. In particular
$\mu_0 \le \mu_\mathrm{aux}(\tilde y) = \mu_\mathrm{aux}^{(A',B')}(y')$.
Taking the infimum over $y' \in \Delta(J')$ gives $\mu_0 \le \mu_0'$.

**Step 4: $\lambda_0 < \lambda_0'$.** Combining Step 3 with the inductive
equality and the hypothesis,
$$
  \lambda_0 \;<\; \mu_0 \;\le\; \mu_0' \;=\; \lambda_0'.
$$

**Step 5: Inductive optimiser $x'$.** By
[[node:math.minimax.loomis_induction_proof.value_existence]] applied to
$(A', B')$ there exists $x' \in \Delta(I)$ with
$$
  (x' A)_j \ge \lambda_0' \,(x' B)_j
  \qquad\text{for every } j \in J'.
$$
(Strategies on $I$ for $(A', B')$ live in the same simplex $\Delta(I)$.)

**Step 6: Convex combination.** For $\alpha \in [0, 1]$ set
$x_\alpha = \alpha x' + (1 - \alpha) x_0 \in \Delta(I)$. By bilinearity of
$(\cdot, A)$ and $(\cdot, B)$, for every $j \in J$
$$
  (x_\alpha A)_j = \alpha (x' A)_j + (1 - \alpha)(x_0 A)_j, \qquad
  (x_\alpha B)_j = \alpha (x' B)_j + (1 - \alpha)(x_0 B)_j.
$$

*Sub-case $j \in J'$.* Using Step 5 and the $x_0$-inequality at $\lambda_0$:
$$
  (x_\alpha A)_j
  \ge \alpha \lambda_0'(x'B)_j + (1 - \alpha) \lambda_0 (x_0 B)_j
  = \lambda_0 (x_\alpha B)_j + \alpha(\lambda_0' - \lambda_0)(x'B)_j.
$$
The extra term $\alpha(\lambda_0' - \lambda_0)(x'B)_j$ is strictly positive
when $\alpha > 0$ (Step 4 plus $(x'B)_j > 0$ by
[[node:math.minimax.loomis_induction_proof.positive_aggregate]]). So for
every $\alpha \in (0, 1]$ and every $j \ne j_0$,
$$
  (x_\alpha A)_j \;>\; \lambda_0 (x_\alpha B)_j. \tag{*}
$$

*Sub-case $j = j_0$.* The function
$\alpha \mapsto (x_\alpha A)_{j_0} - \lambda_0 (x_\alpha B)_{j_0}$ is
affine, hence continuous. At $\alpha = 0$ it equals
$(x_0 A)_{j_0} - \lambda_0 (x_0 B)_{j_0}$, which is strictly positive by
hypothesis. Therefore there exists $\alpha^* > 0$ such that the inequality
remains strict for every $\alpha \in [0, \alpha^*)$. Pick any $\alpha \in
(0, \min(\alpha^*, 1))$.

**Step 7: Contradiction.** For the chosen $\alpha$, $(*)$ holds for every
$j \in J$. Hence
$$
  \frac{(x_\alpha A)_j}{(x_\alpha B)_j} > \lambda_0
  \quad\text{for every } j \in J,
$$
which gives $\lambda_\mathrm{aux}(x_\alpha) > \lambda_0$, contradicting the
definition $\lambda_0 = \sup_x \lambda_\mathrm{aux}(x)$. $\square$

## References

- [MFoGT, Section 2.8, Exercise 1] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Column-drop inductive step in the direct Loomis proof.
