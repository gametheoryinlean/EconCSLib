---
id: math.minimax.loomis_induction_proof
title: Direct Induction Proof Of Loomis Theorem
kind: proof-plan
status: formalized
primary_topic: math
topics:
  - math
  - math.minimax
target: math.minimax.loomis_theorem
plan_status: selected
uses:
  - math.minimax.loomis_induction_proof.base_case
  - math.minimax.loomis_induction_proof.row_drop
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.loomis_value_eq
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 1"
      format: section
      note: "Direct induction proof of Loomis theorem, independent of von Neumann minimax"
verification:
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - proof-plan
---

# Direct Induction Proof Of Loomis Theorem

This proof-plan closes [[node:math.minimax.loomis_theorem]] by induction
on $N := |I| + |J|$. The sub-lemmas it cites factor the argument into six
pieces.

## Notation

Fix $A, B \colon I \times J \to \mathbb{R}$ with $B$ entrywise positive. Set
$$
  \lambda_\mathrm{aux}(x) = \inf_{j \in J} \frac{(xA)_j}{(xB)_j},
  \qquad
  \mu_\mathrm{aux}(y) = \sup_{i \in I} \frac{(Ay)_i}{(By)_i},
$$
$$
  \lambda_0 = \sup_{x \in \Delta(I)} \lambda_\mathrm{aux}(x),
  \qquad
  \mu_0 = \inf_{y \in \Delta(J)} \mu_\mathrm{aux}(y).
$$
Both ratios are well-defined by
[[node:math.minimax.loomis_induction_proof.positive_aggregate]]:
$(xB)_j > 0$ and $(By)_i > 0$ for every $x \in \Delta(I)$, $y \in \Delta(J)$,
$j \in J$, $i \in I$.

## Proof structure

*Step 1 — Existence of optimisers.* By
[[node:math.minimax.loomis_induction_proof.value_existence]], the
functionals $\lambda_\mathrm{aux}$ and $\mu_\mathrm{aux}$ are continuous on
the compact simplices $\Delta(I)$ and $\Delta(J)$, and attain their
respective $\sup$ and $\inf$. Let $x_0 \in \Delta(I)$ and $y_0 \in \Delta(J)$
be attaining strategies, so that for every $j \in J$ and every $i \in I$
$$
  (x_0 A)_j \ge \lambda_0 \,(x_0 B)_j,
  \qquad
  (A y_0)_i \le \mu_0 \,(B y_0)_i.
$$

*Step 2 — Weak duality.* By
[[node:math.minimax.loomis_induction_proof.weak_duality]],
$\lambda_0 \le \mu_0$, using positivity of $x_0 B y_0$.

*Step 3 — Induction on $N = |I| + |J|$.* The base case $N = 2$ (i.e. $|I| =
|J| = 1$) is handled by
[[node:math.minimax.loomis_induction_proof.base_case]]: the unique
ratio $A_{i_0, j_0} / B_{i_0, j_0}$ is simultaneously $\lambda_0$ and
$\mu_0$.

*Step 4 — Inductive step.* Assume $\lambda_0' = \mu_0'$ for every
positive-$B$ pair on index types of total cardinality strictly less than
$N$. Suppose, for contradiction, that $\lambda_0 < \mu_0$. The attainment
inequalities above must contain at least one *strict* inequality: if every
inequality were an equality then
$$
  x_0 A y_0 = \lambda_0 \,(x_0 B y_0) = \mu_0 \,(x_0 B y_0)
$$
(weighting the equalities by $y_0$ and $x_0$ respectively), and dividing by
the strictly positive quantity $x_0 B y_0$ gives $\lambda_0 = \mu_0$,
contradiction. Hence either some column $j_0$ satisfies
$(x_0 A)_{j_0} > \lambda_0 (x_0 B)_{j_0}$, or some row $i_0$ satisfies
$(A y_0)_{i_0} < \mu_0 (B y_0)_{i_0}$. The two cases are dual:

- the column case is closed by
  [[node:math.minimax.loomis_induction_proof.column_drop]];
- the row case is closed by
  [[node:math.minimax.loomis_induction_proof.row_drop]].

Each case derives a contradiction from $\lambda_0 < \mu_0$, completing the
induction. Therefore $\lambda_0 = \mu_0 = v$, and $(x_0, y_0, v)$ witnesses
the Loomis inequalities of [[node:math.minimax.loomis_theorem]].

## References

- [MFoGT, Section 2.8, Exercise 1] Laraki, Renault, and Sorin,
  *Mathematical Foundations of Game Theory*. Direct induction proof of
  Loomis theorem, independent of von Neumann minimax.
