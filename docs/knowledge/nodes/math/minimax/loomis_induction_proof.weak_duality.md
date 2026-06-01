---
id: math.minimax.loomis_induction_proof.weak_duality
title: Weak Duality For Loomis Values
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - math.minimax.loomis_induction_proof.positive_aggregate
  - math.minimax.loomis_induction_proof.value_existence
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.lamB0_le_muB0
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.5, around Theorem 2.5.1"
      format: section
      note: "Weak duality for the Loomis ratios"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - weak-duality
---

# Weak Duality For Loomis Values

The "easy" direction of the Loomis theorem: any maxmin Loomis ratio is
bounded by any minmax Loomis ratio. Used by the direct Loomis induction
proof to set up the sandwich $\lambda_0 \le \mu_0$.

## Statement

Fix $A, B \colon I \times J \to \mathbb{R}$ with $B$ entrywise positive.
With $\lambda_0$ and $\mu_0$ defined in
[[node:math.minimax.loomis_induction_proof.value_existence]],
$$
  \lambda_0 \;\le\; \mu_0.
$$

## Proof

Let $x_0 \in \Delta(I)$ and $y_0 \in \Delta(J)$ be the optimisers supplied
by [[node:math.minimax.loomis_induction_proof.value_existence]], so that
for every $j \in J$ and every $i \in I$
$$
  (x_0 A)_j \ge \lambda_0\,(x_0 B)_j,
  \qquad
  (A y_0)_i \le \mu_0\,(B y_0)_i.
$$
Weight the first family by $y_{0,j} \ge 0$ and sum over $j$:
$$
  \sum_j y_{0,j} (x_0 A)_j \;\ge\; \lambda_0 \sum_j y_{0,j} (x_0 B)_j,
$$
i.e. $x_0 A y_0 \ge \lambda_0 \cdot (x_0 B y_0)$. Symmetrically, weight the
second family by $x_{0,i} \ge 0$ and sum over $i$:
$$
  x_0 A y_0 \;\le\; \mu_0 \cdot (x_0 B y_0).
$$
Combining,
$$
  \lambda_0 \cdot (x_0 B y_0) \;\le\; x_0 A y_0 \;\le\; \mu_0 \cdot (x_0 B y_0).
$$
By [[node:math.minimax.loomis_induction_proof.positive_aggregate]] the
quantity $x_0 B y_0$ is strictly positive, so dividing gives $\lambda_0 \le
\mu_0$. $\square$

## Use

This is the first half of the Loomis sandwich. The reverse direction
$\mu_0 \le \lambda_0$ is established by ruling out the strict inequality
$\lambda_0 < \mu_0$ via the column-drop and row-drop steps of the direct
Loomis induction.

## References

- [MFoGT, Section 2.5] Laraki, Renault, and Sorin, *Mathematical Foundations
  of Game Theory*. Weak duality
  for the Loomis ratios.
