---
id: math.minimax.loomis_induction_proof.positive_aggregate
title: Positive Aggregates xB and By
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.IsPositive.one
    - Loomis.xB_pos
    - Loomis.By_pos
    - Loomis.xBy_pos
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.5, around Theorem 2.5.1"
      format: section
      note: "Aggregate positivity used to define the Loomis ratios"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - simplex
  - positivity
---

# Positive Aggregates xB and By

A bookkeeping lemma used throughout the direct Loomis induction proof: an
entrywise-positive matrix $B$ stays positive after weighting by a
probability vector on either side.

## Statement

Let $I$ and $J$ be finite nonempty index types, and let
$B \colon I \times J \to \mathbb{R}$ satisfy $B_{ij} > 0$ for every
$(i, j) \in I \times J$. Then:

1. For every $x \in \Delta(I)$ and every $j \in J$,
   $(xB)_j = \sum_i x_i B_{ij} > 0$.
2. For every $y \in \Delta(J)$ and every $i \in I$,
   $(By)_i = \sum_j B_{ij}\, y_j > 0$.
3. For every $x \in \Delta(I)$ and every $y \in \Delta(J)$,
   $x B y = \sum_{i, j} x_i B_{ij} y_j > 0$.

## Proof

(i) Fix $x \in \Delta(I)$ and $j \in J$. Each summand $x_i B_{ij}$ is
nonnegative because $x_i \ge 0$ and $B_{ij} > 0$. Since $\sum_i x_i = 1$,
there is some $i^* \in I$ with $x_{i^*} > 0$; for that index
$x_{i^*} B_{i^* j} > 0$ strictly. Adding the nonnegative remaining terms
keeps the sum strictly positive.

(ii) Symmetric in $y$ and the column variable.

(iii) Weight (ii) by $x \ge 0$ with $\sum_i x_i = 1$. The argument of (i)
applied to the strictly positive function $i \mapsto (By)_i$ gives
$\sum_i x_i (By)_i > 0$, which is exactly $x B y$. $\square$

## Use

Used wherever the Loomis ratios $\frac{(xA)_j}{(xB)_j}$ and
$\frac{(Ay)_i}{(By)_i}$ appear: the denominators are strictly positive, so
the ratios are well-defined real numbers and continuous in their simplex
arguments. In particular it underwrites the value-existence and
weak-duality lemmas of the direct Loomis induction proof.

## References

- [MFoGT, Section 2.5] Laraki, Renault, and Sorin, *Mathematical Foundations
  of Game Theory*. Aggregate
  positivity used to define the Loomis ratios.
