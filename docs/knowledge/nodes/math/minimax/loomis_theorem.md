---
id: math.minimax.loomis_theorem
title: Loomis Theorem (Positive B)
kind: theorem
status: proved
proved_via_plan: math.minimax.loomis_induction_proof
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - math.minimax.loomis_induction_proof.column_drop
  - math.minimax.loomis_induction_proof.positive_aggregate
  - math.minimax.loomis_induction_proof.value_existence
  - math.minimax.loomis_induction_proof.weak_duality
  - math.minimax.loomis_induction_proof.base_case
  - math.minimax.loomis_induction_proof.row_drop
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.loomis_value_eq
    - Loomis.loomis_theorem
source:
  spans:
    - artifact: mfogt
      locator: "Theorem 2.5.1"
      format: section
      note: "Loomis theorem for matrices A and positive B"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - minimax
  - loomis
---

# Loomis Theorem (Positive B)

## Setup

Fix finite nonempty index types $I$ and $J$. Let $A, B \colon I \times J \to
\mathbb{R}$ be two real matrices, and assume $B$ is **entrywise positive**:
$B_{ij} > 0$ for every $(i, j) \in I \times J$.

For $x \in \Delta(I)$ and $y \in \Delta(J)$ define the row- and column-vector
products
$$
  (xA)_j = \sum_i x_i A_{ij}, \qquad (Ay)_i = \sum_j A_{ij}\, y_j,
$$
and similarly $(xB)_j$, $(By)_i$. Positivity of $B$ implies $(xB)_j > 0$ for
every $x \in \Delta(I)$ and every $j$, and $(By)_i > 0$ for every
$y \in \Delta(J)$ and every $i$ — recorded as
[[node:math.minimax.loomis_induction_proof.positive_aggregate]].

## Statement

**Theorem (Loomis).** There exist $x \in \Delta(I)$, $y \in \Delta(J)$, and
$v \in \mathbb{R}$ such that
$$
  xA \ge v \cdot xB, \qquad Ay \le v \cdot By,
$$
where the inequalities are componentwise. Equivalently, for every $j \in J$
and every $i \in I$,
$$
  \sum_i x_i A_{ij} \ge v \sum_i x_i B_{ij}, \qquad
  \sum_j A_{ij}\, y_j \le v \sum_j B_{ij}\, y_j.
$$

The common ratio level $v$ is the **Loomis value** of the pair $(A, B)$. The
scalar form of the same statement is
$$
  \lambda_0 \;=\; \mu_0 \;=\; v,
$$
where
$$
  \lambda_0
  \;=\; \sup_{x \in \Delta(I)} \inf_{j \in J} \frac{(xA)_j}{(xB)_j},
  \qquad
  \mu_0
  \;=\; \inf_{y \in \Delta(J)} \sup_{i \in I} \frac{(Ay)_i}{(By)_i}.
$$
The denominators are strictly positive by positivity of $B$, so both
expressions are well-defined.

## Discussion

MFoGT presents Loomis as an extension of von Neumann's minimax theorem. The
canonical blueprint route in this library is the opposite: Loomis is proved
directly by induction on $|I| + |J|$ (see the proof-plan
[[node:math.minimax.loomis_induction_proof]]). Finite minimax is then the
$B = \mathbf{1}$ specialisation
([[node:math.minimax.minimax_from_loomis]]): for any probability vectors
$x, y$ and the all-ones matrix $B = \mathbf{1}$, both $xB$ and $By$ are
identically $1$, so the Loomis inequalities collapse to
$\min_j (xA)_j \ge v \ge \max_i (Ay)_i$.

The library's Lean development formalises the general positive-$B$ Loomis
theorem in `EconCSLib.StrategicGame.Loomis`, and re-derives the
$B = \mathbf{1}$ specialisation (the finite von Neumann minimax) as the
corollary `Loomis.minmax_from_general`. The original inlined
induction at $B = \mathbf{1}$ in `EconCSLib.StrategicGame.MinimaxLoomis`
is retained as an independent witness.

*Proof.* See the induction-on-$|I|+|J|$ proof-plan
*Direct Induction Proof Of Loomis Theorem*, which decomposes the argument
into:

1. positivity of the aggregates $xB$ and $By$
   ([[node:math.minimax.loomis_induction_proof.positive_aggregate]]);
2. existence of optimisers attaining $\lambda_0$ and $\mu_0$
   ([[node:math.minimax.loomis_induction_proof.value_existence]]);
3. weak duality $\lambda_0 \le \mu_0$
   ([[node:math.minimax.loomis_induction_proof.weak_duality]]);
4. the base case $|I| + |J| = 2$
   ([[node:math.minimax.loomis_induction_proof.base_case]]);
5. the column-drop induction step
   ([[node:math.minimax.loomis_induction_proof.column_drop]]);
6. the row-drop induction step
   ([[node:math.minimax.loomis_induction_proof.row_drop]]).

Steps 1–3 give $\lambda_0 \le \mu_0$ and existence of attaining strategies
$x_0, y_0$. Step 4 closes the base case. Steps 5–6 rule out the strict
inequality $\lambda_0 < \mu_0$ by induction on $|I| + |J|$, leaving the
equality $\lambda_0 = \mu_0 = v$, witnessed by $(x_0, y_0)$.

## References

- [MFoGT, Thm. 2.5.1] Laraki, Renault, and Sorin, *Mathematical Foundations
  of Game Theory*. Loomis
  theorem for matrices $A$ and positive $B$.
- [MFoGT, Section 2.8, Exercise 1] Same. Direct induction proof of Loomis,
  independent of von Neumann minimax.
