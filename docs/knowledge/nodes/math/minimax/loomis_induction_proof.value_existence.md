---
id: math.minimax.loomis_induction_proof.value_existence
title: Existence of Loomis Optimisers
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.minimax
uses:
  - math.simplex.bounded_by_value
  - math.simplex.continuity
  - math.minimax.loomis_induction_proof.positive_aggregate
  - game_theory.strategic_game.zero_sum.lam_mu_existence
lean:
  modules:
    - EconCSLib.Math.Minimax.Loomis
  declarations:
    - Loomis.lamB.aux_gt_iff_gt
    - Loomis.muB.aux_lt_iff_lt
    - Loomis.colRatio.continuous
    - Loomis.rowRatio.continuous
    - Loomis.lamB.aux.continuous
    - Loomis.muB.aux.continuous
    - Loomis.lamB.aux.bddAbove
    - Loomis.muB.aux.bddBelow
    - Loomis.lamB.aux.le_lamB0
    - Loomis.muB.aux.ge_muB0
    - Loomis.exists_xx_lamB0
    - Loomis.exists_yy_muB0
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.5"
      format: section
      note: "Compactness/continuity step for the Loomis ratios"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - existence
  - compactness
---

# Existence of Loomis Optimisers

Compactness and continuity step for the Loomis induction
([[node:math.minimax.loomis_induction_proof]]): the Loomis ratios are
continuous on the simplices, and their extrema are attained.

## Setup

Fix $A, B \colon I \times J \to \mathbb{R}$ with $B$ entrywise positive
(see [[node:math.minimax.loomis_induction_proof.positive_aggregate]]).
Define
$$
  \lambda_\mathrm{aux}(x) = \inf_{j \in J} \frac{(xA)_j}{(xB)_j},
  \qquad
  \mu_\mathrm{aux}(y) = \sup_{i \in I} \frac{(Ay)_i}{(By)_i},
$$
and
$$
  \lambda_0 = \sup_{x \in \Delta(I)} \lambda_\mathrm{aux}(x),
  \qquad
  \mu_0 = \inf_{y \in \Delta(J)} \mu_\mathrm{aux}(y).
$$

## Statement

(i) **Continuity.** The maps $\lambda_\mathrm{aux} \colon \Delta(I) \to
\mathbb{R}$ and $\mu_\mathrm{aux} \colon \Delta(J) \to \mathbb{R}$ are
continuous.

(ii) **Boundedness.** $\lambda_\mathrm{aux}$ is bounded above and
$\mu_\mathrm{aux}$ is bounded below on their respective simplices.

(iii) **Attainment.** There exist $x_0 \in \Delta(I)$ and
$y_0 \in \Delta(J)$ such that
$\lambda_\mathrm{aux}(x_0) = \lambda_0$ and $\mu_\mathrm{aux}(y_0) = \mu_0$.
Equivalently, for every $j \in J$ and every $i \in I$,
$$
  (x_0 A)_j \ge \lambda_0\,(x_0 B)_j,
  \qquad
  (A y_0)_i \le \mu_0\,(B y_0)_i.
$$

## Proof

(i) Each coordinate $x \mapsto (xA)_j$ and $x \mapsto (xB)_j$ is a continuous
linear functional on $\Delta(I)$. Their quotient is continuous because the
denominator is strictly positive
([[node:math.minimax.loomis_induction_proof.positive_aggregate]]). The
finite infimum of continuous functions over the finite set $J$ is continuous.
The argument for $\mu_\mathrm{aux}$ is dual.

(ii) Each ratio $(xA)_j / (xB)_j$ is bounded above by the obvious extreme
$M_A / m_B$, where $M_A := \max_{i, j} A_{ij}$ and $m_B := \min_{i, j} B_{ij}
> 0$. So $\lambda_\mathrm{aux} \le M_A / m_B$. Symmetrically,
$\mu_\mathrm{aux} \ge m_A / M_B$ where $m_A := \min_{i, j} A_{ij}$ and
$M_B := \max_{i, j} B_{ij}$.

(iii) $\Delta(I)$ is compact in $\mathbb{R}^{|I|}$, and the continuous
function $\lambda_\mathrm{aux}$ attains its supremum on a compact set
(extreme-value theorem). Let $x_0$ be a maximiser; then
$\lambda_\mathrm{aux}(x_0) = \lambda_0$, which by definition of the
infimum-over-$j$ gives $(x_0 A)_j / (x_0 B)_j \ge \lambda_0$ for every $j$,
i.e. $(x_0 A)_j \ge \lambda_0 (x_0 B)_j$ (multiplying by the strictly
positive $(x_0 B)_j$). The $\mu_0$ side is dual.

The compact/continuous building blocks ([[node:math.simplex.continuity]]
and [[node:math.simplex.bounded_by_value]]) live in the core simplex
layer; this lemma extends the $B = \mathbf{1}$ case
([[node:game_theory.strategic_game.zero_sum.lam_mu_existence]]) to general positive $B$ by composing
with positive division. $\square$

## References

- [MFoGT, Section 2.5] Laraki, Renault, and Sorin, *Mathematical Foundations
  of Game Theory*. Compactness
  step for the Loomis ratios.
