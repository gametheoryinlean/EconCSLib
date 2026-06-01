---
id: math.minimax.loomis_induction_proof.base_case
title: Base Case of Loomis Induction
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
    - Loomis.loomis_value_IJ_2
source:
  spans:
    - artifact: mfogt
      locator: "Section 2.8, Exercise 1"
      format: section
      note: "Base case |I|=|J|=1 of the Loomis induction"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - loomis
  - base-case
---

# Base Case of Loomis Induction

The base case of the induction in
[[node:math.minimax.loomis_induction_proof]]: when $|I| + |J| = 2$ the
matrices are $1 \times 1$ and the Loomis values reduce to a single ratio.

## Statement

Let $I$ and $J$ be finite nonempty index types with $|I| + |J| = 2$, so
$|I| = |J| = 1$ with single elements $i_0 \in I$ and $j_0 \in J$. Let
$A, B \colon I \times J \to \mathbb{R}$ with $B_{i_0, j_0} > 0$. Then
$$
  \lambda_0 \;=\; \mu_0 \;=\; \frac{A_{i_0, j_0}}{B_{i_0, j_0}}.
$$

## Proof

Both simplices are singletons: $\Delta(I) = \{e_{i_0}\}$ and
$\Delta(J) = \{e_{j_0}\}$, where $e_{i_0}$, $e_{j_0}$ are the unique unit
mass strategies. For the unique $x = e_{i_0}$ and $j = j_0$ we have
$(xA)_{j_0} = A_{i_0, j_0}$ and $(xB)_{j_0} = B_{i_0, j_0}$, so
$$
  \lambda_\mathrm{aux}(e_{i_0}) = \frac{A_{i_0, j_0}}{B_{i_0, j_0}}.
$$
Taking the supremum over the singleton $\Delta(I)$ gives $\lambda_0 = A_{i_0,
j_0} / B_{i_0, j_0}$. The argument for $\mu_0$ is identical. $\square$

## References

- [MFoGT, Section 2.8, Exercise 1] Laraki, Renault, and Sorin, *Mathematical
  Foundations of Game Theory*.
  Base case of the Loomis induction.
