---
id: math.simplex.wsum_comm
title: Iterated Weighted Sums Commute
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.simplex
uses:
  - math.simplex.wsum
lean:
  modules:
    - EconCSLib.Math.Simplex
  declarations:
    - wsum_wsum_comm
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - fubini
---

# Iterated Weighted Sums Commute

For finite indices `I` and `J`, simplex elements `x ∈ stdSimplex 𝕜 I` and
`y ∈ stdSimplex 𝕜 J`, and a payoff matrix `A : I → J → 𝕜`,
$$
  \sum_{i \in I} x_i \!\left( \sum_{j \in J} y_j \, A_{ij} \right)
  \;=\;
  \sum_{j \in J} y_j \!\left( \sum_{i \in I} x_i \, A_{ij} \right).
$$

In `wsum`-notation:
$$
  \operatorname{wsum} x \, (\lambda i.\; \operatorname{wsum} y\, A_{i\,\cdot})
  \;=\;
  \operatorname{wsum} y \, (\lambda j.\; \operatorname{wsum} x\, A_{\cdot\, j}).
$$

This is the finite-sum Fubini fact that lets matrix-game expected payoffs be
computed in either order. It is the algebraic backbone of the minimax-style
manipulations (Loomis) on the value of a mixed extension.

## References

- [MSZ, Chapter 5] Maschler, Solan, and Zamir, *Game Theory*. Expected payoff of a matrix game evaluated as a
  bilinear form in the two players' mixed strategies.
