---
id: math.simplex.wsum
title: Weighted Sum over the Standard Simplex
kind: definition
status: formalized
primary_topic: math
topics:
  - math
  - math.simplex
uses: []
lean:
  modules:
    - EconCSLib.Math.Simplex
  declarations:
    - wsum
    - wsum_const
    - wsum_le_wsum
    - wsum_nonneg
    - wsum_pos
    - wsum_ge_wsum
    - wsum_add
    - wsum_smul
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - weighted-sum
---

# Weighted Sum over the Standard Simplex

For a finite index `I`, a strictly ordered field `𝕜`, an element
`x ∈ stdSimplex 𝕜 I`, and a function `f : I → 𝕜`, the *weighted sum* is
$$
  \operatorname{wsum} x \, f \;=\; \sum_{i \in I} x_i \cdot f(i).
$$

This is the operator that turns a mixed strategy into an expected payoff and
a lottery into an expected utility. It is definitionally equal to Mathlib's
finite dot product `x ⬝ᵥ f`, but receives a dedicated name because the
simplex-specific algebraic lemmas below depend on the constraints
$\sum_i x_i = 1$ and $x_i \ge 0$ and have no generic `dotProduct`
analogue.

The core algebra:

- `wsum_const`  -- `wsum x (fun _ => c) = c`
- `wsum_le_wsum`  -- pointwise `f ≤ g` implies `wsum x f ≤ wsum x g`
- `wsum_nonneg`  -- pointwise `0 ≤ f` implies `0 ≤ wsum x f`
- `wsum_ge_wsum`  -- the symmetric `≥` version of monotonicity
- `wsum_add`  -- `wsum x (f + g) = wsum x f + wsum x g`
- `wsum_smul`  -- `wsum x (c • f) = c · wsum x f`

## References

- [MFoGT, Chapter 1] Laraki, Renault, and Sorin, *Mathematical Foundations of
  Game Theory*. Mixed-strategy
  weighted sums.

## Provenance

- Adapted from `GameTheory/Simplex.lean` in
  [math-xmum/gametheory](https://github.com/math-xmum/gametheory).
