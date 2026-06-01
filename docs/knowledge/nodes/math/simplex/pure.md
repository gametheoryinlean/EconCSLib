---
id: math.simplex.pure
title: Point Mass on the Standard Simplex
kind: definition
status: formalized
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
    - stdSimplex.pure
    - stdSimplex.pure_apply
    - wsum_pure_apply
    - wsum_pure
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - dirac
---

# Point Mass on the Standard Simplex

For a finite index `I` with decidable equality and a chosen vertex `i₀ ∈ I`,
the *point mass* `stdSimplex.pure i₀` is the simplex element that puts unit
weight on `i₀`:
$$
  (\operatorname{pure} i_0)_i \;=\;
  \begin{cases} 1 & i = i_0,\\ 0 & i \ne i_0. \end{cases}
$$

The two key facts:

- `stdSimplex.pure_apply` -- the coordinate formula above (rfl-true).
- `wsum_pure_apply` -- weighted-sum collapse:
  $\operatorname{wsum}\,(\operatorname{pure} i_0)\, f \;=\; f(i_0)$.

A legacy version `wsum_pure` is also exposed for code that builds the point
mass inline as an anonymous-structure simplex element; new code should
prefer `stdSimplex.pure` together with `wsum_pure_apply`.

The point mass is the bridge between pure and mixed strategies: it embeds
any pure action into the mixed-strategy simplex without disturbing its
weighted-sum semantics. This embedding is what justifies "pure strategies
are a special case of mixed strategies".

## References

- [MSZ, Chapter 5] Maschler, Solan, and Zamir, *Game Theory*. Pure strategies as Dirac mixed strategies.
