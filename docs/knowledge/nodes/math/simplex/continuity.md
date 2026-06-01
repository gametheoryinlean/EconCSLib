---
id: math.simplex.continuity
title: Continuity on the Real Standard Simplex
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
    - stdSimplex.continuous_coord
    - wsum_continuous
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - continuity
  - topology
---

# Continuity on the Real Standard Simplex

Specialized to the field $\mathbb{R}$, the standard simplex carries the
subspace topology from $\mathbb{R}^I$, and two basic continuity facts are
needed by every existence-via-compactness argument:

- `stdSimplex.continuous_coord i` -- the `i`-th coordinate projection
  $x \mapsto x_i$ is continuous on `stdSimplex ℝ I`.
- `wsum_continuous f` -- for any `f : I → ℝ`, the map
  $x \mapsto \operatorname{wsum} x\, f$ is continuous on `stdSimplex ℝ I`.

Combined with Mathlib's compactness of the real standard simplex
(`stdSimplex.instCompactSpace_coe`), these continuity facts deliver the
existence of optimal mixed strategies via the extreme-value theorem. This
is the analytic ingredient of the Loomis route to the minimax theorem and
of Brouwer-based proofs of Nash existence.

## References

- [MSZ, Chapter 5] Maschler, Solan, and Zamir, *Game Theory*. Continuity of the expected payoff in the
  mixed-strategy profile.
