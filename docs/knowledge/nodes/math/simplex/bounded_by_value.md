---
id: math.simplex.bounded_by_value
title: Pointwise Bounds Are Simplex Bounds
kind: lemma
status: proved
primary_topic: math
topics:
  - math
  - math.simplex
uses:
  - math.simplex.pure
lean:
  modules:
    - EconCSLib.Math.Simplex
  declarations:
    - ge_iff_simplex_ge
    - le_iff_simplex_le
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - core
  - simplex
  - minimax
---

# Pointwise Bounds Are Simplex Bounds

For a finite index `I`, strictly ordered field `𝕜`, value `v ∈ 𝕜`, and
function `f : I → 𝕜`,
$$
  (\forall i,\; v \le f(i)) \;\Longleftrightarrow\;
  (\forall x \in \operatorname{stdSimplex} \mathbb{K}\, I,\; v \le \operatorname{wsum} x\, f).
$$

The symmetric `le_iff_simplex_le` gives the analogous statement for upper
bounds. Both directions are short:

- pointwise $\Rightarrow$ simplex uses `wsum_const` plus `wsum_le_wsum`;
- simplex $\Rightarrow$ pointwise specializes to the point-mass simplex
  element `stdSimplex.pure i` and applies `wsum_pure_apply`.

These bridges are the workhorses of Loomis-style minimax arguments: they
reduce a quantification over the entire mixed-strategy simplex to a
quantification over pure strategies, where finiteness of `I` makes the
remaining argument elementary.

## References

- [MSZ, Chapter 5] Maschler, Solan, and Zamir, *Game Theory*. Reduction of mixed-strategy quantifiers to
  pure-strategy quantifiers in zero-sum analyses.
