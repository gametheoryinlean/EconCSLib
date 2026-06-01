---
id: game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex
title: Mixed Strategy Simplex
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.matrix_game
lean:
  modules:
    - EconCSLib.Math.Simplex
  declarations:
    - stdSimplex.pure
    - wsum
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3"
      format: section
      note: "Delta(S) is the simplex of probabilities on a finite set S"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - mixed-strategy
  - simplex
---

# Mixed Strategy Simplex

For a finite set $S$, the mixed strategy simplex $\Delta(S)$ is the set of
probability vectors on $S$:
$$
  \Delta(S)=\{x \in \mathbb{R}^S : x_s \ge 0 \text{ for all } s,\ 
  \sum_{s \in S} x_s = 1\}.
$$
The Lean library uses Mathlib's `stdSimplex ℝ S` for this set, with
`stdSimplex.pure i` for the Dirac point mass at $i$ and `wsum x f` (a
definitional abbreviation for the dot product `x ⬝ᵥ f`) for the weighted
sum of a function $f \colon S \to \mathbb{R}$.

## References

- [MFoGT, Chapter 2, Section 2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Delta(S) is the simplex of probabilities on a finite set S.
