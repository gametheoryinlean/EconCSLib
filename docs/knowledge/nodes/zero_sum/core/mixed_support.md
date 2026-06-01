---
id: game_theory.strategic_game.zero_sum.core.mixed_support
title: Support Of A Mixed Strategy
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.mixed_strategy_simplex
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.support
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3"
      format: section
      note: "Support of a mixed strategy"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - mixed-strategy
  - support
---

# Support Of A Mixed Strategy

The support of a mixed strategy $x \in \Delta(I)$ is the set
$$
  \operatorname{supp}(x)=\{i \in I : x_i>0\}.
$$
In Lean, `MatrixGame.support` returns this as a `Finset I` via
`Finset.univ.filter (0 < x.val ·)`. Marked `noncomputable` because strict
inequality on `ℝ` is not decidable.

## References

- [MFoGT, Chapter 2, Section 2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Support of a mixed strategy.
