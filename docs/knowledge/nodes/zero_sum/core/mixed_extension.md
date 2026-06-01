---
id: game_theory.strategic_game.zero_sum.core.mixed_extension
title: Mixed Extension Of A Matrix Game
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
    - EconCSLib.Math.Simplex
  declarations:
    - expectedPayoffMatrix
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3"
      format: section
      note: "Mixed extension and multilinear payoff"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - mixed-strategy
  - expected-payoff
---

# Mixed Extension Of A Matrix Game

For a finite matrix game $A : I \times J \to \mathbb{R}$, the mixed extension
has strategy spaces $\Delta(I)$ and $\Delta(J)$.  Its payoff is the bilinear
extension
$$
  g(x,y)=\sum_{i \in I}\sum_{j \in J} x_i y_j A_{ij}.
$$
Pure strategies are identified with Dirac measures in the corresponding
simplex.

## References

- [MFoGT, Chapter 2, Section 2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed extension and multilinear payoff.
