---
id: game_theory.strategic_game.zero_sum.mixed_matrix_payoff
title: Expected Payoff of a Matrix Game
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.core.mixed_strategy
  - game_theory.strategic_game.zero_sum.matrix_game
lean:
  modules:
    - EconCSLib.Math.Simplex
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - expectedPayoffMatrix
    - MatrixGame.E
    - MatrixGame.Ej
    - MatrixGame.Ei
    - MatrixGame.payoffAgainstRow
    - MatrixGame.payoffAgainstColumn
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.3"
      format: section
      note: "Mixed extension of a finite matrix game"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
generality:
  reviewed: true
  prompt: "How is a matrix payoff extended to mixed strategies?"
  verdict: "By the bilinear weighted sum over row and column simplices."
tags:
  - zero-sum
  - mixed-strategy
  - matrix-game
---

# Expected Payoff of a Matrix Game

For mixed strategies $x \in \Delta(I)$ and $y \in \Delta(J)$, the expected
payoff of the matrix game $A$ is

$$E_A(x,y) = \sum_{i \in I}\sum_{j \in J} x_i y_j A(i,j).$$

The one-sided forms $E_A(x,j)$ and $E_A(i,y)$ describe mixed play against a
pure response.

## References

- [MFoGT, Chapter 2, Section 2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed extension of a finite matrix game.
