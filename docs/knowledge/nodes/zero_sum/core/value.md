---
id: game_theory.strategic_game.zero_sum.core.value
title: Value Of A Zero-Sum Game
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.maximin_minimax
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.value
source:
  spans:
    - artifact: mfogt
      locator: "Definition 2.2.5"
      format: section
      note: "A zero-sum game has a value when maxmin equals minmax"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - value
---

# Value Of A Zero-Sum Game

When the maxmin and minmax of a zero-sum game coincide, the common
scalar is the **value** of the game:
$$
  \operatorname{val}(A) = \underline v = \overline v.
$$

The Lean development defines `MatrixGame.value := A.maximin` and provides
`value_eq_maximin` (definitional) and `value_eq_minimax` (via the minimax
theorem).

## References

- [MFoGT, Def. 2.2.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A zero-sum game has a value when maxmin equals minmax.
