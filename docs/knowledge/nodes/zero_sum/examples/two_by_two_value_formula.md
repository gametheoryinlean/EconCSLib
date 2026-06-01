---
id: game_theory.strategic_game.zero_sum.examples.two_by_two_value_formula
title: Two-By-Two Value Formula
kind: example
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.von_neumann_minimax
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.TwoByTwo
  declarations:
    - EconCSLib.StrategicGame.Examples.twoByTwo
    - EconCSLib.StrategicGame.Examples.twoByTwoRowMixed
    - EconCSLib.StrategicGame.Examples.twoByTwoColumnMixed
    - EconCSLib.StrategicGame.Examples.twoByTwoMixedValue
    - EconCSLib.StrategicGame.Examples.twoByTwo_value
source:
  spans:
    - artifact: mfogt
      locator: "Example 2.6.3"
      format: section
      note: "Value formula for two-by-two matrix games"
verification:
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - example
  - two-by-two
---

## Lean formalisation note

The Lean file formalises the **mixed case** of the value formula: under
hypotheses
`0 < a + d - b - c`, `b ≤ a`, `c ≤ a`, `b ≤ d`, `c ≤ d`
(which guarantee that the mixed strategies are valid probability vectors),
the game value is `(a*d - b*c) / (a + d - b - c)`. The pure-optimal case
disjunction described in the blueprint body falls out of dominance
arguments on the matrix entries and is not separately formalised — when
the mixed-case hypotheses fail, one of the rows/columns is dominated and
the pure pair shows up via `MatrixGame.optimal_pairs_iff_saddle_point`.

# Two-By-Two Value Formula

For a two-by-two matrix
$$
  \begin{pmatrix}
  a & b\\
  c & d
  \end{pmatrix},
$$
either there is a pair of pure optimal strategies, or the optimal strategies
are completely mixed and the value is
$$
  \frac{ad-bc}{a+d-b-c}.
$$

## References

- [MFoGT, Ex. 2.6.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Value formula for two-by-two matrix games.
