---
id: game_theory.strategic_game.zero_sum.examples.matching_pennies
title: Matching Pennies
kind: example
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.examples
uses:
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.Examples.StrategicGame.MatchingPennies
  declarations:
    - EconCSLib.StrategicGame.Examples.matchingPennies
    - EconCSLib.StrategicGame.Examples.matchingPennies_value
    - EconCSLib.StrategicGame.Examples.matchingPennies_uniform_row_optimal
    - EconCSLib.StrategicGame.Examples.matchingPennies_uniform_column_optimal
source:
  spans:
    - artifact: mfogt
      locator: "Chapter 2, Section 2.2"
      format: section
      note: "Matching Pennies matrix and pure duality gap"
verification:
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - example
  - matrix-game
---

# Matching Pennies

Matching Pennies is the matrix game
$$
  \begin{pmatrix}
  1 & -1\\
  -1 & 1
  \end{pmatrix}.
$$
Its pure maxmin is $-1$ and its pure minmax is $1$, so it has no value in pure
strategies.  Its mixed extension has value $0$.

## References

- [MFoGT, Chapter 2, Section 2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Matching Pennies matrix and pure duality gap.
