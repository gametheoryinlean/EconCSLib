---
id: game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
title: Optimal Strategy Sets
kind: definition
status: formalized
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.value
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.optimalRowStrategies
    - MatrixGame.optimalColumnStrategies
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1"
      format: section
      note: "Definition of X(A) and Y(A), the optimal strategy sets"
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - zero-sum
  - optimal-strategy
---

# Optimal Strategy Sets

For a finite matrix game $A$, the **optimal row strategy set**
$X(A) \subseteq \Delta(I)$ contains the mixed row strategies that achieve the
maximin value, i.e.
$$
  X(A) = \{ x \in \Delta(I) : \min_{j \in J} E_A(x,j) = \operatorname{val}(A) \}.
$$
The **optimal column strategy set** $Y(A) \subseteq \Delta(J)$ is defined
symmetrically with the maximum over pure rows equal to the value.

By the minimax theorem ([[node:game_theory.strategic_game.zero_sum.von_neumann_minimax]]) both sets are
nonempty.

## References

- [MFoGT, Prop. 2.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Definition of X(A) and Y(A), the optimal strategy sets.
