---
id: game_theory.strategic_game.zero_sum.core.strong_complementarity
title: Strong Complementarity
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.support_complementarity
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.StrongComplementarity
  declarations:
    - MatrixGame.exists_strong_complementary_pair
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(c)"
      format: section
      note: "Existence of a strongly complementary optimal pair"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - complementarity
  - optimal-strategy
---

# Strong Complementarity

For a finite zero-sum matrix game $A : I \times J \to \mathbb{R}$ there exists an
optimal pair $(x^\ast, y^\ast) \in X(A) \times Y(A)$ that is **strongly
complementary**:

$$
  x^\ast_i > 0 \iff e_i A y^\ast = \operatorname{val}(A),
  \qquad
  y^\ast_j > 0 \iff x^\ast A e_j = \operatorname{val}(A).
$$

The forward implications ($\Rightarrow$) hold for *every* optimal pair and are
exactly [[node:game_theory.strategic_game.zero_sum.core.support_complementarity]].
The strengthening here is the existence of a pair for which the reverse
implications ($\Leftarrow$) also hold simultaneously.

*Proof.* Shift the payoffs by a constant $K$ so the value becomes positive, and
read off the row/column linear programs of the shifted game. LP strong
complementary slackness supplies an optimal LP pair satisfying strict
complementarity; rescaling back by the shifted value yields an optimal
matrix-game pair satisfying the biconditional above.

## References

- [MFoGT, Prop. 2.4.1(c)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Strong complementarity of optimal strategies via LP strong complementary slackness.
