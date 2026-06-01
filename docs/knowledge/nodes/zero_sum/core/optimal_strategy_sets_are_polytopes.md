---
id: game_theory.strategic_game.zero_sum.core.optimal_strategy_sets_are_polytopes
title: Optimal Strategy Sets Are Polytopes
kind: proposition
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.OptimalStrategySetPolytope
  declarations:
    - MatrixGame.image_optimalRowStrategies_eq
    - MatrixGame.image_optimalColumnStrategies_eq
    - MatrixGame.optimalRowSet_convex
    - MatrixGame.optimalRowSet_isClosed
    - MatrixGame.optimalRowSet_isCompact
    - MatrixGame.optimalRowSet_nonempty
    - MatrixGame.optimalColumnSet_convex
    - MatrixGame.optimalColumnSet_isClosed
    - MatrixGame.optimalColumnSet_isCompact
    - MatrixGame.optimalColumnSet_nonempty
    - MatrixGame.optimalRowStrategies_image_isPolytope
    - MatrixGame.optimalColumnStrategies_image_isPolytope
    - MatrixGame.optimalRowSet
    - MatrixGame.optimalColumnSet
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(a)"
      format: section
      note: "Nonemptiness and polytope structure of optimal strategy sets"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
generality:
  reviewed: true
  prompt: "Why is the polytope claim stated on `Subtype.val '' optimalRowStrategies` rather than directly on `optimalRowStrategies`?"
  verdict: "The optimal-strategy set lives in the subtype `stdSimplex ℝ I`, which is not an ambient vector space — `Convex ℝ S` requires `S : Set V` for `V` an `AddCommMonoid` with scalar action. The natural ambient space for polytope vocabulary is `I → ℝ`, so the file states convexity, closedness, compactness, and nonemptiness on the image of the optimal set under `Subtype.val`. The explicit H-representation `optimalRowSet` makes the polytope structure machine-checkable."
tags:
  - zero-sum
  - optimal-strategy
  - polytope
---

# Optimal Strategy Sets Are Polytopes

For every finite matrix game $A$, the optimal strategy sets $X(A)$ and $Y(A)$
are nonempty polytopes.

*Proof.* By the minimax theorem, at least one mixed row $x$ and one mixed column
$y$ attain the common value $v=\operatorname{val}(A)$, so $X(A)$ and $Y(A)$ are
nonempty. The row player's optimal set is
$$
  X(A)=\{x\in\Delta(I): xAe_j\ge v\text{ for every }j\in J\}.
$$
This is the intersection of the simplex $\Delta(I)$ with finitely many closed
half-spaces, hence a polytope. Similarly,
$$
  Y(A)=\{y\in\Delta(J): e_iAy\le v\text{ for every }i\in I\},
$$
again an intersection of the simplex with finitely many closed half-spaces.

## References

- [MFoGT, Prop. 2.4.1(a)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nonemptiness and polytope structure of optimal strategy sets.
