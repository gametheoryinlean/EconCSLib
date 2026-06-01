---
id: game_theory.strategic_game.zero_sum.core.optimal_pairs_are_saddle_points
title: Optimal Pairs Are Exactly Saddle Points
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.optimal_strategy_sets
  - game_theory.strategic_game.zero_sum.core.saddle_point
  - game_theory.strategic_game.zero_sum.maximin_le_minimax
  - math.simplex.bounded_by_value
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.optimal_pairs_iff_saddle_point
    - MatrixGame.mem_optimalRowStrategies_iff_E_ge
    - MatrixGame.mem_optimalColumnStrategies_iff_E_le
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(d)"
      format: section
      note: "X(A) x Y(A) is the set of saddle points"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - saddle-point
  - optimal-strategy
---

# Optimal Pairs Are Exactly Saddle Points

For a finite matrix game $A$, the product $X(A)\times Y(A)$ of
optimal-strategy sets is exactly the set of saddle points of $A$.

*Proof.* Let $v=\operatorname{val}(A)$. If $x\in X(A)$ and $y\in Y(A)$, then
$xAy'\ge v$ for every mixed column $y'$ and $x'Ay\le v$ for every mixed row
$x'$. Applying these inequalities to $y$ and $x$ gives $xAy=v$, so
$$
  x'Ay\le xAy\le xAy'
$$
for all $x'$ and $y'$. Thus $(x,y)$ is a saddle point. Conversely, if
$(x,y)$ is a saddle point, then taking $x'$ and $y'$ as pure strategies and
applying the simplex-side order characterisations
([[node:math.simplex.bounded_by_value]]) gives
$$
  E_A(x,y)\le \operatorname{guarantee}_I(x), \qquad
  \operatorname{guarantee}_{II}(y)\le E_A(x,y).
$$
Weak duality [[node:game_theory.strategic_game.zero_sum.maximin_le_minimax]] sandwiches both quantities
between $v$ on the appropriate side, forcing equality. Hence $x\in X(A)$ and
$y\in Y(A)$.

The Lean formalisation factors through two characterisation iff-theorems
(`mem_optimalRowStrategies_iff_E_ge` and `mem_optimalColumnStrategies_iff_E_le`),
which then combine into `MatrixGame.optimal_pairs_iff_saddle_point`.

## References

- [MFoGT, Prop. 2.4.1(d)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. X(A) x Y(A) is the set of saddle points.
