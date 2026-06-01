---
id: game_theory.strategic_game.zero_sum.core.support_complementarity
title: Support Complementarity
kind: theorem
status: proved
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.core
uses:
  - game_theory.strategic_game.zero_sum.core.mixed_support
  - game_theory.strategic_game.zero_sum.core.optimal_pairs_are_saddle_points
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
  declarations:
    - MatrixGame.support_complementarity_row
    - MatrixGame.support_complementarity_column
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 2.4.1(b)"
      format: section
      note: "Complementarity on supports of optimal strategies"
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - zero-sum
  - complementarity
  - optimal-strategy
---

# Support Complementarity

Let $x \in X(A)$ and $y \in Y(A)$. If $i \in \operatorname{supp}(x)$, then
the pure row $i$ obtains the value against $y$. If
$j \in \operatorname{supp}(y)$, then the mixed strategy $x$ obtains the
value against the pure column $j$.

*Proof.* Let $v=\operatorname{val}(A)$. Since $y$ is optimal for player II,
each pure row payoff satisfies $e_iAy\le v$. Since $x$ is optimal for player
I, the average of these row payoffs under $x$ is
$$
  xAy=\sum_i x_i(e_iAy)=v.
$$
An average of numbers all bounded above by $v$ can equal $v$ only if every
term with positive weight is equal to $v$. Hence $e_iAy=v$ for
$i\in\operatorname{supp}(x)$. The column statement is dual: optimality of
$x$ gives $xAe_j\ge v$ for every $j$, while optimality of $y$ gives
$$
  xAy=\sum_j y_j(xAe_j)=v.
$$
Thus every positively weighted column in $y$ satisfies $xAe_j=v$.

The Lean formalisation provides separate theorems for the two directions:
`MatrixGame.support_complementarity_row` (rows in $\operatorname{supp}(x)$
hit the value) and `MatrixGame.support_complementarity_column` (columns in
$\operatorname{supp}(y)$ hit the value).

## References

- [MFoGT, Prop. 2.4.1(b)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Complementarity on supports of optimal strategies.
