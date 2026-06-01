---
id: game_theory.strategic_game.zero_sum.operators.value_operator_nonexpansive_general
title: General Value Operator Is Nonexpansive
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.operators
uses:
  - game_theory.strategic_game.zero_sum.operators.value_operator_general
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 3.4.1"
      format: section
      note: "Nonexpansiveness of the value operator for the sup norm"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - value-operator
---

# General Value Operator Is Nonexpansive

For payoff functions $f,g\in F$,
$$
  |\operatorname{val}(f)-\operatorname{val}(g)|
  \le
  \|f-g\|_\infty.
$$

*Proof.* Since $f\le g+\|f-g\|_\infty$, monotonicity and translation of constants give
$$
  \operatorname{val}(f)
  \le
  \operatorname{val}(g)+\|f-g\|_\infty.
$$
The reverse inequality follows by exchanging $f$ and $g$.

## References

- [MFoGT, Prop. 3.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Nonexpansiveness of the value operator for the sup norm.
