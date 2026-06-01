---
id: game_theory.strategic_game.zero_sum.operators.value_operator_general
title: General Value Operator
kind: definition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.operators
uses:
  - game_theory.strategic_game.zero_sum.core.value
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.4"
      format: section
      note: "Value operator on a cone of payoff functions for games with a value"
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - value-operator
---

# General Value Operator

Fix strategy sets $S$ and $T$ and a convex cone $F$ of functions
$S\times T\to\mathbb R$ containing the constant functions. Assume every game
$(S,T,f)$ with $f\in F$ has a value. The value operator is
$$
  \operatorname{val}_{S\times T}:F\to\mathbb R,\qquad
  f\mapsto
  \sup_{s\in S}\inf_{t\in T}f(s,t)
  =
  \inf_{t\in T}\sup_{s\in S}f(s,t).
$$
It is monotone and translates constants:
$$
  f\le g\Rightarrow \operatorname{val}(f)\le\operatorname{val}(g),
  \qquad
  \operatorname{val}(f+c)=\operatorname{val}(f)+c.
$$

## References

- [MFoGT, Section 3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Value operator on a cone of payoff functions for games with a value.
