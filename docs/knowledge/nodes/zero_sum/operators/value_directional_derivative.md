---
id: game_theory.strategic_game.zero_sum.operators.value_directional_derivative
title: Directional Derivative Of The Value
kind: proposition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.operators
uses:
  - game_theory.strategic_game.zero_sum.operators.derived_game
source:
  spans:
    - artifact: mfogt
      locator: "Proposition 3.4.2"
      format: section
      note: "Directional derivative of the value equals the value of the derived game"
verification:
  statement: accepted
  proof: accepted
tags:
  - zero-sum
  - value-operator
  - derived-game
---

# Directional Derivative Of The Value

Let $S$ and $T$ be compact sets and let $f,g:S\times T\to\mathbb R$. Assume that,
for every $\alpha\ge 0$, the functions $g$ and $f+\alpha g$ are upper
semicontinuous in $s$ and lower semicontinuous in $t$, and that each game
$(S,T,f+\alpha g)$ has a value. Then
$$
  \lim_{\alpha\to0^+}
  \frac{\operatorname{val}_{S\times T}(f+\alpha g)
        -\operatorname{val}_{S\times T}(f)}{\alpha}
$$
exists and equals
$$
  \operatorname{val}_{S(f)\times T(f)}(g),
$$
the value of the derived game.

*Proof.* Let $s_\alpha$ be optimal for player 1 in $f+\alpha g$ and let $t\in T(f)$.
Comparing $(f+\alpha g)(s_\alpha,t)$ with the two values gives a lower bound on
the difference quotient by $\inf_{T(f)}g(s_\alpha,t)$. Taking limit points of
$s_\alpha$ and using semicontinuity places the limit in $S(f)$, giving the lower
bound by the value of the derived game. The dual argument with optimal strategies
for player 2 gives the reverse inequality.

## References

- [MFoGT, Prop. 3.4.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Directional derivative of the value equals the value of the derived game.
