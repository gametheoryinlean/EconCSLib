---
id: game_theory.strategic_game.zero_sum.continuous.sion_wolfe_no_mixed_value
title: Sion-Wolfe Game Has No Mixed Value
kind: example
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.general_mixed_minimax_theorem
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 7"
      format: section
      note: "Sion-Wolfe example with no mixed value"
verification:
  proof: not_applicable
tags:
  - zero-sum
  - mixed-strategy
  - counterexample
---

# Sion-Wolfe Game Has No Mixed Value

Let $S=T=[0,1]$ with the Borel sigma-algebra and define
$$
  f(s,t)=
  \begin{cases}
    -1, & s<t<s+1/2,\\
    0, & t=s\text{ or }t=s+1/2,\\
    1, & \text{otherwise}.
  \end{cases}
$$
For the mixed extension over $\Delta(S)$ and $\Delta(T)$, MFoGT's exercise states
that
$$
  \sup_{\sigma\in\Delta(S)}\inf_{t\in T} f(\sigma,t)=\frac13,
$$
and asks to prove that the mixed game has no value.

## References

- [MFoGT, Section 3.5, Exercise 7] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Sion-Wolfe example with no mixed value.
