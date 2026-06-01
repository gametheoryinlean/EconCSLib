---
id: game_theory.strategic_game.zero_sum.continuous.mixed_extension_pathology
title: Mixed Extension Pathology
kind: example
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.continuous.general_mixed_strategy_space
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.5, Exercise 6"
      format: section
      note: "Pathology for mixed extensions defined by one-sided integration"
verification:
  proof: not_applicable
tags:
  - zero-sum
  - mixed-strategy
  - counterexample
---

# Mixed Extension Pathology

Let $S=T=(0,1]$ and define
$$
  f(s,t)=
  \begin{cases}
    0, & s=t,\\
    -1/s^2, & s>t,\\
    1/t^2, & s<t.
  \end{cases}
$$
MFoGT's exercise asks to show that $\int_S f(s,t)\,ds=1$ for each $t$, but that
the one-sided mixed extensions satisfy
$$
  \sup_{\sigma\in\Delta(S)}\inf_{t\in T} f(\sigma,t)
  >
  \inf_{\tau\in\Delta(T)}\sup_{s\in S} f(s,\tau).
$$
This exhibits a pathology in treating the mixed extension without adequate
measurability and integrability hypotheses.

## References

- [MFoGT, Section 3.5, Exercise 6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Pathology for mixed extensions defined by one-sided integration.
