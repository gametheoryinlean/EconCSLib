---
id: game_theory.strategic_game.zero_sum.continuous.general_mixed_strategy_space
title: General Mixed Strategy Space
kind: definition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
uses:
  - game_theory.strategic_game.zero_sum.zero_sum_game
source:
  spans:
    - artifact: mfogt
      locator: "Section 3.3"
      format: section
      note: "Delta_f(X), Delta(X), regular probabilities, and weak-star topology"
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - mixed-strategy
  - topology
---

# General Mixed Strategy Space

For an arbitrary set $X$, $\Delta_f(X)$ denotes the set of finitely supported
probability measures on $X$, regarded as the convex hull of $X$.

If $X$ is a topological space, $\Delta(X)$ denotes the regular Borel probability
measures on $X$. When $X$ is compact Hausdorff, $\Delta(X)$ carries the weak-star
topology, the weakest topology for which
$$
  \mu\mapsto \int_X \varphi\,d\mu
$$
is continuous for every real-valued continuous function $\varphi$ on $X$.

## References

- [MFoGT, Section 3.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Delta_f(X), Delta(X), regular probabilities, and weak-star topology.
