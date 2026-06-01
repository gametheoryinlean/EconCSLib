---
id: game_theory.strategic_game.zero_sum.continuous.quasi_concavity_semicontinuity
title: Quasi-Concavity And Semicontinuity
kind: definition
status: admitted
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.continuous
source:
  spans:
    - artifact: mfogt
      locator: "Definition 3.2.3"
      format: section
      note: "Quasi-concavity, quasi-convexity, upper semicontinuity, and lower semicontinuity"
verification:
  definition: accepted
  proof: not_applicable
tags:
  - zero-sum
  - convexity
  - topology
---

# Quasi-Concavity And Semicontinuity

Let $E$ be a convex subset of a vector space. A function $f:E\to\mathbb R$ is
quasi-concave if every upper section
$$
  \{x\in E:f(x)\ge\lambda\}
$$
is convex. It is quasi-convex if $-f$ is quasi-concave.

If $E$ is a topological space, $f$ is upper semicontinuous if every upper section is
closed. It is lower semicontinuous if $-f$ is upper semicontinuous.

## References

- [MFoGT, Def. 3.2.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Quasi-concavity, quasi-convexity, upper semicontinuity, and lower semicontinuity.
