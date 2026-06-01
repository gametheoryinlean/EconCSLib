---
id: game_theory.strategic_game.zero_sum.approachability.deterministic_blackwell_sequence
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.applications
title: Deterministic Blackwell Sequence
kind: theorem
status: staged
verification:
  statement: accepted
  proof: gap
tags:
  - approachability
  - convexity
---

# Deterministic Blackwell Sequence

Let $C$ be a nonempty closed convex subset of $\mathbb R^k$, and let
$(x_n)$ be a bounded sequence in $\mathbb R^k$. Let
$$
  \bar x_n=\frac1n\sum_{i=1}^n x_i
$$
and let $\Pi_C(x)$ be the projection of $x$ onto $C$. If
$$
  \langle x_{n+1}-\Pi_C(\bar x_n),\,
          \bar x_n-\Pi_C(\bar x_n)\rangle\le 0
  \quad\text{for all }n,
$$
then
$$
  d(\bar x_n,C)\to 0.
$$

## References

- [MFoGT, Section 2.8, Exercise 4(1)] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Deterministic approachability criterion for Cesaro averages.
