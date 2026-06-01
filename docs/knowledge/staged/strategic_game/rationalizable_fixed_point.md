---
id: game_theory.strategic_game.dominance.rationalizable_fixed_point
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.dominance
title: Rationalizable Set As Largest Best-Response Fixed Set
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.dominance.rationalizable_strategy
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - rationalizability
  - fixed-point
---

# Rationalizable Set As Largest Best-Response Fixed Set

Let $G$ be a compact continuous game. The rationalizable set
$S^\infty=\prod_i S_i^\infty$ is nonempty and compact. It is a fixed set of the
best-response correspondence and is the largest subset $L\subseteq S$ satisfying
$$
  L\subseteq BR(L).
$$

## Proof Sketch

Compactness and continuity imply upper semicontinuity of the best-response
correspondence. By induction, every $S(k)$ is nonempty compact and the sequence is
decreasing, so the intersection is nonempty compact. Upper semicontinuity gives
$S^\infty\subseteq BR(S^\infty)$, while monotonicity of the construction gives
$BR(S^\infty)\subseteq S^\infty$. Any set $L$ satisfying $L\subseteq BR(L)$ is
contained in every $S(k)$, hence in $S^\infty$.

## References

- [MFoGT, Prop. 4.4.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. S_infty is nonempty compact and the largest L satisfying L subset BR(L).
