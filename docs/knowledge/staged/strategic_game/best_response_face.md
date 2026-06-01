---
id: game_theory.strategic_game.correlated.best_response_face
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Best Response Face
kind: proposition
status: staged
uses:
  - game_theory.strategic_game.best_response
  - game_theory.strategic_game.correlated.correlated_strategy
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - best-response
  - correlation
---

# Best Response Face

For a finite strategic game and a correlated opponent strategy
$\theta_{-i}\in\Delta(S_{-i})$, the best-response set
$BR_i(\theta_{-i})$ is a face of the simplex $\Delta(S_i)$.

The extreme points of this face are exactly the pure strategies of player $i$
that are best responses against $\theta_{-i}$.

## Proof Sketch

The expected payoff $m_i\mapsto g_i(m_i,\theta_{-i})$ is affine on
$\Delta(S_i)$. Maximizers of an affine function over a simplex form the convex
hull of the maximizing vertices, hence a simplex face.

## References

- [MFoGT, Section 4.3, before Def. 4.3.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. BR_i(theta_{-i}) is a simplex face whose extreme points are pure best responses.
