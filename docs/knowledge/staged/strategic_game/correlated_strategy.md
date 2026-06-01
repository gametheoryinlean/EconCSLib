---
id: game_theory.strategic_game.correlated.correlated_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategy_profile
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - mixed-strategy
  - correlation
---

# Correlated Strategy

In a finite strategic game, a correlated strategy of the opponents of player $i$
is a probability distribution
$$
  \theta_{-i}\in \Delta(S_{-i})
$$
on the joint pure strategy set $S_{-i}=\prod_{j\ne i}S_j$.

This is more general than an independent mixed profile
$$
  \tau_{-i}\in \prod_{j\ne i}\Delta(S_j),
$$
because the latter induces only product distributions on $S_{-i}$.

A completely correlated strategy of the opponents is an interior point of
$\Delta(S_{-i})$, namely a distribution $\theta_{-i}$ with
$\theta_{-i}(s_{-i})>0$ for every $s_{-i}\in S_{-i}$.

## References

- [MFoGT, Section 4.3, before Def. 4.3.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Opponent correlated strategies are distributions on the joint pure strategy set S_{-i}.
- [MFoGT, Def. 4.3.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Completely correlated strategies are interior distributions on Delta(S_{-i}).
