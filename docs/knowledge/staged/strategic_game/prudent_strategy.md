---
id: game_theory.strategic_game.payoff_geometry.prudent_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Prudent Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - prudence
---

# Prudent Strategy

A mixed strategy $\sigma_i\in\Delta(S_i)$ is prudent for player $i$ if, for every
pure opponent profile $s_{-i}\in S_{-i}$,
$$
  g_i(\sigma_i,s_{-i})\ge
  \max_{\tau_i\in\Delta(S_i)}
  \min_{t_{-i}\in S_{-i}} g_i(\tau_i,t_{-i}).
$$
Thus a prudent strategy guarantees player $i$ at least the player's maxmin
security payoff.

## References

- [MFoGT, Section 4.10.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Prudent strategy and prudent payoff in a finite game.
