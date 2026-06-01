---
id: game_theory.strategic_game.payoff_geometry.threat_point
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Threat Point
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - feasible-payoff
  - repeated-game
---

# Threat Point

Let $G$ be a finite strategic game. The punishment level, or threat point, for
player $i$ is
$$
  V_i=
  \min_{\sigma_{-i}\in\prod_{j\ne i}\Delta(S_j)}
  \max_{s_i\in S_i} g_i(s_i,\sigma_{-i}).
$$
It is the maximal punishment that the other players can enforce against player
$i$ using independent mixed strategies.

## References

- [MFoGT, Section 4.10.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Punishment level or threat point in a finite strategic game.
