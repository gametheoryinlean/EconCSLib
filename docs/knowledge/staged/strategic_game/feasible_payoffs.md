---
id: game_theory.strategic_game.payoff_geometry.feasible_payoffs
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.continuous
title: Feasible And Individually Rational Payoffs
kind: definition
status: staged
uses:
  - game_theory.strategic_game.payoff_geometry.threat_point
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - feasible-payoff
---

# Feasible And Individually Rational Payoffs

For a finite game, the one-shot feasible payoff set is
$$
  P_1=\{x\in\mathbb R^I:\exists\sigma\in\prod_{i\in I}\Delta(S_i),\ G(\sigma)=x\}.
$$
The set of feasible and individually rational one-shot payoffs is
$$
  R_1=\{x\in P_1:x_i\ge V_i\text{ for every }i\in I\},
$$
where $V_i$ is player $i$'s threat point.

## References

- [MFoGT, Section 4.10.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Feasible payoff set and individually rational payoffs in one-shot finite games.
