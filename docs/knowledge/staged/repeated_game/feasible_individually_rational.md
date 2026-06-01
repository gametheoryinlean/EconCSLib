---
id: game_theory.repeated_game.core.feasible_individually_rational_payoffs
title: Repeated Feasible Individually Rational Payoffs
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.strategic_game.payoff_geometry.threat_point
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
  - feasible-payoff
---

# Repeated Feasible Individually Rational Payoffs

For a finite stage game, the repeated-game feasible payoff set is the convex hull
of pure action payoff vectors:
$$
  \operatorname{co} g(A)=g(\Delta(A)).
$$

For each player $i$, the independent minmax level is
$$
  v_i=
  \min_{x_{-i}\in\prod_{j\ne i}\Delta(A_j)}
  \max_{x_i\in\Delta(A_i)}g_i(x_i,x_{-i}).
$$
The feasible and individually rational set is
$$
  E=\{u\in\operatorname{co} g(A):u_i\ge v_i\text{ for every }i\}.
$$

## References

- [MFoGT, Chapter 8, Definitions 8.4.1 to 8.4.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Feasible payoffs, independent minmax levels, and individually rational payoffs.
