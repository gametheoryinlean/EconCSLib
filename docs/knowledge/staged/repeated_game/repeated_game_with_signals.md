---
id: game_theory.repeated_game.core.signals
title: Repeated Game With Signals
kind: definition
status: staged
primary_topic: game_theory.repeated_game
topics:
  - game_theory.repeated_game
  - game_theory.repeated_game.core
uses:
  - game_theory.repeated_game.core.strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - repeated-game
  - signals
  - imperfect-monitoring
---

# Repeated Game With Signals

In a repeated game with signals, players do not necessarily observe the full
action profile after each stage. Instead, each player receives a private signal
whose distribution depends on the action profile.

Strategies are conditioned on each player's observed history of own actions and
signals. MFoGT stresses that imperfect monitoring can make the usual folk
theorem fail and that computing equilibrium payoff sets is difficult in general.

## References

- [MFoGT, Chapter 8, Section 8.6.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Repeated games with imperfect observation or imperfect monitoring.
