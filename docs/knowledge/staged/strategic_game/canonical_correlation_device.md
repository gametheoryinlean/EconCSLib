---
id: game_theory.strategic_game.correlated.canonical_correlation_device
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Canonical Correlation Device
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.mixed_strategy
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - correlated-equilibrium
  - correlation-device
---

# Canonical Correlation Device

For a finite strategic game with action sets $(A_i)_{i\in I}$, a canonical
correlation device is a probability distribution $\mu$ on the product
$A=\prod_i A_i$.

Before play, the device draws an action profile $a\in A$ according to $\mu$ and
privately recommends $a_i$ to player $i$. The recommendation is not binding:
after observing only $a_i$, player $i$ may obey or replace the recommendation
by another action.

The device is canonical because its signals are the actions themselves. General
private signals can be reduced to this canonical form by considering the
distribution of recommended actions and the incentive constraints for obeying
those recommendations.

## References

- [MFoGT, Chapter 7, Section 7.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Correlation devices for Aumann correlated equilibria.
