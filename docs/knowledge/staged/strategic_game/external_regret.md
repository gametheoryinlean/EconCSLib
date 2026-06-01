---
id: game_theory.strategic_game.zero_sum.learning.external_regret
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: External Regret
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - learning
  - regret
---

# External Regret

In repeated play of a finite strategic game, the external regret of player $i$
compares the realized payoff to the payoff that would have been obtained by
using one fixed action throughout the same history.

For a realized action history $(a^1,\ldots,a^n)$, the external regret against a
fixed alternative action $b_i\in A_i$ is
$$
  \frac1n\sum_{t=1}^n
  (g_i(b_i,a_{-i}^t)-g_i(a_i^t,a_{-i}^t)).
$$
A procedure has no external regret if the positive part of this quantity
converges to $0$ for every fixed alternative action.

External regret is weaker than internal regret: it tests only constant
counterfactual actions, not recommendation-contingent replacements.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. No-external-regret procedures in repeated play.
