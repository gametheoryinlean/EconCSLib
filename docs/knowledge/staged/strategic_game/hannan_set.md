---
id: game_theory.strategic_game.zero_sum.learning.hannan_set
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Hannan Set
kind: definition
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.external_regret
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - learning
  - regret
---

# Hannan Set

For player $i$, the Hannan set is the set of distributions $q\in\Delta(A)$ over
action profiles for which player $i$ has no profitable fixed-action
counterfactual:
$$
  \sum_{a\in A}q(a)g_i(a)
  \ge
  \sum_{a\in A}q(a)g_i(b_i,a_{-i})
  \quad\text{for every } b_i\in A_i.
$$

Equivalently, $q$ makes player $i$'s realized action payoff at least as good as
the payoff from any single action chosen in hindsight.

The intersection of the Hannan sets over all players is the distributional
target reached when every player has no external regret. It is weaker than the
correlated-equilibrium set because it does not condition deviations on the
recommended action.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Hannan set associated to no-external-regret play.
