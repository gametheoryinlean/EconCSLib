---
id: game_theory.strategic_game.correlated.obedience_condition
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Obedience Condition
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.recommendation_strategy
  - game_theory.strategic_game.best_response
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - correlated-equilibrium
  - obedience
---

# Obedience Condition

Let $\mu$ be the mediator's distribution on pure strategy profiles. Obedience is
optimal when, after every recommendation $s_i$, player $i$ cannot improve by
switching to another action $t_i$:
$$
  \sum_{s_{-i}} \mu(s_i,s_{-i})\,g_i(s_i,s_{-i})
  \ge
  \sum_{s_{-i}} \mu(s_i,s_{-i})\,g_i(t_i,s_{-i}).
$$

## Proof Sketch

Condition on a received recommendation. If the inequality holds for every
possible replacement action, obedience is a best response in the induced
mediated game. Conversely, if obedience is a best response, comparing it with
the recommendation strategy that changes only $s_i$ to $t_i$ gives the
inequality.

## References

- [MSZ, Chapter 8, Thm. 8.5] Maschler, Solan, and Zamir, *Game Theory*. Obedience inequalities characterize equilibrium in the mediated game.
