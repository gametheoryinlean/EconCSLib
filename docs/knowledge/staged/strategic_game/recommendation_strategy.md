---
id: game_theory.strategic_game.correlated.recommendation_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Recommendation Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.correlated.mediated_game
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - correlated-equilibrium
---

# Recommendation Strategy

In the mediated game, a recommendation strategy for player $i$ maps each
recommended action $s_i$ to the action that player will actually play.

The obedient recommendation strategy is the identity strategy: after receiving
recommendation $s_i$, player $i$ plays $s_i$.

## References

- [MSZ, Chapter 8, Def. 8.4] Maschler, Solan, and Zamir, *Game Theory*. Recommendation strategies in the induced mediated game.
