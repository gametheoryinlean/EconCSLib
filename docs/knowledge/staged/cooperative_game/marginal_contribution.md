---
id: game_theory.cooperative_game.marginal_contribution
title: Marginal Contribution
kind: definition
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.tu_game
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.ShapleyValue
  declarations:
    - CoalitionalGame.marginalContrib
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - coalitional-game
  - shapley-value
  - marginal-contribution
---

# Marginal Contribution

The **marginal contribution** of player $i$ to a coalition $S$ not
containing $i$ is
$$
  v(S \cup \{i\}) - v(S).
$$

This is the payoff increment created by adding $i$ to $S$. Shapley-value
formulae average this quantity over all possible predecessor coalitions.

## References

- [MSZ Ch.18, §18.2] Maschler, Solan, Zamir, *Game Theory*.
