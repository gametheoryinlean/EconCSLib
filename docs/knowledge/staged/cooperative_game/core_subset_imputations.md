---
id: game_theory.cooperative_game.core_subset_imputations
title: Core Payoffs Are Imputations
kind: theorem
status: staged
primary_topic: game_theory.cooperative_game
topics:
  - game_theory.cooperative_game
  - game_theory.cooperative_game.core
uses:
  - game_theory.cooperative_game.core
  - game_theory.cooperative_game.imputation
lean:
  modules:
    - EconCSLib.GameTheory.CoalitionalGame.Core
  declarations:
    - CoalitionalGame.core_subset_imputations
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - coalitional-game
  - core
  - imputation
---

# Core Payoffs Are Imputations

Every payoff vector in the core is an imputation.

Indeed, the core definition already contains efficiency:
$$
  \sum_{i \in N} x_i = v(N).
$$
For individual rationality, apply the core's coalitional rationality
condition to the singleton coalition $\{i\}$:
$$
  x_i = \sum_{j \in \{i\}} x_j \ge v(\{i\}).
$$

Thus core membership implies both efficiency and individual rationality.

## References

- [MSZ Ch.17, Def 17.1-17.2] Maschler, Solan, Zamir, *Game Theory*.
