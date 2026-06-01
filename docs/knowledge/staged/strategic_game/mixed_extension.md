---
id: game_theory.strategic_game.core.mixed_extension
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Mixed Extension Of A Strategic Game
kind: definition
status: staged
uses:
  - game_theory.strategic_game.core.mixed_strategy
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.MixedStrategy
  declarations:
    - StrategicGame.expectedPayoff
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - mixed-strategy
---

# Mixed Extension Of A Strategic Game

For a finite strategic game $G$, its mixed extension $\widetilde G$ has player
$i$'s strategy set $\Delta(S_i)$ and payoff
$$
  \widetilde g_i(\sigma)
  =
  \sum_{s=(s_1,\ldots,s_N)\in S}
    \left(\prod_{j\in I}\sigma_j(s_j)\right) g_i(s).
$$
This is the multilinear extension of the pure payoff function.

## References

- [MFoGT, Section 1.3.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed extension by expected payoff.
- [MFoGT, Section 4.6] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Finite mixed extension with multilinear payoff.
