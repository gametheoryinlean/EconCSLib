---
id: game_theory.strategic_game.core.mixed_strategy
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.core
title: Mixed Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.strategic_game
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.MixedStrategy
  declarations:
    - MixedStrategy
    - StrategicGame.MixedProfile
    - StrategicGame.pureToMixed
    - StrategicGame.IsCompletelyMixed
    - StrategicGame.IsCompletelyMixedProfile
    - StrategicGame.uniformMixed
    - StrategicGame.uniformMixedProfile
    - StrategicGame.pureProfileToMixed
    - StrategicGame.deviateMixed
    - StrategicGame.IsCompletelyMixedProfile.player
    - StrategicGame.pureToMixed_not_isCompletelyMixed_of_ne
    - StrategicGame.uniformMixedProfile_isCompletelyMixed
    - StrategicGame.uniformMixed_apply
    - StrategicGame.uniformMixed_isCompletelyMixed
    - StrategicGame.uniformMixed_pos
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - mixed-strategy
---

# Mixed Strategy

A mixed strategy for player $i$ is a probability distribution over the strategy
set \(S_i\). When \(S_i\) is finite, a mixed strategy is a vector
\(x_i \in \Delta(S_i)\) in the standard simplex. Pure strategies are identified
with the Dirac measures (point masses) in the corresponding simplex.

A mixed profile is an element $\sigma=(\sigma_i)_{i\in I}\in\prod_{i\in I}\Delta(S_i)$.

## References

- [MSZ, Chapter 3] Maschler, Solan, and Zamir, *Game Theory*. Mixed strategies and mixed extensions.
- [MFoGT, Section 1.3.5] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed extensions and pure strategies as Dirac masses.
- [MFoGT, Section 4.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed strategy profile in $\Delta(S_i)$.
