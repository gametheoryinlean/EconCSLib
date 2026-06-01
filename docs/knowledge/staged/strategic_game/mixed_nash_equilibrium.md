---
id: game_theory.strategic_game.equilibrium.mixed_nash_equilibrium
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.equilibrium
title: Mixed Nash Equilibrium
kind: definition
status: staged
uses:
  - game_theory.strategic_game.nash_equilibrium
  - game_theory.strategic_game.core.mixed_extension
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.MixedStrategy
  declarations:
    - StrategicGame.IsMixedNashEq
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - strategic-game
  - mixed-strategy
  - nash-equilibrium
---

# Mixed Nash Equilibrium

A mixed equilibrium of a finite strategic game $G$ is a Nash equilibrium of its
mixed extension $\widetilde G$.

Equivalently, a mixed profile $\sigma$ is a mixed Nash equilibrium if for every
player $i$ and every pure deviation $t_i\in S_i$,
$$
  \widetilde g_i(t_i,\sigma_{-i})
  \le
  \widetilde g_i(\sigma_i,\sigma_{-i}).
$$

## References

- [MFoGT, Def. 4.6.1] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed equilibrium of a finite game.
