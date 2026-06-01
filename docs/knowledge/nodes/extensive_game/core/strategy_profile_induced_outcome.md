---
id: game_theory.extensive_game.core.strategy_profile_induced_outcome
title: Strategy Profile And Induced Outcome
kind: definition
status: formalized
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.core
lean:
  modules:
    - EconCSLib.GameTheory.ExtensiveGame.Strategy
    - EconCSLib.GameTheory.ExtensiveGame.Play
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
  declarations:
    - ExtensiveGame.StrategyProfile
    - ExtensiveGame.StrategyProfile.actionAt
    - ExtensiveGame.finalPayoff
    - GameTree.outcome
verification:
  definition: accepted
  proof: not_applicable
  alignment: aligned
tags:
  - extensive-game
  - strategy
  - outcome
---

# Strategy Profile And Induced Outcome

A strategy profile $\sigma=(\sigma_i)_{i\in I}$ specifies one successor at every
decision position. Starting from the origin and following the successor prescribed
by the player who controls the current position gives a unique terminal outcome
$$
  F(\sigma)\in R.
$$
Payoffs under the strategy profile are then $g_i(F(\sigma))$.

## References

- [MFoGT, Section 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy profile induces a unique terminal outcome.
