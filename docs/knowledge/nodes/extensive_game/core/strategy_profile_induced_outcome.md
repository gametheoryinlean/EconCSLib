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
    - EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution
    - EconCSLib.GameTheory.ExtensiveGame.Observed.Game
    - EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE
  declarations:
    - Arena.HistoryPolicy
    - ExtensiveGame.stoppedPayoff
    - ExtensiveGame.ObservedGame.PureProfile
    - ExtensiveGame.ObservedGame.PureProfile.actionAt
    - ExtensiveGame.ObservedGame.stoppedPayoff
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

A pure strategy profile $\sigma=(\sigma_i)_{i\in I}$ specifies an action at
every decision information state. In a terminating extensive-form game,
starting from the origin and following the action prescribed by the controlling
player gives a unique terminal outcome
$$
  F(\sigma)\in R.
$$
Payoffs under the strategy profile are then $g_i(F(\sigma))$.

For an inductive finite `GameTree`, `GameTree.outcome` is total because
termination is structural. For a general `ExtensiveGame`, execution is instead
history-sensitive and fuel-bounded: `ExtensiveGame.stoppedPayoff` and
`ObservedGame.stoppedPayoff` return `none` when the supplied fuel expires
before a terminal history. Thus the general API does not pretend that arbitrary
arenas terminate.

## References

- [MFoGT, Section 6.2.2] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. A strategy profile induces a unique terminal outcome.
