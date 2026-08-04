---
id: game_theory.strategic_game.correlated.correlated_equilibrium_exists
primary_topic: game_theory.strategic_game
topics:
  - game_theory.strategic_game
  - game_theory.strategic_game.bayesian_correlated
title: Correlated Equilibrium Exists In Finite Games
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.correlated.nash_induces_correlated_equilibrium
  - game_theory.strategic_game.equilibrium.nash_existence_finite_games
  - game_theory.strategic_game.zero_sum.learning.no_internal_regret_correlated_convergence
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.CorrelatedEq
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Process
  declarations:
    - StrategicGame.piProduct_mem_correlatedEquilibriumDistributions_of_mixedNashEquilibrium
    - StrategicGame.NoRegretProbability.correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - correlated-equilibrium
  - existence
---

# Correlated Equilibrium Exists In Finite Games

Every finite strategic-form game has at least one correlated equilibrium.

## Proof Sketch

The formalized proof uses MFoGT's no-internal-regret learning route. Let every
player independently run the finite internal-regret procedure.
The empirical distribution approaches the correlated-equilibrium set almost
surely, so that set must be nonempty.

The classical alternative is also formalized: apply Nash's theorem and use
MSZ's proved Nash-product bridge from a mixed Nash equilibrium to its product
correlated distribution.

## References

- [MSZ, Chapter 8, Cor. 8.8] Maschler, Solan, and Zamir, *Game Theory*. Every finite strategic-form game has a correlated equilibrium.
- [MFoGT, Chapter 7, Proposition 7.3.18 and the following discussion] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Internal-regret learning yields correlated-equilibrium convergence and existence.
