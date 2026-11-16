---
id: game_theory.strategic_game.zero_sum.learning.calibrated_strategy_exists
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Epsilon-Calibrated Strategy Exists
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.calibrated_strategy
  - game_theory.strategic_game.zero_sum.learning.internal_regret
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Calibration
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Process
  declarations:
    - StrategicGame.IsEpsilonCalibrated
    - StrategicGame.NoRegretProbability.IsEpsilonCalibratedAE
    - StrategicGame.NoRegretProbability.exists_forecastGrid_meshLe
    - StrategicGame.NoRegretProbability.isEpsilonCalibrated_of_hasNoInternalRegret
    - StrategicGame.NoRegretProbability.exists_forecastRule_isEpsilonCalibratedOnGeneratedProcessesAE
    - StrategicGame.NoRegretProbability.exists_forecastRule_isEpsilonCalibratedAE_against_predictable
verification:
  statement: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - calibration
  - existence
---

# Epsilon-Calibrated Strategy Exists

For every $\varepsilon>0$ in a finite prediction problem, there exists an
$\varepsilon$-calibrated randomized strategy.

## Proof Sketch

Choose a finite grid in the outcome simplex with sufficiently small Euclidean
mesh and run a no-internal-regret procedure with the grid points as actions and
negative squared forecast loss as payoff. The internal-regret inequalities
compare each announced forecast with a nearby grid point for its empirical
conditional outcome distribution. A finite sum and Cauchy--Schwarz then bound
the calibration error by the grid mesh.

The formalization includes both a reusable reduction for an already-generated
predictable process and an Ionescu--Tulcea construction of the trajectory law
for every finite-history predictable outcome rule, with the required
almost-sure calibration statement under that law.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of calibrated strategies via the learning framework.
