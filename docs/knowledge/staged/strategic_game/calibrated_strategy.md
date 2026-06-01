---
id: game_theory.strategic_game.zero_sum.learning.calibrated_strategy
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Calibrated Strategy
kind: definition
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.external_regret
verification:
  definition: accepted
  proof: not_applicable
tags:
  - strategic-game
  - learning
  - calibration
---

# Calibrated Strategy

A calibrated strategy is a forecasting or learning procedure whose announced
probabilities are asymptotically consistent with the empirical frequencies that
follow those announcements.

In a finite prediction problem, if the procedure repeatedly announces forecasts
in a finite grid of probability vectors, calibration requires that for each
forecast $p$ used infinitely often, the empirical distribution of outcomes on
the dates where $p$ was announced converges to $p$.

Calibration is stronger than merely having small average prediction error: it
requires conditional accuracy on the subsequences selected by the forecasts
themselves.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Calibrated strategies in the learning framework.
