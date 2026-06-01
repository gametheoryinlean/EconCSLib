---
id: game_theory.strategic_game.zero_sum.learning.calibrated_strategy_exists
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Calibrated Strategy Exists
kind: theorem
status: staged
uses:
  - game_theory.strategic_game.zero_sum.learning.calibrated_strategy
  - game_theory.strategic_game.zero_sum.approachability.blackwell_b_set_approachability
verification:
  statement: accepted
  proof: gap
tags:
  - strategic-game
  - learning
  - calibration
  - existence
---

# Calibrated Strategy Exists

In a finite prediction problem, there exists a calibrated strategy.

## Proof Sketch

The standard route encodes calibration errors as vector payoffs and applies an
approachability argument to the closed convex set where every conditional
forecasting error is nonpositive. The resulting strategy drives the average
calibration-error vector to that set, which is exactly the calibration property.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Existence of calibrated strategies via the learning framework.
