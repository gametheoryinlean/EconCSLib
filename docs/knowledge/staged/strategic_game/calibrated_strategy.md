---
id: game_theory.strategic_game.zero_sum.learning.calibrated_strategy
primary_topic: game_theory.zero_sum
topics:
  - game_theory.zero_sum
  - game_theory.zero_sum.learning
title: Calibrated Strategy
kind: definition
status: staged
lean:
  modules:
    - EconCSLib.GameTheory.StrategicGame.NoRegret.Calibration
  declarations:
    - StrategicGame.ForecastGrid
    - StrategicGame.calibrationResidual
    - StrategicGame.directCalibrationError
    - StrategicGame.calibrationError
    - StrategicGame.directCalibrationError_eq_calibrationError
    - StrategicGame.isEpsilonCalibrated_iff_directCalibrationError
    - StrategicGame.IsEpsilonCalibrated
    - StrategicGame.NoRegretProbability.IsEpsilonCalibratedAE
    - StrategicGame.NoRegretProbability.IsEpsilonCalibratedOnGeneratedProcessesAE
verification:
  definition: accepted
  proof: accepted
  alignment: aligned
tags:
  - strategic-game
  - learning
  - calibration
---

# Calibrated Strategy

A calibrated strategy is a forecasting or learning procedure whose announced
probabilities are asymptotically consistent with the empirical frequencies that
follow those announcements.

In a finite prediction problem, suppose the procedure announces forecasts in a
finite grid $V$ of probability vectors. Let $|N_n(v)|/n$ be the empirical use
frequency of $v$, and let $\bar\omega_n(v)$ be the empirical outcome
distribution on the dates when $v$ was announced. The finite-grid calibration
error is
$$
  \sum_{v\in V}\frac{|N_n(v)|}{n}
    \lVert \bar\omega_n(v)-v\rVert_2.
$$
Equivalently, in the direct residual-vector form displayed in MFoGT, it is
$$
  \sum_{v\in V}
  \left\lVert
    \frac1n\sum_{\{m\le n:\,\phi_m=v\}}(X_m-v)
  \right\rVert_2.
$$
The Lean theorem `directCalibrationError_eq_calibrationError` proves this
identity, including forecasts that have not been used, and
`isEpsilonCalibrated_iff_directCalibrationError` restates the asymptotic
predicate directly in the source's notation.

Following MFoGT's finite-grid calibration definition, a randomized procedure is
$\varepsilon$-calibrated if the limit superior of this error is at most
$\varepsilon$ almost surely, for every admissible outcome process.

Calibration is stronger than merely having small average prediction error: it
requires frequency-weighted conditional accuracy on the subsequences selected
by the forecasts themselves. Merely using a forecast infinitely often is not
enough to force its unweighted conditional error to vanish when its asymptotic
use frequency is zero.

## References

- [MFoGT, Chapter 7, Section 7.3] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Calibrated strategies in the learning framework.
