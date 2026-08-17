/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators unitInterval

namespace EconCSLib.OpenProblem.EconCSBench.SignalPreservingInformationDesign

open MeasureTheory

/-- A `K`-signal scheme under the uniform prior.  `weight s θ` is the
conditional probability of signal `s` in state `θ`; it is zero off `[0,1]`. -/
structure UniformSignalScheme (K : ℕ) where
  /-- State-dependent signal probabilities. -/
  weight : Fin K → ℝ → ℝ
  /-- Measurability of each signal rule. -/
  measurable_weight : ∀ s, Measurable (weight s)
  /-- Signal probabilities are nonnegative. -/
  nonnegative : ∀ s θ, 0 ≤ weight s θ
  /-- Weights vanish outside the state interval. -/
  support : ∀ s θ, θ ∉ Set.Icc (0 : ℝ) 1 → weight s θ = 0
  /-- Probabilities sum to one in every state in `[0,1]`. -/
  sum_one : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (∑ s, weight s θ) = 1

/-- Ex-ante probability of a signal. -/
noncomputable def signalProbability
    {K : ℕ} (scheme : UniformSignalScheme K) (s : Fin K) : ℝ :=
  ∫ θ : ℝ, scheme.weight s θ ∂volume

/-- Posterior mean induced by a signal.  Zero-probability signals contribute
zero to the objective, so Lean's total division convention is harmless. -/
noncomputable def posteriorMean
    {K : ℕ} (scheme : UniformSignalScheme K) (s : Fin K) : ℝ :=
  (∫ θ : ℝ, θ * scheme.weight s θ ∂volume) /
    signalProbability scheme s

/-- Designer payoff of a general scheme. -/
noncomputable def schemePayoff
    {K : ℕ} (utility : ℝ → ℝ) (scheme : UniformSignalScheme K) : ℝ :=
  ∑ s, signalProbability scheme s * utility (posteriorMean scheme s)

/-- A partition of `[0,1]` into `K` consecutive intervals. -/
structure IntervalPartition (K : ℕ) where
  /-- The `K+1` ordered cut points. -/
  cut : Fin (K + 1) → ℝ
  /-- Left endpoint. -/
  left_endpoint : cut 0 = 0
  /-- Right endpoint. -/
  right_endpoint : cut (Fin.last K) = 1
  /-- Ordered thresholds. -/
  monotone : Monotone cut

/-- Designer payoff of an interval-partitional scheme under the uniform prior. -/
noncomputable def intervalPartitionPayoff
    {K : ℕ} (utility : ℝ → ℝ) (partition : IntervalPartition K) : ℝ :=
  ∑ i : Fin K,
    (partition.cut i.succ - partition.cut i.castSucc) *
      utility ((partition.cut i.castSucc + partition.cut i.succ) / 2)

/-- Optimal payoff over all schemes with at most `K` signals. -/
noncomputable def generalOPT (K : ℕ) (utility : ℝ → ℝ) : ℝ :=
  ⨆ scheme : UniformSignalScheme K, schemePayoff utility scheme

/-- Optimal payoff over `K` interval-partitional schemes. -/
noncomputable def partitionalOPT (K : ℕ) (utility : ℝ → ℝ) : ℝ :=
  ⨆ partition : IntervalPartition K, intervalPartitionPayoff utility partition

/-- Open-problem statement: no signal increase is needed for the `2/3`
explainability approximation under the uniform prior. -/
def SignalPreservingTwoThirdsStatement : Prop :=
  ∀ K : ℕ, 2 ≤ K →
    ∀ utility : ℝ → ℝ,
      (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ utility x ∧ utility x ≤ 1) →
      (2 / 3 : ℝ) * generalOPT K utility ≤ partitionalOPT K utility

/-- English version: "For the uniform prior, does every `K`-signal linear
information-design instance admit a `K`-interval-partitional scheme worth at
least two thirds of optimum?" -/
theorem signalPreservingTwoThirds :
    answer(sorry) ↔ SignalPreservingTwoThirdsStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.SignalPreservingInformationDesign
