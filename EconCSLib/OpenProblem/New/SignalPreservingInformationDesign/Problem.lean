/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Semicontinuity.Basic

/-!
# 22. Signal-preserving information design
-/



section

/-!
## A signal-preserving two-thirds approximation

[CLTTF, Explainable Information Design, Sections 2 and 3.2] motivates this
uniform-prior question. Utilities are arbitrary bounded functions as in the open
problem, without adding the paper's upper-semicontinuity assumption. Both optima are
therefore suprema, not asserted maxima. Empty signals and repeated cuts represent at
most K signals.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

open MeasureTheory

/-- A finite signaling kernel for the uniform prior, extended by zero outside the unit
interval. Kernel measurability imposes no regularity on utility. -/
structure UniformSignalScheme (K : ℕ) where
  weight : Fin K → ℝ → ℝ
  measurable_weight : ∀ s, Measurable (weight s)
  nonnegative : ∀ s θ, 0 ≤ weight s θ
  support : ∀ s θ, θ ∉ Set.Icc (0 : ℝ) 1 → weight s θ = 0
  sum_one : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (∑ s, weight s θ) = 1

/-- Ex-ante signal probability under the uniform distribution on an interval of length
one. -/
noncomputable def signalProbability
    {K : ℕ} (scheme : UniformSignalScheme K) (s : Fin K) : ℝ :=
  ∫ θ : ℝ, scheme.weight s θ ∂volume

/-- Posterior mean; a zero-probability signal contributes zero payoff regardless of the
totalized division convention. -/
noncomputable def posteriorMean
    {K : ℕ} (scheme : UniformSignalScheme K) (s : Fin K) : ℝ :=
  (∫ θ : ℝ, θ * scheme.weight s θ ∂volume) /
    signalProbability scheme s

/-- The finite probability-weighted sum of utilities of posterior means. -/
noncomputable def schemePayoff
    {K : ℕ} (utility : ℝ → ℝ) (scheme : UniformSignalScheme K) : ℝ :=
  ∑ s, signalProbability scheme s * utility (posteriorMean scheme s)

/-- K consecutive intervals; repeated thresholds are allowed. Endpoint and monotonicity
conditions imply all cuts lie in the unit interval. -/
structure IntervalPartition (K : ℕ) where
  cut : Fin (K + 1) → ℝ
  left_endpoint : cut 0 = 0
  right_endpoint : cut (Fin.last K) = 1
  monotone : Monotone cut

/-- Under the uniform prior, interval mass is its length and its posterior mean is the
midpoint. Zero-length intervals contribute zero. -/
noncomputable def intervalPartitionPayoff
    {K : ℕ} (utility : ℝ → ℝ) (partition : IntervalPartition K) : ℝ :=
  ∑ i : Fin K,
    (partition.cut i.succ - partition.cut i.castSucc) *
      utility ((partition.cut i.castSucc + partition.cut i.succ) / 2)

/-- Supremum over every kernel with at most K signals, without an attainment claim. -/
noncomputable def generalOPT (K : ℕ) (utility : ℝ → ℝ) : ℝ :=
  ⨆ scheme : UniformSignalScheme K, schemePayoff utility scheme

/-- Supremum over partitions with the same signal budget K. -/
noncomputable def partitionalOPT (K : ℕ) (utility : ℝ → ℝ) : ℝ :=
  ⨆ partition : IntervalPartition K, intervalPartitionPayoff utility partition

/-- The original same-budget inequality for arbitrary bounded utility, without continuity,
measurability, concavity, or rational-representation assumptions. -/
def SignalPreservingTwoThirdsStatement : Prop :=
  ∀ K : ℕ, 2 ≤ K →
    ∀ utility : ℝ → ℝ,
      (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ utility x ∧ utility x ≤ 1) →
      (2 / 3 : ℝ) * generalOPT K utility ≤ partitionalOPT K utility

end EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

/-- The two-thirds guarantee between the two payoff suprema. -/
theorem signalPreservingInformationDesign :
    answer(sorry) ↔ SignalPreservingTwoThirdsStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign
