/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.SignalPreservingInformationDesign.Problem

/-!
# SignalPreservingInformationDesign: supporting material

Auxiliary definitions and lemmas for the problem statement.
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

/-- The kernel axioms bound every signal weight by one. -/
theorem UniformSignalScheme.weight_le_one {K : ℕ} (scheme : UniformSignalScheme K)
    (s : Fin K) (θ : ℝ) : scheme.weight s θ ≤ 1 := by
  by_cases h : θ ∈ Set.Icc (0 : ℝ) 1
  · calc
      scheme.weight s θ ≤ ∑ t, scheme.weight t θ :=
        Finset.single_le_sum (fun t _ => scheme.nonnegative t θ) (Finset.mem_univ s)
      _ = 1 := scheme.sum_one θ h
  · rw [scheme.support s θ h]
    exact zero_le_one

/-- Finite signal weights are integrable; the integral is not a nonintegrable fallback. -/
theorem UniformSignalScheme.integrable_weight {K : ℕ} (scheme : UniformSignalScheme K)
    (s : Fin K) : Integrable (scheme.weight s) (volume : Measure ℝ) := by
  have bound : Integrable ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine bound.mono' (scheme.measurable_weight s).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (scheme.nonnegative s θ)]
    by_cases h : θ ∈ Set.Icc (0 : ℝ) 1
    · simpa [Set.indicator_of_mem h] using scheme.weight_le_one s θ
    · simp [Set.indicator_of_notMem h, scheme.support s θ h]

/-- Every signal has nonnegative ex-ante probability. -/
theorem signalProbability_nonnegative {K : ℕ} (scheme : UniformSignalScheme K)
    (s : Fin K) : 0 ≤ signalProbability scheme s :=
  integral_nonneg (scheme.nonnegative s)

/-- Zero-probability signals use the harmless totalized posterior mean zero. -/
theorem posteriorMean_of_zero_probability {K : ℕ} (scheme : UniformSignalScheme K)
    (s : Fin K) (h : signalProbability scheme s = 0) : posteriorMean scheme s = 0 := by
  simp [posteriorMean, h]

/-- Every posterior mean belongs to the utility domain, including zero-mass signals. -/
theorem posteriorMean_mem_unitInterval {K : ℕ} (scheme : UniformSignalScheme K)
    (s : Fin K) : posteriorMean scheme s ∈ Set.Icc (0 : ℝ) 1 := by
  have nonneg : ∀ θ, 0 ≤ θ * scheme.weight s θ := by
    intro θ
    by_cases h : θ ∈ Set.Icc (0 : ℝ) 1
    · exact mul_nonneg h.1 (scheme.nonnegative s θ)
    · simp [scheme.support s θ h]
  have bound : ∀ θ, θ * scheme.weight s θ ≤ scheme.weight s θ := by
    intro θ
    by_cases h : θ ∈ Set.Icc (0 : ℝ) 1
    · calc
        θ * scheme.weight s θ ≤ 1 * scheme.weight s θ :=
          mul_le_mul_of_nonneg_right h.2 (scheme.nonnegative s θ)
        _ = scheme.weight s θ := one_mul _
    · simp [scheme.support s θ h]
  have moment_integrable : Integrable (fun θ => θ * scheme.weight s θ) volume := by
    refine (scheme.integrable_weight s).mono'
      (measurable_id.mul (scheme.measurable_weight s)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (nonneg θ)]
      exact bound θ
  have hn : 0 ≤ ∫ θ : ℝ, θ * scheme.weight s θ ∂volume := integral_nonneg nonneg
  have hb : (∫ θ : ℝ, θ * scheme.weight s θ ∂volume) ≤ signalProbability scheme s :=
    integral_mono moment_integrable (scheme.integrable_weight s) bound
  have hp := signalProbability_nonnegative scheme s
  refine ⟨div_nonneg hn hp, ?_⟩
  by_cases hz : signalProbability scheme s = 0
  · simp [posteriorMean, hz]
  · exact (div_le_one (lt_of_le_of_ne hp (Ne.symm hz))).2 hb

/-- Exact conversion is a separate, potentially stronger attainment question. -/
def ExactSignalPreservingConversionStatement : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ utility : ℝ → ℝ,
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1) →
    ∀ scheme : UniformSignalScheme K, ∃ partition : IntervalPartition K,
      (2 / 3 : ℝ) * schemePayoff utility scheme ≤ intervalPartitionPayoff utility partition

/-- The approximation version of conversion does not demand exact attainment. -/
def ApproximateSignalPreservingConversionStatement : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ utility : ℝ → ℝ,
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1) →
    ∀ scheme : UniformSignalScheme K, ∀ ε : ℝ, 0 < ε →
      ∃ partition : IntervalPartition K,
        (2 / 3 : ℝ) * schemePayoff utility scheme ≤
          intervalPartitionPayoff utility partition + ε

end EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

end


section

/-!
## Finite posterior support removes the utility-regularity gap

For a fixed finite signaling scheme, retain utility only at its posterior means. The
resulting finite nonnegative spikes are upper semicontinuous, preserve that scheme's
payoff, and never improve a partition's payoff. Consequently the universal supremum
inequality is equivalent to its upper-semicontinuous restriction.
-/

open MeasureTheory
open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

/-- A one-signal kernel, padded with zero-probability labels. -/
noncomputable def singleSignalScheme {K : ℕ} (hK : 0 < K) : UniformSignalScheme K where
  weight s θ := if s = ⟨0, hK⟩ then
    (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) θ else 0
  measurable_weight s := by
    by_cases hs : s = ⟨0, hK⟩
    · simpa only [hs, if_true] using
        (measurable_const.indicator measurableSet_Icc :
          Measurable ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))))
    · simpa only [hs, if_false] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
  nonnegative s θ := by
    split_ifs
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) θ
    · exact le_rfl
  support s θ hθ := by simp [Set.indicator_of_notMem hθ]
  sum_one θ hθ := by simp [Set.indicator_of_mem hθ]

/-- Positive signal budgets have admissible kernels. -/
theorem nonempty_uniformSignalScheme {K : ℕ} (hK : 0 < K) :
    Nonempty (UniformSignalScheme K) := ⟨singleSignalScheme hK⟩

/-- Equal-length intervals supply a partition for every positive budget. -/
noncomputable def equalIntervalPartition {K : ℕ} (hK : 0 < K) : IntervalPartition K where
  cut i := (i.val : ℝ) / K
  left_endpoint := by simp
  right_endpoint := by
    simp only [Fin.val_last]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK))
  monotone i j hij := div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg K)

theorem nonempty_intervalPartition {K : ℕ} (hK : 0 < K) :
    Nonempty (IntervalPartition K) := ⟨equalIntervalPartition hK⟩

/-- Each signal probability is at most the total unit-interval mass. -/
theorem signalProbability_le_one {K : ℕ} (scheme : UniformSignalScheme K) (s : Fin K) :
    signalProbability scheme s ≤ 1 := by
  have integrableBound : Integrable
      ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have bound : ∀ θ, scheme.weight s θ ≤
      (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    by_cases hθ : θ ∈ Set.Icc (0 : ℝ) 1
    · simpa only [Set.indicator_of_mem hθ] using scheme.weight_le_one s θ
    · simp only [Set.indicator_of_notMem hθ, scheme.support s θ hθ, le_refl]
  have := integral_mono (scheme.integrable_weight s) integrableBound bound
  simpa [signalProbability, integral_indicator_const, Real.volume_real_Icc] using this

theorem IntervalPartition.cut_mem_unitInterval {K : ℕ}
    (partition : IntervalPartition K) (i : Fin (K + 1)) :
    partition.cut i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← partition.left_endpoint]
    exact partition.monotone (Fin.zero_le i)
  · rw [← partition.right_endpoint]
    exact partition.monotone (Fin.le_last i)

theorem IntervalPartition.intervalLength_nonnegative {K : ℕ}
    (partition : IntervalPartition K) (i : Fin K) :
    0 ≤ partition.cut i.succ - partition.cut i.castSucc :=
  sub_nonneg.mpr (partition.monotone (by change i.val ≤ i.val + 1; omega))

theorem IntervalPartition.midpoint_mem_unitInterval {K : ℕ}
    (partition : IntervalPartition K) (i : Fin K) :
    (partition.cut i.castSucc + partition.cut i.succ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := partition.cut_mem_unitInterval i.castSucc
  have hright := partition.cut_mem_unitInterval i.succ
  constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]

/-- A coarse finite bound suffices for the conditional supremum. -/
theorem schemePayoff_le_signalCount {K : ℕ} (utility : ℝ → ℝ)
    (bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1)
    (scheme : UniformSignalScheme K) : schemePayoff utility scheme ≤ K := by
  calc
    schemePayoff utility scheme ≤ ∑ _s : Fin K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      have hu := bounded _ (posteriorMean_mem_unitInterval scheme s)
      exact mul_le_one₀ (signalProbability_le_one scheme s) hu.1 hu.2
    _ = K := by simp

theorem intervalPartitionPayoff_le_signalCount {K : ℕ} (utility : ℝ → ℝ)
    (bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1)
    (partition : IntervalPartition K) : intervalPartitionPayoff utility partition ≤ K := by
  calc
    intervalPartitionPayoff utility partition ≤ ∑ _i : Fin K, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hu := bounded _ (partition.midpoint_mem_unitInterval i)
      have hleft := partition.cut_mem_unitInterval i.castSucc
      have hright := partition.cut_mem_unitInterval i.succ
      exact mul_le_one₀ (by linarith [hleft.1, hright.2]) hu.1 hu.2
    _ = K := by simp

theorem bddAbove_schemePayoffs (K : ℕ) (utility : ℝ → ℝ)
    (bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1) :
    BddAbove (Set.range (schemePayoff (K := K) utility)) := by
  refine ⟨K, ?_⟩
  rintro _ ⟨scheme, rfl⟩
  exact schemePayoff_le_signalCount utility bounded scheme

theorem bddAbove_partitionPayoffs (K : ℕ) (utility : ℝ → ℝ)
    (bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1) :
    BddAbove (Set.range (intervalPartitionPayoff (K := K) utility)) := by
  refine ⟨K, ?_⟩
  rintro _ ⟨partition, rfl⟩
  exact intervalPartitionPayoff_le_signalCount utility bounded partition

/-- Pointwise utility domination on the actual domain passes to every partition. -/
theorem intervalPartitionPayoff_mono {K : ℕ} {u v : ℝ → ℝ}
    (dominated : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x) (partition : IntervalPartition K) :
    intervalPartitionPayoff u partition ≤ intervalPartitionPayoff v partition := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (dominated _ (partition.midpoint_mem_unitInterval i))
    (partition.intervalLength_nonnegative i)

theorem partitionalOPT_mono {K : ℕ} (hK : 0 < K) {u v : ℝ → ℝ}
    (bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v x ∧ v x ≤ 1)
    (dominated : ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x) :
    partitionalOPT K u ≤ partitionalOPT K v := by
  letI := nonempty_intervalPartition hK
  apply ciSup_le
  intro partition
  exact (intervalPartitionPayoff_mono dominated partition).trans
    (le_ciSup (bddAbove_partitionPayoffs K v bounded) partition)

/-- Utility retained only on a finite set of posterior means. -/
noncomputable def finiteUtilityRestriction (points : Finset ℝ) (utility : ℝ → ℝ) : ℝ → ℝ :=
  (points : Set ℝ).indicator utility

/-- Nonnegative finite spikes are globally upper semicontinuous, regardless of regularity
of the unrestricted utility. -/
theorem finiteUtilityRestriction_upperSemicontinuous (points : Finset ℝ) (utility : ℝ → ℝ)
    (nonnegative : ∀ x ∈ points, 0 ≤ utility x) :
    UpperSemicontinuous (finiteUtilityRestriction points utility) := by
  have hnonnegative : ∀ x, 0 ≤ finiteUtilityRestriction points utility x := by
    intro x
    exact Set.indicator_nonneg (fun y hy => nonnegative y hy) x
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro threshold
  by_cases hthreshold : threshold ≤ 0
  · have all : finiteUtilityRestriction points utility ⁻¹' Set.Ici threshold = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
      exact hthreshold.trans (hnonnegative x)
    rw [all]
    exact isClosed_univ
  · apply Set.Finite.isClosed
    apply points.finite_toSet.subset
    intro x hx
    by_contra hnot
    have zero : finiteUtilityRestriction points utility x = 0 :=
      Set.indicator_of_notMem hnot utility
    have : threshold ≤ 0 := by simpa only [Set.mem_preimage, Set.mem_Ici, zero] using hx
    exact hthreshold this

/-- The source's utility regularity restriction, with no extra attainment claim. -/
def UpperSemicontinuousSignalPreservingTwoThirdsStatement : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ utility : ℝ → ℝ,
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ utility x ∧ utility x ≤ 1) →
    UpperSemicontinuousOn utility (Set.Icc (0 : ℝ) 1) →
      (2 / 3 : ℝ) * generalOPT K utility ≤ partitionalOPT K utility

/-- Upper-semicontinuous utility is sufficient for the universal same-budget supremum
question. No maximizer or finite representation of utility is needed. -/
theorem signalPreservingTwoThirds_iff_upperSemicontinuous :
    SignalPreservingTwoThirdsStatement ↔
      UpperSemicontinuousSignalPreservingTwoThirdsStatement := by
  constructor
  · intro h K hK utility bounded _
    exact h K hK utility bounded
  · intro h K hK utility bounded
    classical
    have positive : 0 < K := by omega
    letI := nonempty_uniformSignalScheme positive
    rw [mul_comm (2 / 3 : ℝ)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)).mp
    apply ciSup_le
    intro scheme
    let points : Finset ℝ := Finset.univ.image (posteriorMean scheme)
    let restricted := finiteUtilityRestriction points utility
    have point_domain : ∀ x ∈ points, x ∈ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx
      exact posteriorMean_mem_unitInterval scheme s
    have restricted_bounded : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ restricted x ∧ restricted x ≤ 1 := by
      intro x hx
      by_cases hp : x ∈ points
      · simpa only [restricted, finiteUtilityRestriction, Set.indicator_of_mem hp] using bounded x hx
      · simp only [restricted, finiteUtilityRestriction, Set.indicator_of_notMem hp]
        exact ⟨le_rfl, zero_le_one⟩
    have restricted_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, restricted x ≤ utility x := by
      intro x hx
      by_cases hp : x ∈ points
      · simp only [restricted, finiteUtilityRestriction, Set.indicator_of_mem hp, le_refl]
      · simpa only [restricted, finiteUtilityRestriction, Set.indicator_of_notMem hp] using (bounded x hx).1
    have usc : UpperSemicontinuous restricted :=
      finiteUtilityRestriction_upperSemicontinuous points utility
        (fun x hx => (bounded x (point_domain x hx)).1)
    have preserved : schemePayoff restricted scheme = schemePayoff utility scheme := by
      apply Finset.sum_congr rfl
      intro s _
      have hp : posteriorMean scheme s ∈ points := Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
      simp only [restricted, finiteUtilityRestriction, Set.indicator_of_mem hp]
    have source_bound := h K hK restricted restricted_bounded
      (usc.upperSemicontinuousOn (Set.Icc (0 : ℝ) 1))
    have scheme_bound : (2 / 3 : ℝ) * schemePayoff utility scheme ≤ partitionalOPT K utility := by
      rw [← preserved]
      exact (mul_le_mul_of_nonneg_left
        (le_ciSup (bddAbove_schemePayoffs K restricted restricted_bounded) scheme)
        (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans
        (source_bound.trans (partitionalOPT_mono positive bounded restricted_le))
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 / 3)).mpr (by simpa [mul_comm] using scheme_bound)

end EconCSLib.OpenProblem.New.EconCSBench.SignalPreservingInformationDesign

end
