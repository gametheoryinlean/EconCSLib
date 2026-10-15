/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NoRegret.External
import EconCSLib.GameTheory.StrategicGame.ZeroSum.StochasticMatrix

/-!
# Internal regret

This module formalizes the internal-regret matrix, invariant-measure
orthogonality, and internal-regret matching of [MFoGT, Section 7.3.2].
It includes the conditional-process theorem and the ingredients used by
`NoRegret.Process` to construct its finite-history realization.

## References

* [MFoGT] Chapter 7, Section 7.3.2
-/

open Finset BigOperators Filter Topology
open scoped MeasureTheory

namespace StrategicGame

universe uK uL uN uS uΩ uOut

/-! ### Internal regret: MFoGT 7.3.2 -/

/-- The internal regret matrix `S(k, U)`, comparing replacement of the realized
move `j` by the alternative `ℓ`. -/
def internalRegretStage {K : Type uK} [DecidableEq K]
    (choice : K) (payoff : K → ℝ) (j ℓ : K) : ℝ :=
  if choice = j then payoff ℓ - payoff j else 0

/-- Average internal regret up to stage `n + 1`. -/
noncomputable def averageInternalRegret {K : Type uK} [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) (j ℓ : K) : ℝ :=
  ((n + 1 : ℝ)⁻¹) *
    ∑ t : Fin (n + 1), internalRegretStage (play t.val) (payoff t.val) j ℓ

/-- Realized-path internal-regret criterion. MFoGT Definition 7.3.5 is the
corresponding almost-sure property of a randomized strategy. -/
def HasNoInternalRegret {K : Type uK} [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) : Prop :=
  ∀ j ℓ : K, VanishesAboveZero fun n => posPart (averageInternalRegret play payoff n j ℓ)

/-- The maximum positive average internal regret at stage `n + 1`, a finite
scalar summary of the coordinatewise criterion in MFoGT Definition 7.3.5. -/
noncomputable def maximalPositiveAverageInternalRegret
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun jl : K × K =>
    posPart (averageInternalRegret play payoff n jl.1 jl.2)

/-- On a finite nonempty action set, coordinatewise no internal regret is
equivalent to vanishing of the maximum positive matrix entry. -/
theorem hasNoInternalRegret_iff_maximalPositiveAverageInternalRegret
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) :
    HasNoInternalRegret play payoff ↔
      VanishesAboveZero (maximalPositiveAverageInternalRegret play payoff) := by
  classical
  constructor
  · intro h ε hε
    choose N hN using fun jl : K × K => h jl.1 jl.2 ε hε
    refine ⟨∑ jl : K × K, N jl, fun n hn => ?_⟩
    unfold maximalPositiveAverageInternalRegret
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro jl _
    apply hN jl n
    exact le_trans
      (Finset.single_le_sum (fun jk _ => Nat.zero_le (N jk)) (Finset.mem_univ jl)) hn
  · intro h j ℓ ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    exact (Finset.le_sup' (fun jl : K × K =>
      posPart (averageInternalRegret play payoff n jl.1 jl.2))
        (Finset.mem_univ (j, ℓ))).trans (hN n hn)

/-- The maximum positive average internal regret is nonnegative. -/
lemma maximalPositiveAverageInternalRegret_nonneg
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) :
    0 ≤ maximalPositiveAverageInternalRegret play payoff n := by
  classical
  let k : K := Classical.choice (inferInstance : Nonempty K)
  exact (posPart_nonneg (averageInternalRegret play payoff n k k)).trans
    (Finset.le_sup' (fun jl : K × K =>
      posPart (averageInternalRegret play payoff n jl.1 jl.2))
        (Finset.mem_univ (k, k)))

/-- Finite maximum form of MFoGT Definition 7.3.5: no internal regret is
equivalent to convergence of the maximum positive matrix entry to zero. -/
theorem hasNoInternalRegret_iff_tendsto_maximalPositiveAverageInternalRegret_zero
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) :
    HasNoInternalRegret play payoff ↔
      Tendsto (maximalPositiveAverageInternalRegret play payoff) atTop (nhds 0) := by
  rw [hasNoInternalRegret_iff_maximalPositiveAverageInternalRegret]
  constructor
  · intro h
    exact Metric.tendsto_atTop.mpr fun ε hε => by
      obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
      exact ⟨N, fun n hn => by
        rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (maximalPositiveAverageInternalRegret_nonneg play payoff n)]
        exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
    exact ⟨N, fun n hn => by
      have hdist := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (maximalPositiveAverageInternalRegret_nonneg play payoff n)] at hdist
      exact hdist.le⟩

/-- A robust pathwise predicate: every bounded path remaining in the support of
the online rule satisfies internal consistency. This is stronger than MFoGT
Definition 7.3.5, whose randomized-strategy guarantee is almost sure. -/
def IsRobustPathwiseNoInternalRegretStrategy {K : Type uK} [Fintype K] [DecidableEq K]
    (σ : ExternalOnlineStrategy K) : Prop :=
  ∀ play payoff,
    IsSupportedByExternalStrategy σ play payoff →
    IsBoundedPayoffProcess payoff →
    HasNoInternalRegret play payoff

/-- The invariant-measure equation for a comparison matrix `A`.
Nonnegativity is required by the existence theorem used to choose such a
measure, but not by this equation or the orthogonality lemma below. -/
def IsInvariantMeasureFor {K : Type uK} [Fintype K]
    (A : K → K → ℝ) (μ : stdSimplex ℝ K) : Prop :=
  ∀ ℓ : K, ∑ k : K, μ.val k * A k ℓ = μ.val ℓ * ∑ k : K, A ℓ k

/-- Expected internal-regret matrix under mixed action `μ`. -/
noncomputable def expectedInternalRegret {K : Type uK} [Fintype K] [DecidableEq K]
    (μ : stdSimplex ℝ K) (U : K → ℝ) : K → K → ℝ :=
  fun j ℓ => ∑ k : K, μ.val k * internalRegretStage k U j ℓ

/-- Matrix inner product. -/
noncomputable def matrixInner {K : Type uK} [Fintype K]
    (A B : K → K → ℝ) : ℝ :=
  ∑ k : K, ∑ ℓ : K, A k ℓ * B k ℓ

/-- [MFoGT Lemma 7.3.6] Invariant measures cancel the expected internal-regret
matrix. Nonnegativity is needed to construct a suitable invariant measure, but
not for this algebraic identity once invariance is assumed. -/
theorem invariantMeasure_internalRegret_orthogonal {K : Type uK}
    [Fintype K] [DecidableEq K]
    (A : K → K → ℝ) (μ : stdSimplex ℝ K) (U : K → ℝ)
    (hμ : IsInvariantMeasureFor A μ) :
    matrixInner A (expectedInternalRegret μ U) = 0 := by
  have hEIR : ∀ j ℓ : K, expectedInternalRegret μ U j ℓ = μ.val j * (U ℓ - U j) := by
    intro j ℓ
    simp only [expectedInternalRegret, internalRegretStage]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · simp
    · intro k _ hk
      rw [if_neg hk, mul_zero]
  have hexpand : matrixInner A (expectedInternalRegret μ U)
      = (∑ j : K, ∑ ℓ : K, A j ℓ * (μ.val j * U ℓ))
        - ∑ j : K, ∑ ℓ : K, A j ℓ * (μ.val j * U j) := by
    simp only [matrixInner, hEIR, mul_sub, ← Finset.sum_sub_distrib]
  have hfirst : ∑ j : K, ∑ ℓ : K, A j ℓ * (μ.val j * U ℓ)
      = ∑ ℓ : K, μ.val ℓ * U ℓ * ∑ k : K, A ℓ k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    have : ∑ j : K, A j ℓ * (μ.val j * U ℓ) = U ℓ * ∑ j : K, μ.val j * A j ℓ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, hμ ℓ]
    ring
  have hsecond : ∑ j : K, ∑ ℓ : K, A j ℓ * (μ.val j * U j)
      = ∑ ℓ : K, μ.val ℓ * U ℓ * ∑ k : K, A ℓ k := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  rw [hexpand, hfirst, hsecond, sub_self]

/-! ### Internal-regret-matching rule from MFoGT Proposition 7.3.7 -/

/-- `posPart` distributes over multiplication by a positive scalar. -/
lemma posPart_pos_smul {c x : ℝ} (hc : 0 < c) : posPart (c * x) = c * posPart x := by
  unfold posPart
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc.le h), mul_zero]
  · rw [max_eq_left h, max_eq_left (mul_nonneg hc.le h)]

/-- `IsInvariantMeasureFor` is invariant under rescaling the comparison matrix by any
constant, since the defining identity is homogeneous (bilinear) in `A`. -/
lemma isInvariantMeasureFor_smul {K : Type uK} [Fintype K] {A : K → K → ℝ} {μ : stdSimplex ℝ K}
    (c : ℝ) (h : IsInvariantMeasureFor A μ) :
    IsInvariantMeasureFor (fun j ℓ => c * A j ℓ) μ := by
  intro ℓ
  have hrow : (∑ k : K, c * A ℓ k) = c * ∑ k : K, A ℓ k := by rw [Finset.mul_sum]
  have hcol : (∑ k : K, μ.val k * (c * A k ℓ)) = c * ∑ k : K, μ.val k * A k ℓ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hcol, hrow, h ℓ]
  ring

/-- The strategy `σ(hₙ) = μ(S̄ₙ⁺)` from [MFoGT, Proposition 7.3.7]: at each
stage it selects an invariant measure of the positive part of the accumulated
internal-regret matrix.

The invariant measure is chosen noncomputably. The process theorem in this
module uses the conditional-law predicate, while `NoRegret.Process` constructs
a measurable realization on each finite discrete history space. -/
noncomputable def internalRegretMatchingStrategy
    (K : Type uK) [Fintype K] [Nonempty K] [DecidableEq K] : ExternalOnlineStrategy K :=
  fun n hist =>
    (@EconCSLib.StrategicGame.MatrixGame.exists_invariant_measure_nonneg K _ _ _
      (fun j ℓ => posPart (∑ t : Fin n, internalRegretStage (hist.1 t) (hist.2 t) j ℓ))
      (fun _ _ => posPart_nonneg _)).choose

/-- The defining invariance property of `internalRegretMatchingStrategy`'s output. -/
lemma internalRegretMatchingStrategy_isInvariantMeasureFor
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (n : ℕ) (hist : (Fin n → K) × (Fin n → K → ℝ)) :
    IsInvariantMeasureFor
      (fun j ℓ => posPart (∑ t : Fin n, internalRegretStage (hist.1 t) (hist.2 t) j ℓ))
      (internalRegretMatchingStrategy K n hist) :=
  (@EconCSLib.StrategicGame.MatrixGame.exists_invariant_measure_nonneg K _ _ _
    (fun j ℓ => posPart (∑ t : Fin n, internalRegretStage (hist.1 t) (hist.2 t) j ℓ))
    (fun _ _ => posPart_nonneg _)).choose_spec

/-- The strategy's raw per-history invariance transfers to the running average internal-regret
matrix, up to the positive-scale invariance of `IsInvariantMeasureFor`. -/
lemma internalRegretMatchingStrategy_isInvariantMeasureFor_average
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) :
    IsInvariantMeasureFor (fun j ℓ => posPart (averageInternalRegret play payoff n j ℓ))
      (internalRegretMatchingStrategy K (n + 1)
        (fun t : Fin (n + 1) => play t.val, fun t : Fin (n + 1) => payoff t.val)) := by
  have hspec := internalRegretMatchingStrategy_isInvariantMeasureFor (n + 1)
    (fun t : Fin (n + 1) => play t.val, fun t : Fin (n + 1) => payoff t.val)
  have hscaled := isInvariantMeasureFor_smul ((n : ℝ) + 1)⁻¹ hspec
  have heq : (fun j ℓ => ((n : ℝ) + 1)⁻¹ *
        posPart (∑ t : Fin (n + 1), internalRegretStage (play t.val) (payoff t.val) j ℓ))
      = (fun j ℓ => posPart (averageInternalRegret play payoff n j ℓ)) := by
    funext j ℓ
    unfold averageInternalRegret
    rw [posPart_pos_smul (show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ from by positivity)]
  rw [heq] at hscaled
  exact hscaled

namespace NoRegretProbability

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω]

/-! ### Almost-sure internal-regret interfaces -/

/-- No internal regret almost surely. -/
def HasNoInternalRegretAE {K : Type uK} [DecidableEq K]
    (P : MeasureTheory.Measure Ω)
    (play : ℕ → Ω → K) (payoff : ℕ → Ω → K → ℝ) : Prop :=
  ∀ᵐ ω ∂P,
    HasNoInternalRegret (fun n => play n ω) (fun n => payoff n ω)

/-- A strategy has robust no internal regret if every bounded predictable
process with the prescribed conditional action law has no internal regret
almost surely. This predicate does not assert existence of such a process. -/
def HasNoInternalRegretOnGeneratedProcessesAE
    {K : Type uK} [Fintype K] [DecidableEq K]
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (σ : ExternalOnlineStrategy K) : Prop :=
  ∀ play payoff,
    IsGeneratedByExternalStrategyAE P ℱ σ play payoff →
    IsBoundedPayoffProcessAE P payoff →
    HasNoInternalRegretAE P play payoff

/-! ### Generated-process no-internal-regret theorem: MFoGT Proposition 7.3.7 -/

/-- Conditional process form of [MFoGT, Proposition 7.3.7]. Every bounded
predictable process generated by the invariant-measure rule
`σ(hₙ) = μ(S̄ₙ⁺)` has no internal regret almost surely. -/
theorem internalRegretMatchingStrategy_hasNoInternalRegretOnGeneratedProcessesAE
    {K : Type uK} [Fintype K] [Nonempty K] [DecidableEq K]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ) :
    HasNoInternalRegretOnGeneratedProcessesAE P ℱ
      (internalRegretMatchingStrategy K) := by
  intro play payoff hgen hbdd
  set σ : ExternalOnlineStrategy K := internalRegretMatchingStrategy K with hσ_def
  set 𝒢 : MeasureTheory.Filtration ℕ mΩ :=
    { seq := fun n => ℱ (n + 1)
      mono' := fun n m hnm => ℱ.mono (by omega)
      le' := fun n => ℱ.le (n + 1) } with h𝒢_def
  set x : ℕ → Ω → (K × K) → ℝ := fun n ω jl =>
    internalRegretStage (play n ω) (payoff n ω) jl.1 jl.2 with hx_def
  set y : ℕ → Ω → (K × K) → ℝ := fun n ω jl =>
    ∑ k : K, externalStrategyProbability σ play payoff n k ω *
      internalRegretStage k (payoff n ω) jl.1 jl.2 with hy_def
  have hpayoff_pred : ∀ n : ℕ, ∀ k : K, Measurable[ℱ n] (fun ω => payoff n ω k) :=
    hgen.payoffPredictable
  have hpayoff_pred' : ∀ n : ℕ, ∀ k : K, Measurable[ℱ (n + 1)] (fun ω => payoff n ω k) :=
    fun n k => (hpayoff_pred n k).mono (ℱ.mono (Nat.le_succ n)) le_rfl
  have hind_meas' : ∀ n : ℕ, ∀ k : K, Measurable[ℱ (n + 1)] (actionIndicator play n k) :=
    fun n k => hgen.historyAdapted.playHistory (n + 1) ⟨n, Nat.lt_succ_self n⟩ k
  have hx_eq : ∀ n : ℕ, ∀ ω : Ω, ∀ j ℓ : K,
      x n ω (j, ℓ) = actionIndicator play n j ω * (payoff n ω ℓ - payoff n ω j) := by
    intro n ω j ℓ
    show internalRegretStage (play n ω) (payoff n ω) j ℓ = _
    unfold internalRegretStage actionIndicator
    split <;> ring
  have hadapted : MeasureTheory.Adapted 𝒢 x := by
    intro n
    show Measurable[ℱ (n + 1)] (fun ω (jl : K × K) => x n ω jl)
    letI : MeasurableSpace Ω := ℱ (n + 1)
    refine measurable_pi_lambda _ (fun jl => ?_)
    have heq : (fun ω => x n ω jl)
        = fun ω => actionIndicator play n jl.1 ω * (payoff n ω jl.2 - payoff n ω jl.1) :=
      funext fun ω => hx_eq n ω jl.1 jl.2
    rw [heq]
    exact (hind_meas' n jl.1).mul ((hpayoff_pred' n jl.2).sub (hpayoff_pred' n jl.1))
  have hbounded : IsUniformlyBoundedVectorProcessAE P x := by
    intro jl
    refine ⟨2, by norm_num, ?_⟩
    filter_upwards [hbdd] with ω hω n
    rw [hx_eq n ω jl.1 jl.2]
    have hind_le : |actionIndicator play n jl.1 ω| ≤ 1 := by
      unfold actionIndicator; split <;> norm_num
    have hdiff_le : |payoff n ω jl.2 - payoff n ω jl.1| ≤ 2 := by
      rw [abs_le]
      constructor <;> [linarith [(hω n jl.2).1, (hω n jl.1).2];
        linarith [(hω n jl.2).2, (hω n jl.1).1]]
    calc |actionIndicator play n jl.1 ω * (payoff n ω jl.2 - payoff n ω jl.1)|
        = |actionIndicator play n jl.1 ω| * |payoff n ω jl.2 - payoff n ω jl.1| := abs_mul _ _
      _ ≤ 1 * 2 := mul_le_mul hind_le hdiff_le (abs_nonneg _) (by norm_num)
      _ = 2 := by ring
  have hcondExp : IsConditionalExpectationSequence P 𝒢 x y := by
    constructor
    · intro n jl
      have hmeas : StronglyMeasurable[mΩ] (fun ω => x n ω jl) :=
        (((measurable_pi_apply jl).comp (hadapted n)).stronglyMeasurable).mono (𝒢.le n)
      have hbound : ∀ᵐ ω ∂P, |x n ω jl| ≤ 2 := by
        filter_upwards [hbdd] with ω hω
        rw [hx_eq n ω jl.1 jl.2]
        have hind_le : |actionIndicator play n jl.1 ω| ≤ 1 := by
          unfold actionIndicator; split <;> norm_num
        have hdiff_le : |payoff n ω jl.2 - payoff n ω jl.1| ≤ 2 := by
          rw [abs_le]
          constructor <;> [linarith [(hω n jl.2).1, (hω n jl.1).2];
            linarith [(hω n jl.2).2, (hω n jl.1).1]]
        calc |actionIndicator play n jl.1 ω * (payoff n ω jl.2 - payoff n ω jl.1)|
            = |actionIndicator play n jl.1 ω| * |payoff n ω jl.2 - payoff n ω jl.1| := abs_mul _ _
          _ ≤ 1 * 2 := mul_le_mul hind_le hdiff_le (abs_nonneg _) (by norm_num)
          _ = 2 := by ring
      exact integrable_of_stronglyMeasurable_abs_bound (le_refl mΩ) hmeas hbound
    · intro n jl
      show (fun ω => y (n + 1) ω jl)
          =ᵐ[P] MeasureTheory.condExp (ℱ (n + 1)) P (fun ω => x (n + 1) ω jl)
      obtain ⟨j, ℓ⟩ := jl
      have hf_meas : ∀ k : K, StronglyMeasurable[ℱ (n + 1)]
          (fun ω => internalRegretStage k (payoff (n + 1) ω) j ℓ) := by
        intro k
        unfold internalRegretStage
        split
        · exact ((hpayoff_pred (n + 1) ℓ).sub (hpayoff_pred (n + 1) j)).stronglyMeasurable
        · exact MeasureTheory.stronglyMeasurable_const
      have hf_bound : ∀ k : K,
          ∀ᵐ ω ∂P, |internalRegretStage k (payoff (n + 1) ω) j ℓ| ≤ 2 := by
        intro k
        filter_upwards [hbdd] with ω hω
        unfold internalRegretStage
        split
        · rw [abs_le]
          constructor <;> [linarith [(hω (n + 1) ℓ).1, (hω (n + 1) j).2];
            linarith [(hω (n + 1) ℓ).2, (hω (n + 1) j).1]]
        · simp
      have hpull := condExp_sum_mul_actionIndicator hgen n
        (fun k ω => internalRegretStage k (payoff (n + 1) ω) j ℓ) 2 hf_meas hf_bound
      have hxeq2 : (fun ω => x (n + 1) ω (j, ℓ))
          = fun ω => ∑ k : K,
            internalRegretStage k (payoff (n + 1) ω) j ℓ * actionIndicator play (n + 1) k ω := by
        funext ω
        show internalRegretStage (play (n + 1) ω) (payoff (n + 1) ω) j ℓ = _
        exact (sum_mul_actionIndicator_eq_apply play (n + 1)
          (fun k ω => internalRegretStage k (payoff (n + 1) ω) j ℓ) ω).symm
      have hy_eq2 : (fun ω => y (n + 1) ω (j, ℓ))
          = fun ω => ∑ k : K, internalRegretStage k (payoff (n + 1) ω) j ℓ *
              externalStrategyProbability σ play payoff (n + 1) k ω := by
        funext ω
        show (∑ k : K, externalStrategyProbability σ play payoff (n + 1) k ω *
            internalRegretStage k (payoff (n + 1) ω) j ℓ) = _
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hxeq2, hy_eq2]
      exact hpull.symm
  have hblackwell : BlackwellNegativeOrthantConditionAE P x y := by
    filter_upwards with ω
    intro n
    set r : K × K → ℝ := averageVector (fun m => x m ω) n with hr_def
    show ∑ jl : K × K, vectorPosPart r jl * (y (n + 1) ω jl - negativeOrthantProjection r jl) ≤ 0
    have hr_eq : ∀ j ℓ : K, r (j, ℓ)
        = averageInternalRegret (fun m => play m ω) (fun m => payoff m ω) n j ℓ := fun j ℓ => rfl
    set A : K → K → ℝ := fun j ℓ =>
      posPart (averageInternalRegret (fun m => play m ω) (fun m => payoff m ω) n j ℓ) with hA_def
    have hVA : ∀ j ℓ : K, vectorPosPart r (j, ℓ) = A j ℓ := fun j ℓ => by
      show posPart (r (j, ℓ)) = A j ℓ
      rw [hr_eq j ℓ]
    set μ : stdSimplex ℝ K :=
      σ (n + 1) (externalHistoryOf (fun t => play t ω) (fun t => payoff t ω) (n + 1)) with hμ_def
    have hInv : IsInvariantMeasureFor A μ := by
      rw [hμ_def]
      exact internalRegretMatchingStrategy_isInvariantMeasureFor_average
        (fun m => play m ω) (fun m => payoff m ω) n
    have hApos : ∀ j ℓ : K, 0 ≤ A j ℓ := fun j ℓ => posPart_nonneg _
    have hyeq' : ∀ j ℓ : K, y (n + 1) ω (j, ℓ)
        = expectedInternalRegret μ (payoff (n + 1) ω) j ℓ := by
      intro j ℓ
      show (∑ k : K, externalStrategyProbability σ play payoff (n + 1) k ω *
          internalRegretStage k (payoff (n + 1) ω) j ℓ) = _
      unfold expectedInternalRegret externalStrategyProbability
      rw [hμ_def]
    have horth := invariantMeasure_internalRegret_orthogonal A μ (payoff (n + 1) ω) hInv
    have hkey : ∑ jl : K × K, vectorPosPart r jl * y (n + 1) ω jl = 0 := by
      calc ∑ jl : K × K, vectorPosPart r jl * y (n + 1) ω jl
          = ∑ j : K, ∑ ℓ : K, vectorPosPart r (j, ℓ) * y (n + 1) ω (j, ℓ) :=
            Fintype.sum_prod_type _
        _ = ∑ j : K, ∑ ℓ : K, A j ℓ * expectedInternalRegret μ (payoff (n + 1) ω) j ℓ :=
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ℓ _ => by
              rw [hVA j ℓ, hyeq' j ℓ]
        _ = matrixInner A (expectedInternalRegret μ (payoff (n + 1) ω)) := rfl
        _ = 0 := horth
    have hkey2 : ∑ jl : K × K, vectorPosPart r jl * negativeOrthantProjection r jl = 0 :=
      Finset.sum_eq_zero fun jl _ => vectorPosPart_mul_negativeOrthantProjection_eq_zero r jl
    have hsplit : ∑ jl : K × K, vectorPosPart r jl * (y (n + 1) ω jl - negativeOrthantProjection r jl)
        = ∑ jl : K × K, vectorPosPart r jl * y (n + 1) ω jl
          - ∑ jl : K × K, vectorPosPart r jl * negativeOrthantProjection r jl := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun jl _ => by ring
    rw [hsplit, hkey, hkey2]
    norm_num
  have happroach := blackwell_approach_negativeOrthant_ae P 𝒢 x y hadapted hbounded hcondExp
    hblackwell
  filter_upwards [happroach] with ω hω
  intro j ℓ
  have heq : (fun n => posPart (averageVector (fun m => x m ω) n (j, ℓ)))
      = fun n => posPart (averageInternalRegret (fun m => play m ω) (fun m => payoff m ω) n j ℓ) := by
    funext n
    exact congrArg posPart rfl
  have hxjl := hω (j, ℓ)
  rwa [heq] at hxjl

end NoRegretProbability

end StrategicGame
