/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Adapted

/-!
# Blackwell approachability for closed convex targets

This module proves the finite-dimensional real-Hilbert-space form of Blackwell's
almost-sure projection criterion. It supplies a reusable metric-projection API
for nonempty closed convex targets and the stochastic convergence theorem used
in MFoGT Theorem 7.3.2.

## Main declarations

* `ClosedConvexTarget` - a bundled nonempty closed convex set.
* `ClosedConvexTarget.projection` - its metric projection.
* `ClosedConvexTarget.projection_lipschitz` - nonexpansiveness of projection.
* `hilbertAverage` - finite running averages indexed from zero.
* `Blackwell.blackwell_approach_closedConvex_ae` - the almost-sure criterion.
* `Blackwell.blackwell_projectionDistance_tendsto_zero_ae` - its
  distance-to-target formulation.

## References

* [MFoGT, Theorem 7.3.2]
* Blackwell, "An Analog of the Minimax Theorem for Vector Payoffs" (1956)
-/

open Finset BigOperators Filter Topology
open scoped MeasureTheory

namespace EconCSLib

universe uE

/-- A sequence approaches a set in metric distance. -/
def ApproachesSet {α : Type*} [PseudoMetricSpace α] (seq : ℕ → α) (C : Set α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∃ c ∈ C, dist (seq n) c ≤ ε

/-- A random sequence approaches a set almost surely. -/
def ApproachesSetAE {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : MeasureTheory.Measure Ω) (seq : ℕ → Ω → α) (C : Set α) : Prop :=
  ∀ᵐ ω ∂P, ApproachesSet (fun n => seq n ω) C

/-- A nonempty closed convex target in a real Hilbert space. -/
structure ClosedConvexTarget (E : Type uE) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  isClosed : IsClosed carrier
  convex : Convex ℝ carrier

namespace ClosedConvexTarget

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

instance : SetLike (ClosedConvexTarget E) E where
  coe D := D.carrier
  coe_injective' D D' h := by cases D; cases D'; cases h; rfl

/-- The metric projection onto a nonempty closed convex target. -/
noncomputable def projection (D : ClosedConvexTarget E) (x : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex D.nonempty D.isClosed.isComplete D.convex x)

theorem projection_mem (D : ClosedConvexTarget E) (x : E) : D.projection x ∈ D :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex D.nonempty D.isClosed.isComplete D.convex x)).1

theorem norm_sub_projection_eq_iInf (D : ClosedConvexTarget E) (x : E) :
    ‖x - D.projection x‖ = ⨅ d : D.carrier, ‖x - (d : E)‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex D.nonempty D.isClosed.isComplete D.convex x)).2

theorem projection_inner_le_zero (D : ClosedConvexTarget E) (x : E)
    {d : E} (hd : d ∈ D) :
    inner ℝ (x - D.projection x) (d - D.projection x) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero D.convex (D.projection_mem x)).mp
    (D.norm_sub_projection_eq_iInf x) d hd

theorem projection_minimizes (D : ClosedConvexTarget E) (x : E)
    {d : E} (hd : d ∈ D) :
    ‖x - D.projection x‖ ≤ ‖x - d‖ := by
  rw [D.norm_sub_projection_eq_iInf x]
  have hbdd : BddBelow (Set.range (fun y : D.carrier ↦ ‖x - (y : E)‖)) := by
    refine ⟨0, ?_⟩
    rintro z ⟨y, rfl⟩
    exact norm_nonneg _
  exact ciInf_le hbdd ⟨d, hd⟩

theorem norm_projection_sub_projection_le (D : ClosedConvexTarget E) (x y : E) :
    ‖D.projection x - D.projection y‖ ≤ ‖x - y‖ := by
  set p := D.projection x
  set q := D.projection y
  have hpq : inner ℝ (x - p) (q - p) ≤ 0 :=
    D.projection_inner_le_zero x (D.projection_mem y)
  have hqp : inner ℝ (y - q) (p - q) ≤ 0 :=
    D.projection_inner_le_zero y (D.projection_mem x)
  have hmono : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      inner ℝ (p - q) (p - q)
          ≤ inner ℝ (x - p) (p - q) + inner ℝ (p - q) (p - q)
              + inner ℝ (q - y) (p - q) := by
            have h1 : 0 ≤ inner ℝ (x - p) (p - q) := by
              rw [show p - q = -(q - p) by abel, inner_neg_right]
              linarith
            have h2 : 0 ≤ inner ℝ (q - y) (p - q) := by
              rw [show q - y = -(y - q) by abel, inner_neg_left]
              linarith
            linarith
      _ = inner ℝ (x - y) (p - q) := by
        rw [← inner_add_left, ← inner_add_left]
        congr 2
        abel
  by_cases hpq0 : p - q = 0
  · simp [hpq0]
  · have hnormpos : 0 < ‖p - q‖ := norm_pos_iff.mpr hpq0
    have hcauchy : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ :=
      real_inner_le_norm _ _
    have hmul : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
      rw [← pow_two]
      exact hmono.trans hcauchy
    exact le_of_mul_le_mul_right hmul hnormpos

theorem projection_lipschitz (D : ClosedConvexTarget E) : LipschitzWith 1 D.projection := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact D.norm_projection_sub_projection_le x y

theorem continuous_projection (D : ClosedConvexTarget E) : Continuous D.projection :=
  D.projection_lipschitz.continuous

end ClosedConvexTarget

/-! ## Hilbert-space Blackwell approachability -/

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The empirical average through stage `n`, indexed from stage zero. -/
noncomputable def hilbertAverage (x : ℕ → E) (n : ℕ) : E :=
  ((n + 1 : ℝ)⁻¹) • ∑ t ∈ Finset.range (n + 1), x t

lemma hilbertAverage_succ (x : ℕ → E) (n : ℕ) :
    hilbertAverage x (n + 1) =
      ((n + 1 : ℝ) / (n + 2)) • hilbertAverage x n +
        (1 / (n + 2 : ℝ)) • x (n + 1) := by
  unfold hilbertAverage
  rw [Finset.sum_range_succ]
  push_cast
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  rw [smul_add, smul_smul]
  congr 1
  · congr 1
    field_simp
    ring
  · congr 1
    ring

lemma norm_hilbertAverage_le (x : ℕ → E) {B : ℝ}
    (hbound : ∀ n, ‖x n‖ ≤ B) (n : ℕ) :
    ‖hilbertAverage x n‖ ≤ B := by
  unfold hilbertAverage
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((n + 1 : ℝ)⁻¹) by positivity)]
  calc
    ((n + 1 : ℝ)⁻¹) * ‖∑ t ∈ Finset.range (n + 1), x t‖
        ≤ ((n + 1 : ℝ)⁻¹) * ∑ t ∈ Finset.range (n + 1), ‖x t‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n + 1 : ℝ)⁻¹) * ∑ _t ∈ Finset.range (n + 1), B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ ↦ hbound t) (by positivity)
    _ = B := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp

lemma hilbertAverage_sum_split (x : ℕ → E) {m n : ℕ} (hmn : m ≤ n) :
    (n + 1 : ℝ) • hilbertAverage x n =
      (m + 1 : ℝ) • hilbertAverage x m +
        ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t := by
  unfold hilbertAverage
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hn1, mul_inv_cancel₀ hm1, one_smul,
    one_smul]
  exact (Finset.sum_range_add_sum_Ico x (Nat.add_le_add_right hmn 1)).symm

lemma norm_hilbertAverage_sub_le (x : ℕ → E) {B : ℝ}
    (hbound : ∀ n, ‖x n‖ ≤ B) {m n : ℕ} (hmn : m ≤ n) :
    ‖hilbertAverage x n - hilbertAverage x m‖ ≤
      2 * B * ((n : ℝ) - m) / (n + 1) := by
  have havgm := norm_hilbertAverage_le x hbound m
  have hsplit := hilbertAverage_sum_split x hmn
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have htail_eq : (∑ t ∈ Finset.Ico (m + 1) (n + 1), x t) =
      (n + 1 : ℝ) • hilbertAverage x n - (m + 1 : ℝ) • hilbertAverage x m := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hsplit.symm
  have heq : hilbertAverage x n - hilbertAverage x m =
      -(((n : ℝ) - m) / (n + 1)) • hilbertAverage x m +
        ((n + 1 : ℝ)⁻¹) • ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t := by
    rw [htail_eq, smul_sub, smul_smul, smul_smul]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    simp only [inv_mul_cancel₀ hn1, one_smul]
    have hcoef : -(((n : ℝ) - m) / (n + 1)) -
        (n + 1 : ℝ)⁻¹ * (m + 1) = -1 := by
      field_simp
      ring
    symm
    calc
      -(((n : ℝ) - m) / (n + 1)) • hilbertAverage x m +
            (hilbertAverage x n - ((n + 1 : ℝ)⁻¹ * (m + 1)) • hilbertAverage x m) =
          hilbertAverage x n +
            (-(((n : ℝ) - m) / (n + 1)) - (n + 1 : ℝ)⁻¹ * (m + 1)) •
              hilbertAverage x m := by module
      _ = hilbertAverage x n + (-1 : ℝ) • hilbertAverage x m := by rw [hcoef]
      _ = hilbertAverage x n - hilbertAverage x m := by module
  rw [heq]
  calc
    ‖-(((n : ℝ) - m) / (n + 1)) • hilbertAverage x m +
          ((n + 1 : ℝ)⁻¹) • ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t‖
        ≤ ‖-(((n : ℝ) - m) / (n + 1)) • hilbertAverage x m‖ +
            ‖((n + 1 : ℝ)⁻¹) • ∑ t ∈ Finset.Ico (m + 1) (n + 1), x t‖ :=
      norm_add_le _ _
    _ ≤ (((n : ℝ) - m) / (n + 1)) * B +
          ((n + 1 : ℝ)⁻¹) *
            ((n - m : ℕ) : ℝ) * B := by
      have hnm0 : 0 ≤ (n : ℝ) - m := sub_nonneg.mpr (by exact_mod_cast hmn)
      have htail : ‖∑ t ∈ Finset.Ico (m + 1) (n + 1), x t‖ ≤
          ((n - m : ℕ) : ℝ) * B := by
        calc
          ‖∑ t ∈ Finset.Ico (m + 1) (n + 1), x t‖
              ≤ ∑ t ∈ Finset.Ico (m + 1) (n + 1), ‖x t‖ := norm_sum_le _ _
          _ ≤ ∑ _t ∈ Finset.Ico (m + 1) (n + 1), B :=
            Finset.sum_le_sum fun t _ ↦ hbound t
          _ = ((n - m : ℕ) : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
            have hcard : (n + 1) - (m + 1) = n - m := by omega
            rw [hcard]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : ℝ)⁻¹)),
        abs_neg, abs_of_nonneg (div_nonneg hnm0 hn1pos.le)]
      exact add_le_add (mul_le_mul_of_nonneg_left havgm (div_nonneg hnm0 hn1pos.le))
        (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ ((n + 1 : ℝ)⁻¹)))
    _ = 2 * B * ((n : ℝ) - m) / (n + 1) := by
      rw [Nat.cast_sub hmn]
      field_simp
      ring

/-- Squared distance to a closed convex target, realized by its metric projection. -/
noncomputable def closedConvexPotential [CompleteSpace E]
    (D : ClosedConvexTarget E) (z : E) : ℝ :=
  ‖z - D.projection z‖ ^ 2

lemma closedConvexPotential_nonneg [CompleteSpace E]
    (D : ClosedConvexTarget E) (z : E) :
    0 ≤ closedConvexPotential D z := sq_nonneg _

/-- The deterministic one-step recursion behind Blackwell's approachability theorem. -/
lemma closedConvexPotential_hilbertAverage_succ_le [CompleteSpace E]
    (D : ClosedConvexTarget E) (x : ℕ → E) (n : ℕ) :
    closedConvexPotential D (hilbertAverage x (n + 1)) ≤
      ((n + 1 : ℝ) / (n + 2)) ^ 2 *
          closedConvexPotential D (hilbertAverage x n) +
        2 * ((n + 1 : ℝ) / (n + 2)) * (1 / (n + 2 : ℝ)) *
          inner ℝ
            (hilbertAverage x n - D.projection (hilbertAverage x n))
            (x (n + 1) - D.projection (hilbertAverage x n)) +
        (1 / (n + 2 : ℝ)) ^ 2 *
          ‖x (n + 1) - D.projection (hilbertAverage x n)‖ ^ 2 := by
  set a : ℝ := (n + 1 : ℝ) / (n + 2)
  set b : ℝ := 1 / (n + 2 : ℝ)
  set z : E := hilbertAverage x n
  set p : E := D.projection z
  have hab : a + b = 1 := by
    dsimp only [a, b]
    field_simp
    ring
  have havg : hilbertAverage x (n + 1) = a • z + b • x (n + 1) := by
    simpa only [a, b, z] using hilbertAverage_succ x n
  have hrewrite : hilbertAverage x (n + 1) - p =
      a • (z - p) + b • (x (n + 1) - p) := by
    calc
      hilbertAverage x (n + 1) - p = a • z + b • x (n + 1) - p := by rw [havg]
      _ = a • z + b • x (n + 1) - (a + b) • p := by rw [hab, one_smul]
      _ = a • (z - p) + b • (x (n + 1) - p) := by module
  have hmin := D.projection_minimizes (hilbertAverage x (n + 1)) (D.projection_mem z)
  have hsq : closedConvexPotential D (hilbertAverage x (n + 1)) ≤
      ‖hilbertAverage x (n + 1) - p‖ ^ 2 := by
    unfold closedConvexPotential
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
  rw [hrewrite, norm_add_sq_real] at hsq
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hnorma : ‖a • (z - p)‖ ^ 2 = a ^ 2 * ‖z - p‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, mul_pow]
  have hnormb : ‖b • (x (n + 1) - p)‖ ^ 2 =
      b ^ 2 * ‖x (n + 1) - p‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, mul_pow]
  have hinner : inner ℝ (a • (z - p)) (b • (x (n + 1) - p)) =
      a * b * inner ℝ (z - p) (x (n + 1) - p) := by
    simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    ring
  rw [hnorma, hnormb, hinner] at hsq
  have hsq' : closedConvexPotential D (hilbertAverage x (n + 1)) ≤
      a ^ 2 * ‖z - p‖ ^ 2 + 2 * a * b * inner ℝ (z - p) (x (n + 1) - p) +
        b ^ 2 * ‖x (n + 1) - p‖ ^ 2 := by
    nlinarith [hsq]
  simpa only [a, b, z, p, closedConvexPotential] using hsq'

namespace Blackwell

universe uΩ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type uΩ} [mΩ : MeasurableSpace Ω]

omit [MeasurableSpace E] [BorelSpace E] in
noncomputable local instance finiteDimensionalCompleteSpace : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

/-- The real inner product as a continuous bilinear map. -/
noncomputable def realInnerBilin : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ E) 1 fun x y ↦ by
    simpa only [one_mul] using norm_inner_le_norm x y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma realInnerBilin_apply (x y : E) : realInnerBilin x y = inner ℝ x y := rfl

/-- A Hilbert-valued process is uniformly bounded almost surely. -/
def IsUniformlyBoundedHilbertProcessAE
    (P : MeasureTheory.Measure Ω) (x : ℕ → Ω → E) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂P, ∀ n : ℕ, ‖x n ω‖ ≤ B

/-- Vector-valued conditional expectations for the next stage. -/
structure IsHilbertConditionalExpectationSequence
    (P : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (x y : ℕ → Ω → E) : Prop where
  integrable : ∀ n : ℕ, MeasureTheory.Integrable (x n) P
  condExp : ∀ n : ℕ,
    y (n + 1) =ᵐ[P] MeasureTheory.condExp (ℱ n) P (x (n + 1))

/-- The one-step Blackwell projection inequality for a closed convex target. -/
noncomputable def BlackwellClosedConvexConditionAE
    (D : ClosedConvexTarget E) (P : MeasureTheory.Measure Ω)
    (x y : ℕ → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ n : ℕ,
    inner ℝ
      (hilbertAverage (fun t ↦ x t ω) n -
        D.projection (hilbertAverage (fun t ↦ x t ω) n))
      (y (n + 1) ω - D.projection (hilbertAverage (fun t ↦ x t ω) n)) ≤ 0

/-- Each running Hilbert-space average is measurable at the corresponding stage. -/
lemma measurable_hilbertAverage
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x) (n : ℕ) :
    Measurable[ℱ n] (fun ω ↦ hilbertAverage (fun t ↦ x t ω) n) := by
  unfold hilbertAverage
  refine Measurable.const_smul (Finset.measurable_sum (Finset.range (n + 1)) ?_) _
  intro t ht
  exact hadapted.measurable_le (Nat.le_of_lt_succ (Finset.mem_range.mp ht))

/-- The projection of the running average is measurable at the same stage. -/
lemma measurable_projection_hilbertAverage
    (D : ClosedConvexTarget E) {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {x : ℕ → Ω → E} (hadapted : MeasureTheory.Adapted ℱ x) (n : ℕ) :
    Measurable[ℱ n]
      (fun ω ↦ D.projection (hilbertAverage (fun t ↦ x t ω) n)) :=
  D.continuous_projection.measurable.comp (measurable_hilbertAverage hadapted n)

/-- The squared-distance potential of the running average is measurable. -/
lemma measurable_closedConvexPotential_hilbertAverage
    (D : ClosedConvexTarget E) {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {x : ℕ → Ω → E} (hadapted : MeasureTheory.Adapted ℱ x) (n : ℕ) :
    Measurable[ℱ n]
      (fun ω ↦ closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n)) := by
  unfold closedConvexPotential
  have havg := measurable_hilbertAverage hadapted n
  have hproj := measurable_projection_hilbertAverage D hadapted n
  letI : MeasurableSpace Ω := ℱ n
  exact (havg.sub hproj).norm.pow_const 2

omit [MeasurableSpace E] [BorelSpace E] in
/-- A projection of a bounded running average is bounded relative to any fixed target point. -/
lemma norm_projection_hilbertAverage_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    (x : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖x n‖ ≤ B) (n : ℕ) :
    ‖D.projection (hilbertAverage x n)‖ ≤ 2 * B + ‖d₀‖ := by
  set z := hilbertAverage x n
  set p := D.projection z
  have hz : ‖z‖ ≤ B := norm_hilbertAverage_le x hbound n
  have hdist : ‖z - p‖ ≤ ‖z - d₀‖ := D.projection_minimizes z hd₀
  have hp : ‖p‖ ≤ ‖z‖ + ‖z - p‖ := by
    calc
      ‖p‖ = ‖z - (z - p)‖ := by congr 1; abel
      _ ≤ ‖z‖ + ‖z - p‖ := norm_sub_le _ _
  have hzd : ‖z - d₀‖ ≤ ‖z‖ + ‖d₀‖ := norm_sub_le _ _
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- The fresh sample minus the previous projection has a uniform bound. -/
lemma norm_sub_projection_hilbertAverage_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    (x : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖x n‖ ≤ B)
    (n t : ℕ) :
    ‖x t - D.projection (hilbertAverage x n)‖ ≤ 3 * B + ‖d₀‖ := by
  have hp := norm_projection_hilbertAverage_le D hd₀ x hbound n
  have hx := hbound t
  exact (norm_sub_le _ _).trans (by linarith)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The squared target-distance potential of a bounded average is uniformly bounded. -/
lemma closedConvexPotential_hilbertAverage_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    (x : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖x n‖ ≤ B)
    (n : ℕ) :
    closedConvexPotential D (hilbertAverage x n) ≤ (B + ‖d₀‖) ^ 2 := by
  have hz := norm_hilbertAverage_le x hbound n
  have hmin := D.projection_minimizes (hilbertAverage x n) hd₀
  have htri : ‖hilbertAverage x n - d₀‖ ≤ B + ‖d₀‖ :=
    (norm_sub_le _ _).trans (add_le_add hz le_rfl)
  unfold closedConvexPotential
  exact (pow_le_pow_left₀ (norm_nonneg _) (hmin.trans htri) 2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- Strong measurability plus an almost-sure norm bound gives integrability on a probability
space. -/
lemma integrable_of_stronglyMeasurable_norm_bound
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} {f : Ω → E} (hm : m ≤ mΩ)
    (hf : StronglyMeasurable[m] f) {C : ℝ} (hC : ∀ᵐ ω ∂P, ‖f ω‖ ≤ C) :
    MeasureTheory.Integrable f P :=
  MeasureTheory.Integrable.of_bound (hf.mono hm).aestronglyMeasurable C hC

/-- Running averages are integrable under a uniform process bound. -/
lemma integrable_hilbertAverage
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    MeasureTheory.Integrable (fun ω ↦ hilbertAverage (fun t ↦ x t ω) n) P := by
  apply integrable_of_stronglyMeasurable_norm_bound (ℱ.le n)
    (measurable_hilbertAverage hadapted n).stronglyMeasurable
  filter_upwards [hB] with ω hω
  exact norm_hilbertAverage_le (fun t ↦ x t ω) hω n

/-- Projections of running averages are integrable under a uniform process bound. -/
lemma integrable_projection_hilbertAverage
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω ↦ D.projection (hilbertAverage (fun t ↦ x t ω) n)) P := by
  apply integrable_of_stronglyMeasurable_norm_bound (ℱ.le n)
    (measurable_projection_hilbertAverage D hadapted n).stronglyMeasurable
  filter_upwards [hB] with ω hω
  exact norm_projection_hilbertAverage_le D hd₀ (fun t ↦ x t ω) hω n

/-- Squared-distance potentials of running averages are integrable. -/
lemma integrable_closedConvexPotential_hilbertAverage
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω ↦ closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n)) P := by
  apply MeasureTheory.Integrable.of_bound
    ((measurable_closedConvexPotential_hilbertAverage D hadapted n).mono (ℱ.le n) le_rfl
      |>.stronglyMeasurable.aestronglyMeasurable)
    ((B + ‖d₀‖) ^ 2)
  filter_upwards [hB] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (closedConvexPotential_nonneg D _)]
  exact closedConvexPotential_hilbertAverage_le D hd₀ (fun t ↦ x t ω) hω n

/-- Conditional expectation commutes with subtracting the predictable projection of the
current running average. -/
lemma condExp_sub_projection_hilbertAverage
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    {B : ℝ} (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    MeasureTheory.condExp (ℱ n) P
        (fun ω ↦ x (n + 1) ω - D.projection (hilbertAverage (fun t ↦ x t ω) n))
      =ᵐ[P]
        fun ω ↦ y (n + 1) ω - D.projection (hilbertAverage (fun t ↦ x t ω) n) := by
  let p : Ω → E := fun ω ↦ D.projection (hilbertAverage (fun t ↦ x t ω) n)
  change MeasureTheory.condExp (ℱ n) P (x (n + 1) - p) =ᵐ[P] y (n + 1) - p
  have hpint := integrable_projection_hilbertAverage D hd₀ hadapted hB n
  have hpsm : StronglyMeasurable[ℱ n] p :=
    (measurable_projection_hilbertAverage D hadapted n).stronglyMeasurable
  have hpcond : MeasureTheory.condExp (ℱ n) P p =ᵐ[P] p :=
    MeasureTheory.condExp_of_aestronglyMeasurable' (ℱ.le n)
      hpsm.aestronglyMeasurable hpint
  have hsub := MeasureTheory.condExp_sub (hcondExp.integrable (n + 1)) hpint (ℱ n)
  filter_upwards [hsub, (hcondExp.condExp n).symm, hpcond] with ω hωsub hωx hωp
  simp only [Pi.sub_apply] at hωsub ⊢
  calc
    MeasureTheory.condExp (ℱ n) P (x (n + 1) - p) ω =
        MeasureTheory.condExp (ℱ n) P (x (n + 1)) ω -
          MeasureTheory.condExp (ℱ n) P p ω := hωsub
    _ = y (n + 1) ω - p ω := by rw [hωx, hωp]

/-- One-step expectation recursion for the squared distance to a closed convex target. -/
lemma integral_closedConvexPotential_succ_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) (n + 1)) ∂P ≤
      ((n + 1 : ℝ) / (n + 2)) ^ 2 *
          ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P +
        (1 / (n + 2 : ℝ)) ^ 2 * (3 * B + ‖d₀‖) ^ 2 := by
  let avg : Ω → E := fun ω ↦ hilbertAverage (fun t ↦ x t ω) n
  let p : Ω → E := fun ω ↦ D.projection (avg ω)
  let r : Ω → E := fun ω ↦ avg ω - p ω
  let d : Ω → E := fun ω ↦ x (n + 1) ω - p ω
  let V : Ω → ℝ := fun ω ↦ closedConvexPotential D (avg ω)
  let a : ℝ := (n + 1 : ℝ) / (n + 2)
  let b : ℝ := 1 / (n + 2 : ℝ)
  let C : ℝ := 3 * B + ‖d₀‖
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have havgMeas : Measurable[ℱ n] avg := measurable_hilbertAverage hadapted n
  have hpMeas : Measurable[ℱ n] p := measurable_projection_hilbertAverage D hadapted n
  have hrSM : StronglyMeasurable[ℱ n] r := (havgMeas.sub hpMeas).stronglyMeasurable
  have hpInt := integrable_projection_hilbertAverage D hd₀ hadapted hB n
  have hdInt : MeasureTheory.Integrable d P := (hcondExp.integrable (n + 1)).sub hpInt
  have hrBound : ∀ᵐ ω ∂P, ‖r ω‖ ≤ B + ‖d₀‖ := by
    filter_upwards [hB] with ω hω
    have havgBound := norm_hilbertAverage_le (fun t ↦ x t ω) hω n
    have hmin := D.projection_minimizes (avg ω) hd₀
    exact hmin.trans ((norm_sub_le _ _).trans (add_le_add havgBound le_rfl))
  have hcrossInt : MeasureTheory.Integrable (fun ω ↦ realInnerBilin (r ω) (d ω)) P :=
    realInnerBilin.integrable_of_bilin_of_bdd_left (B + ‖d₀‖)
      ((hrSM.mono (ℱ.le n)).aestronglyMeasurable) hrBound hdInt
  have hcrossInt' : MeasureTheory.Integrable (fun ω ↦ inner ℝ (r ω) (d ω)) P := by
    simpa only [realInnerBilin_apply] using hcrossInt
  have hdiffCond := condExp_sub_projection_hilbertAverage D hd₀ hadapted hcondExp hB n
  have hpull := MeasureTheory.condExp_bilin_of_stronglyMeasurable_left
    (B := realInnerBilin) hrSM hcrossInt hdInt
  have hcrossCond : MeasureTheory.condExp (ℱ n) P
        (fun ω ↦ realInnerBilin (r ω) (d ω)) =ᵐ[P]
      fun ω ↦ inner ℝ (r ω) (y (n + 1) ω - p ω) := by
    filter_upwards [hpull, hdiffCond] with ω hωpull hωdiff
    rw [hωpull, hωdiff]
    rfl
  have hcondn : ∀ᵐ ω ∂P, inner ℝ (r ω) (y (n + 1) ω - p ω) ≤ 0 := by
    filter_upwards [hcond] with ω hω
    exact hω n
  have hcrossIntegral : ∫ ω, inner ℝ (r ω) (d ω) ∂P ≤ 0 := by
    calc
      ∫ ω, inner ℝ (r ω) (d ω) ∂P =
          ∫ ω, MeasureTheory.condExp (ℱ n) P
            (fun ω ↦ realInnerBilin (r ω) (d ω)) ω ∂P := by
              rw [MeasureTheory.integral_condExp (ℱ.le n)]
              rfl
      _ = ∫ ω, inner ℝ (r ω) (y (n + 1) ω - p ω) ∂P :=
        MeasureTheory.integral_congr_ae hcrossCond
      _ ≤ 0 := MeasureTheory.integral_nonpos_of_ae hcondn
  have hVInt := integrable_closedConvexPotential_hilbertAverage D hd₀ hadapted hB n
  have hVSuccInt := integrable_closedConvexPotential_hilbertAverage D hd₀ hadapted hB (n + 1)
  have hpoint : (λ ω ↦ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) (n + 1))) ≤ᵐ[P]
      fun ω ↦ a ^ 2 * V ω + 2 * a * b * inner ℝ (r ω) (d ω) + b ^ 2 * C ^ 2 := by
    filter_upwards [hB] with ω hω
    have hstep := closedConvexPotential_hilbertAverage_succ_le D (fun t ↦ x t ω) n
    have hdNorm := norm_sub_projection_hilbertAverage_le D hd₀ (fun t ↦ x t ω)
      hω n (n + 1)
    have hdSq : ‖d ω‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdNorm 2
    have hbSq : 0 ≤ b ^ 2 := sq_nonneg _
    dsimp only [a, b, C, V, r, d, avg, p] at hstep hdSq ⊢
    nlinarith [hstep, mul_le_mul_of_nonneg_left hdSq hbSq]
  have hRhsInt : MeasureTheory.Integrable
      (fun ω ↦ a ^ 2 * V ω + 2 * a * b * inner ℝ (r ω) (d ω) + b ^ 2 * C ^ 2) P :=
    ((hVInt.const_mul _).add (hcrossInt'.const_mul _)).add (MeasureTheory.integrable_const _)
  have hmono := MeasureTheory.integral_mono_ae hVSuccInt hRhsInt hpoint
  have hRhsIntegral :
      ∫ ω, a ^ 2 * V ω + 2 * a * b * inner ℝ (r ω) (d ω) + b ^ 2 * C ^ 2 ∂P =
        a ^ 2 * ∫ ω, V ω ∂P +
          2 * a * b * ∫ ω, inner ℝ (r ω) (d ω) ∂P + b ^ 2 * C ^ 2 := by
    calc
      ∫ ω, a ^ 2 * V ω + 2 * a * b * inner ℝ (r ω) (d ω) + b ^ 2 * C ^ 2 ∂P =
          (∫ ω, a ^ 2 * V ω + 2 * a * b * inner ℝ (r ω) (d ω) ∂P) +
            ∫ _ω, b ^ 2 * C ^ 2 ∂P :=
        MeasureTheory.integral_add ((hVInt.const_mul _).add (hcrossInt'.const_mul _))
          (MeasureTheory.integrable_const _)
      _ = ((∫ ω, a ^ 2 * V ω ∂P) +
            ∫ ω, 2 * a * b * inner ℝ (r ω) (d ω) ∂P) +
            ∫ _ω, b ^ 2 * C ^ 2 ∂P := by
        rw [MeasureTheory.integral_add (hVInt.const_mul _) (hcrossInt'.const_mul _)]
      _ = a ^ 2 * ∫ ω, V ω ∂P +
          2 * a * b * ∫ ω, inner ℝ (r ω) (d ω) ∂P + b ^ 2 * C ^ 2 := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const, MeasureTheory.measureReal_def,
          MeasureTheory.measure_univ, ENNReal.toReal_one, one_smul]
  rw [hRhsIntegral] at hmono
  dsimp only [a, b, C, V, r, d, avg, p] at hmono ⊢
  have hcoef₀ : 0 ≤ 2 * ((n + 1 : ℝ) / (n + 2)) * (1 / (n + 2 : ℝ)) := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef₀ hcrossIntegral]

lemma sq_mul_integral_closedConvexPotential_succ_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    (n + 2 : ℝ) ^ 2 *
        ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) (n + 1)) ∂P ≤
      (n + 1 : ℝ) ^ 2 *
          ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P +
        (3 * B + ‖d₀‖) ^ 2 := by
  have hstep := integral_closedConvexPotential_succ_le D hd₀ hadapted hcondExp hcond hB₀ hB n
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstep (sq_nonneg (n + 2 : ℝ))
  calc
    (n + 2 : ℝ) ^ 2 *
        ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) (n + 1)) ∂P ≤
      (n + 2 : ℝ) ^ 2 *
        (((n + 1 : ℝ) / (n + 2)) ^ 2 *
            ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P +
          (1 / (n + 2 : ℝ)) ^ 2 * (3 * B + ‖d₀‖) ^ 2) := hmul
    _ = (n + 1 : ℝ) ^ 2 *
          ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P +
        (3 * B + ‖d₀‖) ^ 2 := by
      field_simp [hn2.ne']

lemma sq_mul_integral_closedConvexPotential_le
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    (n + 1 : ℝ) ^ 2 *
        ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P ≤
      (∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) 0) ∂P) +
        n * (3 * B + ‖d₀‖) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := sq_mul_integral_closedConvexPotential_succ_le
      D hd₀ hadapted hcondExp hcond hB₀ hB n
    push_cast
    push_cast at ih
    nlinarith [hstep, ih]

lemma integral_closedConvexPotential_le_const_div
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B) (n : ℕ) :
    ∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) n) ∂P ≤
      ((∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) 0) ∂P) +
        (3 * B + ‖d₀‖) ^ 2) / (n + 1) := by
  have hkey := sq_mul_integral_closedConvexPotential_le
    D hd₀ hadapted hcondExp hcond hB₀ hB n
  have hE₀ : 0 ≤ ∫ ω, closedConvexPotential D
      (hilbertAverage (fun t ↦ x t ω) 0) ∂P :=
    MeasureTheory.integral_nonneg fun ω ↦ closedConvexPotential_nonneg D _
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  rw [le_div_iff₀ hn1]
  nlinarith [hkey, sq_nonneg (n + 1 : ℝ), sq_nonneg (3 * B + ‖d₀‖),
    Nat.cast_nonneg (α := ℝ) n]

/-- Along perfect-square checkpoints, the squared distance to the target converges to zero
almost surely. -/
lemma ae_eventually_closedConvexPotential_checkpoint_lt
    (D : ClosedConvexTarget E) {d₀ : E} (hd₀ : d₀ ∈ D)
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {x y : ℕ → Ω → E}
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y)
    {B : ℝ} (hB₀ : 0 ≤ B) (hB : ∀ᵐ ω ∂P, ∀ n, ‖x n ω‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ l in Filter.atTop,
      closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2)) < ε := by
  set C : ℝ :=
    (∫ ω, closedConvexPotential D (hilbertAverage (fun t ↦ x t ω) 0) ∂P) +
      (3 * B + ‖d₀‖) ^ 2 with hC_def
  have hCnonneg : 0 ≤ C := by
    have hE₀ : 0 ≤ ∫ ω, closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) 0) ∂P :=
      MeasureTheory.integral_nonneg fun ω ↦ closedConvexPotential_nonneg D _
    rw [hC_def]
    positivity
  have hPle : ∀ l : ℕ,
      P.real {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))} ≤
        C / (ε * ((l : ℝ) + 1) ^ 2) := by
    intro l
    have hnonneg : 0 ≤ᵐ[P] fun ω ↦ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2)) :=
      Filter.Eventually.of_forall fun ω ↦ closedConvexPotential_nonneg D _
    have hint := integrable_closedConvexPotential_hilbertAverage
      D hd₀ hadapted hB ((l + 1) ^ 2)
    have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint ε
    have hdecay := integral_closedConvexPotential_le_const_div
      D hd₀ hadapted hcondExp hcond hB₀ hB ((l + 1) ^ 2)
    have hcombine : ε * P.real {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))} ≤
        C / (((l : ℝ) + 1) ^ 2 + 1) := by
      refine hmarkov.trans ?_
      rw [hC_def]
      convert hdecay using 3
      push_cast
      ring
    have hstep : C / (((l : ℝ) + 1) ^ 2 + 1) ≤ C / ((l : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left hCnonneg (by positivity) (by linarith)
    have hle : ε * P.real {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))} ≤
        C / ((l : ℝ) + 1) ^ 2 := hcombine.trans hstep
    rw [div_mul_eq_div_div_swap, le_div_iff₀ hε]
    linarith
  have hEle : ∀ l : ℕ,
      P {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))} ≤
        ENNReal.ofReal (C / (ε * ((l : ℝ) + 1) ^ 2)) := by
    intro l
    have hne : P {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))} ≠ ⊤ :=
      MeasureTheory.measure_ne_top P _
    rw [← ENNReal.ofReal_toReal hne, ← MeasureTheory.measureReal_def]
    exact ENNReal.ofReal_le_ofReal (hPle l)
  have hsum₂ : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hsumshift : Summable (fun l : ℕ ↦ (((l : ℝ) + 1) ^ 2)⁻¹) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) 1).mpr hsum₂
    simpa using h
  have hsumfin : Summable (fun l : ℕ ↦ C / (ε * ((l : ℝ) + 1) ^ 2)) := by
    have h := hsumshift.mul_left (C / ε)
    convert h using 1
    ext l
    field_simp
  have hne_top : (∑' l : ℕ, P {ω | ε ≤ closedConvexPotential D
      (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))}) ≠ ⊤ := by
    have hle_sum : (∑' l : ℕ, P {ω | ε ≤ closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2))}) ≤
        ∑' l : ℕ, ENNReal.ofReal (C / (ε * ((l : ℝ) + 1) ^ 2)) :=
      ENNReal.tsum_le_tsum hEle
    refine ne_top_of_le_ne_top ?_ hle_sum
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l ↦ by positivity) hsumfin]
    exact ENNReal.ofReal_ne_top
  have hbc := MeasureTheory.ae_eventually_notMem hne_top
  filter_upwards [hbc] with ω hω
  filter_upwards [hω] with l hl
  exact not_le.mp hl

/-- **MFoGT Theorem 7.3.2.** If a uniformly bounded adapted process satisfies
the Blackwell projection inequality for a nonempty closed convex target, then
its empirical averages approach that target almost surely. -/
theorem blackwell_approach_closedConvex_ae
    (D : ClosedConvexTarget E)
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (x y : ℕ → Ω → E)
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hbounded : IsUniformlyBoundedHilbertProcessAE P x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y) :
    ApproachesSetAE P
      (fun n ω ↦ hilbertAverage (fun t ↦ x t ω) n) D.carrier := by
  obtain ⟨B, hB₀, hB⟩ := hbounded
  obtain ⟨d₀, hd₀⟩ := D.nonempty
  have hcheck : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ l in Filter.atTop,
      closedConvexPotential D
        (hilbertAverage (fun t ↦ x t ω) ((l + 1) ^ 2)) <
          (1 / (j + 1 : ℝ)) ^ 2 :=
    MeasureTheory.ae_all_iff.mpr fun j ↦
      ae_eventually_closedConvexPotential_checkpoint_lt D hd₀ hadapted hcondExp hcond
        hB₀ hB (by positivity : 0 < (1 / (j + 1 : ℝ)) ^ 2)
  filter_upwards [hB, hcheck] with ω hωB hωcheck
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / ε)
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hsmall : 1 / ((j : ℝ) + 1) < ε / 2 := by
    rw [div_lt_div_iff₀ hjpos (by norm_num : (0 : ℝ) < 2)]
    have := (div_lt_iff₀ hε).mp hj
    nlinarith
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (hωcheck j)
  obtain ⟨Q₂, hQ₂⟩ := exists_nat_gt (8 * B / ε)
  set Q : ℕ := max (L + 1) (max Q₂ 1)
  have hQL : L + 1 ≤ Q := le_max_left _ _
  have hQQ₂ : Q₂ ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQone : 1 ≤ Q := le_trans (le_max_right Q₂ 1) (le_max_right _ _)
  refine ⟨Q ^ 2, fun n hn ↦ ?_⟩
  have hnone : 1 ≤ n := le_trans (Nat.one_le_pow 2 Q hQone) hn
  set q : ℕ := Nat.sqrt n
  have hqQ : Q ≤ q := Nat.le_sqrt'.mpr hn
  have hqL : L + 1 ≤ q := le_trans hQL hqQ
  have hqQ₂ : Q₂ ≤ q := le_trans hQQ₂ hqQ
  have hqone : 1 ≤ q := le_trans hQone hqQ
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqone)
  have hqle : q ^ 2 ≤ n := Nat.sqrt_le' n
  have hqlt : n < (q + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hnq : n - q ^ 2 ≤ 2 * q := by
    have : n ≤ q ^ 2 + 2 * q := by
      have hexpand : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      rw [hexpand] at hqlt
      omega
    omega
  have hcheckpoint := hL (q - 1) (by omega)
  have hqsub : q - 1 + 1 = q := by omega
  rw [hqsub] at hcheckpoint
  have hprojDist :
      ‖hilbertAverage (fun t ↦ x t ω) (q ^ 2) -
          D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2))‖ < ε / 2 := by
    have hnormsmall :
        ‖hilbertAverage (fun t ↦ x t ω) (q ^ 2) -
            D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2))‖ <
          1 / ((j : ℝ) + 1) := by
      unfold closedConvexPotential at hcheckpoint
      have hnormnonneg := norm_nonneg
        (hilbertAverage (fun t ↦ x t ω) (q ^ 2) -
          D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2)))
      have hdelta : 0 < 1 / ((j : ℝ) + 1) := by positivity
      nlinarith
    exact hnormsmall.trans hsmall
  have hgap := norm_hilbertAverage_sub_le (fun t ↦ x t ω) hωB hqle
  have hgapSmall :
      ‖hilbertAverage (fun t ↦ x t ω) n -
          hilbertAverage (fun t ↦ x t ω) (q ^ 2)‖ < ε / 2 := by
    have hnqR : (n : ℝ) - q ^ 2 ≤ 2 * q := by
      rw [← Nat.cast_pow]
      exact_mod_cast hnq
    have hn1pos : (0 : ℝ) < n + 1 := by positivity
    have hratio₁ : 2 * B * ((n : ℝ) - q ^ 2) / (n + 1) ≤
        4 * B * q / (n + 1) := by
      rw [div_le_div_iff_of_pos_right hn1pos]
      nlinarith
    have hqsqR : (q : ℝ) ^ 2 ≤ (n : ℝ) + 1 := by
      have : (q : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hqle
      linarith
    have hratio₂ : 4 * B * q / (n + 1) ≤ 4 * B / q := by
      rw [div_le_div_iff₀ hn1pos hqpos]
      nlinarith
    have hq₂R : (Q₂ : ℝ) ≤ q := by exact_mod_cast hqQ₂
    have hQbound : 4 * B / q < ε / 2 := by
      have hQ₂ineq : 8 * B < (Q₂ : ℝ) * ε := (div_lt_iff₀ hε).mp hQ₂
      have hqineq : 8 * B < (q : ℝ) * ε :=
        lt_of_lt_of_le hQ₂ineq (mul_le_mul_of_nonneg_right hq₂R hε.le)
      rw [div_lt_div_iff₀ hqpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hgap' :
        ‖hilbertAverage (fun t ↦ x t ω) n -
            hilbertAverage (fun t ↦ x t ω) (q ^ 2)‖ ≤
          2 * B * ((n : ℝ) - (q : ℝ) ^ 2) / (n + 1) := by
      simpa only [Nat.cast_pow] using hgap
    exact hgap'.trans_lt (hratio₁.trans_lt (hratio₂.trans_lt hQbound))
  refine ⟨D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2)),
    D.projection_mem _, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖hilbertAverage (fun t ↦ x t ω) n -
        D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2))‖ ≤
      ‖hilbertAverage (fun t ↦ x t ω) n -
          hilbertAverage (fun t ↦ x t ω) (q ^ 2)‖ +
        ‖hilbertAverage (fun t ↦ x t ω) (q ^ 2) -
          D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2))‖ := by
            rw [show hilbertAverage (fun t ↦ x t ω) n -
                D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2)) =
              (hilbertAverage (fun t ↦ x t ω) n -
                hilbertAverage (fun t ↦ x t ω) (q ^ 2)) +
              (hilbertAverage (fun t ↦ x t ω) (q ^ 2) -
                D.projection (hilbertAverage (fun t ↦ x t ω) (q ^ 2))) by abel]
            exact norm_add_le _ _
    _ ≤ ε := by linarith

/-- Distance formulation of [MFoGT, Theorem 7.3.2]. Under the
Blackwell projection condition, the distance from the running average to the
closed convex target, realized by its metric projection, tends to zero almost
surely. -/
theorem blackwell_projectionDistance_tendsto_zero_ae
    (D : ClosedConvexTarget E)
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ)
    (x y : ℕ → Ω → E)
    (hadapted : MeasureTheory.Adapted ℱ x)
    (hbounded : IsUniformlyBoundedHilbertProcessAE P x)
    (hcondExp : IsHilbertConditionalExpectationSequence P ℱ x y)
    (hcond : BlackwellClosedConvexConditionAE D P x y) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n => ‖hilbertAverage (fun t ↦ x t ω) n -
          D.projection (hilbertAverage (fun t ↦ x t ω) n)‖)
        Filter.atTop (nhds 0) := by
  have happ := blackwell_approach_closedConvex_ae
    D P ℱ x y hadapted hbounded hcondExp hcond
  filter_upwards [happ] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hω (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨d, hdD, hdist⟩ := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖hilbertAverage (fun t ↦ x t ω) n -
        D.projection (hilbertAverage (fun t ↦ x t ω) n)‖
        ≤ ‖hilbertAverage (fun t ↦ x t ω) n - d‖ :=
      D.projection_minimizes _ hdD
    _ = dist (hilbertAverage (fun t ↦ x t ω) n) d := by rw [dist_eq_norm]
    _ ≤ ε / 2 := hdist
    _ < ε := half_lt_self hε

end Blackwell

end EconCSLib
