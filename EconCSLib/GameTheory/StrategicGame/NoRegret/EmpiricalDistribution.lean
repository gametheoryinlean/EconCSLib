/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NoRegret.Internal
import EconCSLib.GameTheory.StrategicGame.CorrelatedEq

/-!
# Empirical distributions under no regret

This module formalizes Hannan consistency, no-comparison-regret sets, and
convergence of empirical play to correlated equilibrium distributions from
[MFoGT, Section 7.3.4]. It contains pathwise implications and their
almost-sure liftings; `NoRegret.Process` applies them to canonical learning
laws.

## References

* [MFoGT] Chapter 7, Section 7.3.4
-/

open Finset BigOperators Filter Topology
open scoped MeasureTheory

namespace StrategicGame

universe uK uL uN uS uΩ uOut

/-- If a continuous nonnegative violation function tends to zero on a compact
metric space, the sequence approaches its nonempty zero set. Applied below,
the violation aggregates the positive parts of the finitely many regret inequalities in
[MFoGT, Propositions 7.3.13, 7.3.16, and 7.3.18]. -/
theorem approachesSet_zeroSet_of_tendsto_violation {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X]
    (viol : X → ℝ) (hcont : Continuous viol) (hnonneg : ∀ x, 0 ≤ viol x)
    (z : ℕ → X) (hz : Tendsto (fun n => viol (z n)) atTop (nhds 0)) :
    EconCSLib.ApproachesSet z {x | viol x = 0} := by
  haveI : Nonempty X := ⟨z 0⟩
  set S : Set X := {x | viol x = 0} with hS_def
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x0, -, hx0⟩ :=
      IsCompact.exists_isMinOn isCompact_univ Set.univ_nonempty hcont.continuousOn
    have hmin : ∀ y, viol x0 ≤ viol y := fun y => isMinOn_iff.mp hx0 y (Set.mem_univ y)
    have hle : viol x0 ≤ 0 := ge_of_tendsto' hz fun n => hmin (z n)
    exact ⟨x0, le_antisymm hle (hnonneg x0)⟩
  intro ε hε
  by_contra hbad
  push Not at hbad
  have hfreq : ∃ᶠ n in atTop, ε ≤ Metric.infDist (z n) S := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hnN, hn⟩ := hbad N
    exact ⟨n, hnN, (Metric.le_infDist hS_nonempty).mpr fun c hc => (hn c hc).le⟩
  obtain ⟨ψ, hψmono, hψ⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨a, φ, hφmono, hφtendsto⟩ := CompactSpace.tendsto_subseq (z ∘ ψ)
  have hcomp_tendsto : Tendsto (ψ ∘ φ) atTop atTop :=
    hψmono.tendsto_atTop.comp hφmono.tendsto_atTop
  have hviol_lim : Tendsto (fun k => viol (z (ψ (φ k)))) atTop (nhds 0) := hz.comp hcomp_tendsto
  have hviol_cont : Tendsto (fun k => viol ((z ∘ ψ) (φ k))) atTop (nhds (viol a)) :=
    (hcont.tendsto a).comp hφtendsto
  have ha_viol : viol a = 0 := tendsto_nhds_unique hviol_cont hviol_lim
  have haS : a ∈ S := ha_viol
  have hinf_lim : Tendsto (fun k => Metric.infDist ((z ∘ ψ) (φ k)) S) atTop
      (nhds (Metric.infDist a S)) :=
    (Metric.continuous_infDist_pt (s := S)).tendsto a |>.comp hφtendsto
  rw [Metric.infDist_zero_of_mem haS] at hinf_lim
  have hge : ∀ k, ε ≤ Metric.infDist ((z ∘ ψ) (φ k)) S := fun k => hψ (φ k)
  exact absurd (ge_of_tendsto' hinf_lim hge) (not_le.mpr hε)

/-! ### Applications to strategic games: MFoGT 7.3.4 -/

/-- A distribution over a two-block action space `K × L`. -/
abbrev JointDistribution (K : Type uK) (L : Type uL) [Fintype K] [Fintype L] :=
  stdSimplex ℝ (K × L)

/-- First-coordinate marginal of a finite joint distribution. -/
noncomputable def jointFirstMarginal {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] (z : JointDistribution K L) : stdSimplex ℝ K where
  val k := ∑ l : L, z.val (k, l)
  property := by
    constructor
    · intro k
      exact Finset.sum_nonneg fun l _ => z.property.1 (k, l)
    · rw [← Fintype.sum_prod_type]
      exact z.property.2

/-- Second-coordinate marginal of a finite joint distribution. -/
noncomputable def jointSecondMarginal {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] (z : JointDistribution K L) : stdSimplex ℝ L where
  val l := ∑ k : K, z.val (k, l)
  property := by
    constructor
    · intro l
      exact Finset.sum_nonneg fun k _ => z.property.1 (k, l)
    · rw [Finset.sum_comm, ← Fintype.sum_prod_type]
      exact z.property.2

/-- Expected payoff of a two-block distribution. -/
noncomputable def jointPayoff {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) : ℝ :=
  ∑ s : K × L, z.val s * F s.1 s.2

/-- Payoff from switching to a fixed `k`, keeping the marginal distribution on
opponents' moves induced by `z`. -/
noncomputable def payoffAgainstOpponentMarginal {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L]
    (F : K → L → ℝ) (k : K) (z : JointDistribution K L) : ℝ :=
  ∑ ℓ : L, (∑ j : K, z.val (j, ℓ)) * F k ℓ

/-- Payoff against a fixed second-player action, keeping the first-coordinate
marginal induced by the joint distribution. -/
noncomputable def payoffAgainstPlayerMarginal {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L]
    (F : K → L → ℝ) (l : L) (z : JointDistribution K L) : ℝ :=
  ∑ k : K, (∑ l' : L, z.val (k, l')) * F k l

/-- [MFoGT Definition 7.3.12] Hannan's set for one player. -/
def HannanSet {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : Set (JointDistribution K L) :=
  {z | ∀ k : K, payoffAgainstOpponentMarginal F k z ≤ jointPayoff F z}

/-- Hannan set of the minimizing column player in a two-player zero-sum game.
Equivalently, this is the ordinary Hannan set for payoff `-F` after swapping
the two coordinates. -/
def ColumnHannanSet {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : Set (JointDistribution K L) :=
  {z | ∀ l : L, jointPayoff F z ≤ payoffAgainstPlayerMarginal F l z}

/-- Expected payoff against a pure row is computed from the second marginal. -/
lemma payoffAgainstOpponentMarginal_eq_matrixGame_Ei
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (k : K) (z : JointDistribution K L) :
    payoffAgainstOpponentMarginal F k z =
      (⟨F⟩ : MatrixGame K L ℝ).Ei k (jointSecondMarginal z) := rfl

/-- Expected payoff against a pure column is computed from the first marginal. -/
lemma payoffAgainstPlayerMarginal_eq_matrixGame_Ej
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (l : L) (z : JointDistribution K L) :
    payoffAgainstPlayerMarginal F l z =
      (⟨F⟩ : MatrixGame K L ℝ).Ej (jointFirstMarginal z) l := rfl

/-- Zero-sum consequence following [MFoGT, Proposition 7.3.13]. If a joint
distribution satisfies the Hannan inequalities of both players, then its two
marginals are optimal strategies and its correlated expected payoff equals the
value of the matrix game. No independence of the joint distribution is
assumed. -/
theorem hannanSets_zeroSum_marginals_optimal_and_payoff_eq_value
    {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [Nonempty K] [Nonempty L]
    (F : K → L → ℝ) (z : JointDistribution K L)
    (hrow : z ∈ HannanSet F) (hcolumn : z ∈ ColumnHannanSet F) :
    jointFirstMarginal z ∈ (⟨F⟩ : MatrixGame K L ℝ).optimalRowStrategies ∧
      jointSecondMarginal z ∈ (⟨F⟩ : MatrixGame K L ℝ).optimalColumnStrategies ∧
      (⟨F⟩ : MatrixGame K L ℝ).E (jointFirstMarginal z) (jointSecondMarginal z) =
        jointPayoff F z ∧
      jointPayoff F z = (⟨F⟩ : MatrixGame K L ℝ).value := by
  let A : MatrixGame K L ℝ := ⟨F⟩
  let x : stdSimplex ℝ K := jointFirstMarginal z
  let y : stdSimplex ℝ L := jointSecondMarginal z
  let w : ℝ := jointPayoff F z
  have hrow' : ∀ k : K, A.Ei k y ≤ w := by
    intro k
    simpa only [A, y, w, payoffAgainstOpponentMarginal_eq_matrixGame_Ei] using hrow k
  have hcolumn' : ∀ l : L, w ≤ A.Ej x l := by
    intro l
    simpa only [A, x, w, payoffAgainstPlayerMarginal_eq_matrixGame_Ej] using hcolumn l
  have hw : w = A.value :=
    A.common_guarantee_eq_value w ⟨x, hcolumn'⟩ ⟨y, hrow'⟩
  have hproduct_le : A.E x y ≤ w := by
    change wsum x (fun k => A.Ei k y) ≤ w
    exact (le_iff_simplex_le.mp hrow') x
  have hproduct_ge : w ≤ A.E x y := by
    have hmix := (ge_iff_simplex_ge.mp hcolumn') y
    have hswap : A.E x y = wsum y (fun l => A.Ej x l) := by
      exact wsum_wsum_comm x y F
    rwa [hswap]
  have hproduct : A.E x y = w := le_antisymm hproduct_le hproduct_ge
  have hx : x ∈ A.optimalRowStrategies :=
    (A.mem_optimalRowStrategies_iff_E_ge x).mpr fun y' => by
      have hmix := (ge_iff_simplex_ge.mp hcolumn') y'
      have hswap : A.E x y' = wsum y' (fun l => A.Ej x l) := by
        exact wsum_wsum_comm x y' F
      rw [hswap, ← hw]
      exact hmix
  have hy : y ∈ A.optimalColumnStrategies :=
    (A.mem_optimalColumnStrategies_iff_E_le y).mpr fun x' => by
      have hmix := (le_iff_simplex_le.mp hrow') x'
      change wsum x' (fun k => A.Ei k y) ≤ A.value
      rw [← hw]
      exact hmix
  exact ⟨hx, hy, hproduct, hw⟩

/-- A sequence of distributions is the empirical distribution of the realized
two-block play path. -/
def IsEmpiricalJointDistribution {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (z : ℕ → JointDistribution K L) (play : ℕ → K × L) : Prop :=
  ∀ n : ℕ, ∀ s : K × L,
    (z n).val s =
      ((n + 1 : ℝ)⁻¹) * ∑ t : Fin (n + 1), if play t.val = s then 1 else 0

/-- The Hannan-set violation function: sum of the positive parts of the finitely many
inequalities defining `HannanSet F`. It is continuous and nonnegative, and vanishes exactly on
`HannanSet F`. -/
noncomputable def hannanViolation {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) : ℝ :=
  ∑ k : K, posPart (payoffAgainstOpponentMarginal F k z - jointPayoff F z)

lemma hannanViolation_nonneg {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) : 0 ≤ hannanViolation F z :=
  Finset.sum_nonneg fun _ _ => posPart_nonneg _

lemma hannanViolation_continuous {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : Continuous (hannanViolation F) := by
  unfold hannanViolation posPart payoffAgainstOpponentMarginal jointPayoff
  refine continuous_finsetSum _ fun k _ => Continuous.max ?_ continuous_const
  refine Continuous.sub ?_ ?_
  · exact continuous_finsetSum _ fun ℓ _ =>
      (continuous_finsetSum _ fun j _ =>
        (continuous_apply (j, ℓ)).comp continuous_subtype_val).mul continuous_const
  · exact continuous_finsetSum _ fun s _ =>
      ((continuous_apply s).comp continuous_subtype_val).mul continuous_const

lemma hannanViolation_eq_zero_iff {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) :
    hannanViolation F z = 0 ↔ z ∈ HannanSet F := by
  unfold hannanViolation
  rw [Finset.sum_eq_zero_iff_of_nonneg fun k _ => posPart_nonneg _]
  simp only [posPart_eq_zero_iff, sub_nonpos, HannanSet, Set.mem_setOf_eq, Finset.mem_univ,
    true_implies]

/-- Under an empirical joint distribution, the Hannan-set inequality gap against a fixed action
`k` coincides exactly with the average external-regret against `k`. -/
lemma payoffAgainstOpponentMarginal_sub_jointPayoff_eq_averageExternalRegret
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (F : K → L → ℝ) (z : ℕ → JointDistribution K L) (play : ℕ → K × L)
    (hEmp : IsEmpiricalJointDistribution z play) (n : ℕ) (k : K) :
    payoffAgainstOpponentMarginal F k (z n) - jointPayoff F (z n)
      = averageExternalRegret (fun m => (play m).1) (fun m k' => F k' (play m).2) n k := by
  have hstep1 : payoffAgainstOpponentMarginal F k (z n) - jointPayoff F (z n)
      = ∑ j : K, ∑ ℓ : L, (z n).val (j, ℓ) * (F k ℓ - F j ℓ) := by
    simp only [payoffAgainstOpponentMarginal, jointPayoff]
    rw [Fintype.sum_prod_type (fun s => (z n).val s * F s.1 s.2)]
    rw [show (∑ ℓ : L, (∑ j : K, (z n).val (j, ℓ)) * F k ℓ)
        = ∑ ℓ : L, ∑ j : K, (z n).val (j, ℓ) * F k ℓ from
        Finset.sum_congr rfl fun ℓ _ => Finset.sum_mul ..]
    rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  have hindicator : ∀ t : Fin (n + 1),
      (∑ j : K, ∑ ℓ : L, (if play t.val = (j, ℓ) then (1 : ℝ) else 0) * (F k ℓ - F j ℓ))
        = F k (play t.val).2 - F (play t.val).1 (play t.val).2 := by
    intro t
    rw [show (∑ j : K, ∑ ℓ : L, (if play t.val = (j, ℓ) then (1 : ℝ) else 0) * (F k ℓ - F j ℓ))
        = ∑ s : K × L, (if play t.val = s then (1 : ℝ) else 0) * (F k s.2 - F s.1 s.2) from
        (Fintype.sum_prod_type
          (fun s => (if play t.val = s then (1 : ℝ) else 0) * (F k s.2 - F s.1 s.2))).symm]
    simp only [ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq (play t.val) (fun s => F k s.2 - F s.1 s.2)
  rw [hstep1]
  simp only [averageExternalRegret, externalRegretStage]
  simp_rw [hEmp n, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  have hswap1 : ∀ j : K, (∑ ℓ : L, ∑ t : Fin (n + 1),
        (if play t.val = (j, ℓ) then (1 : ℝ) else 0) * (F k ℓ - F j ℓ))
      = ∑ t : Fin (n + 1), ∑ ℓ : L,
        (if play t.val = (j, ℓ) then (1 : ℝ) else 0) * (F k ℓ - F j ℓ) :=
    fun j => Finset.sum_comm
  simp_rw [hswap1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => hindicator t

/-- Pathwise implication in [MFoGT, Proposition 7.3.13]: no external regret
forces the empirical distribution to approach Hannan's set. -/
theorem noExternalRegret_empiricalDistribution_approaches_hannan
    {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (F : K → L → ℝ)
    (z : ℕ → JointDistribution K L) (play : ℕ → K × L)
    (hEmp : IsEmpiricalJointDistribution z play)
    (hRegret : HasNoExternalRegret (fun n => (play n).1)
      (fun n k => F k (play n).2)) :
    EconCSLib.ApproachesSet z (HannanSet F) := by
  have hHannan : HannanSet F = {x | hannanViolation F x = 0} := by
    ext x; rw [Set.mem_setOf_eq, hannanViolation_eq_zero_iff]
  rw [hHannan]
  apply approachesSet_zeroSet_of_tendsto_violation (hannanViolation F)
    (hannanViolation_continuous F) (hannanViolation_nonneg F)
  have hEq : ∀ n, hannanViolation F (z n)
      = ∑ k : K, posPart (averageExternalRegret (fun m => (play m).1)
          (fun m k' => F k' (play m).2) n k) := by
    intro n
    unfold hannanViolation
    exact Finset.sum_congr rfl fun k _ => by
      rw [payoffAgainstOpponentMarginal_sub_jointPayoff_eq_averageExternalRegret F z play hEmp n k]
  simp_rw [hEq]
  simpa using tendsto_finsetSum Finset.univ
    (fun k _ => tendsto_zero_of_vanishesAboveZero_posPart (hRegret k))

/-- The comparison gain from replacing move `j` by move `k` in a two-block
distribution. -/
noncomputable def comparisonGain {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) (j k : K) : ℝ :=
  ∑ ℓ : L, z.val (j, ℓ) * (F k ℓ - F j ℓ)

/-- Summing the comparison gains into a fixed replacement action gives exactly
the corresponding Hannan inequality gap. This is the identity displayed after
MFoGT Definition 7.3.15. -/
lemma sum_comparisonGain_eq_hannanGap
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) (k : K) :
    ∑ j : K, comparisonGain F z j k =
      payoffAgainstOpponentMarginal F k z - jointPayoff F z := by
  symm
  simp only [comparisonGain, payoffAgainstOpponentMarginal, jointPayoff]
  rw [Fintype.sum_prod_type (fun s => z.val s * F s.1 s.2)]
  rw [show (∑ ℓ : L, (∑ j : K, z.val (j, ℓ)) * F k ℓ)
      = ∑ ℓ : L, ∑ j : K, z.val (j, ℓ) * F k ℓ from
      Finset.sum_congr rfl fun ℓ _ => Finset.sum_mul ..]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- [MFoGT Definition 7.3.15] Player-one no-`C`-regret set. -/
def NoCRegretSet {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : Set (JointDistribution K L) :=
  {z | ∀ j k : K, comparisonGain F z j k ≤ 0}

/-- The no-comparison-regret set is contained in Hannan's external-regret set,
as observed immediately after MFoGT Definition 7.3.15. -/
theorem noCRegretSet_subset_hannanSet
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : NoCRegretSet F ⊆ HannanSet F := by
  intro z hz k
  have hsum : (∑ j : K, comparisonGain F z j k) ≤ 0 :=
    Finset.sum_nonpos fun j _ => hz j k
  rw [sum_comparisonGain_eq_hannanGap] at hsum
  linarith

/-- The no-`C`-regret violation function: sum of the positive parts of the finitely many
inequalities defining `NoCRegretSet F`. -/
noncomputable def noCRegretViolation {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) : ℝ :=
  ∑ j : K, ∑ k : K, posPart (comparisonGain F z j k)

lemma noCRegretViolation_nonneg {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) : 0 ≤ noCRegretViolation F z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => posPart_nonneg _

lemma noCRegretViolation_continuous {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) : Continuous (noCRegretViolation F) := by
  unfold noCRegretViolation posPart comparisonGain
  refine continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => Continuous.max ?_ continuous_const
  exact continuous_finsetSum _ fun ℓ _ =>
    ((continuous_apply (j, ℓ)).comp continuous_subtype_val).mul continuous_const

lemma noCRegretViolation_eq_zero_iff {K : Type uK} {L : Type uL} [Fintype K] [Fintype L]
    (F : K → L → ℝ) (z : JointDistribution K L) :
    noCRegretViolation F z = 0 ↔ z ∈ NoCRegretSet F := by
  unfold noCRegretViolation
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Finset.sum_nonneg fun _ _ => posPart_nonneg _]
  simp only [Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ (Finset.univ : Finset K)) =>
      posPart_nonneg _, posPart_eq_zero_iff, NoCRegretSet, Set.mem_setOf_eq,
      Finset.mem_univ, true_implies]

/-- Under an empirical joint distribution, player-one's comparison gain from replacing move `j`
by move `k` coincides exactly with the average internal regret from `j` to `k`. -/
lemma comparisonGain_eq_averageInternalRegret
    {K : Type uK} {L : Type uL} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (F : K → L → ℝ) (z : ℕ → JointDistribution K L) (play : ℕ → K × L)
    (hEmp : IsEmpiricalJointDistribution z play) (n : ℕ) (j k : K) :
    comparisonGain F (z n) j k
      = averageInternalRegret (fun m => (play m).1) (fun m k' => F k' (play m).2) n j k := by
  have hcollapse : ∀ t : Fin (n + 1),
      (∑ ℓ : L, (if play t.val = (j, ℓ) then (1 : ℝ) else 0) * (F k ℓ - F j ℓ))
        = if (play t.val).1 = j then F k (play t.val).2 - F j (play t.val).2 else 0 := by
    intro t
    set p := play t.val
    by_cases h : p.1 = j
    · rw [if_pos h]
      have heq : ∀ ℓ : L, (p = (j, ℓ)) ↔ (p.2 = ℓ) := by
        intro ℓ
        constructor
        · intro heq; rw [heq]
        · intro heq; rw [← heq, ← h]
      simp_rw [heq, ite_mul, one_mul, zero_mul]
      exact Fintype.sum_ite_eq p.2 (fun ℓ => F k ℓ - F j ℓ)
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro ℓ _
      have hne : p ≠ (j, ℓ) := fun heq => h (by rw [heq])
      rw [if_neg hne, zero_mul]
  simp only [comparisonGain, averageInternalRegret, internalRegretStage]
  simp_rw [hEmp n, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => hcollapse t

/-- Pathwise implication in [MFoGT, Proposition 7.3.16]: no internal regret
forces the empirical distribution to approach the playerwise
no-`C`-regret set. -/
theorem noInternalRegret_empiricalDistribution_approaches_playerSet
    {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (F : K → L → ℝ)
    (z : ℕ → JointDistribution K L) (play : ℕ → K × L)
    (hEmp : IsEmpiricalJointDistribution z play)
    (hRegret : HasNoInternalRegret (fun n => (play n).1)
      (fun n k => F k (play n).2)) :
    EconCSLib.ApproachesSet z (NoCRegretSet F) := by
  have hSet : NoCRegretSet F = {x | noCRegretViolation F x = 0} := by
    ext x; rw [Set.mem_setOf_eq, noCRegretViolation_eq_zero_iff]
  rw [hSet]
  apply approachesSet_zeroSet_of_tendsto_violation (noCRegretViolation F)
    (noCRegretViolation_continuous F) (noCRegretViolation_nonneg F)
  have hEq : ∀ n, noCRegretViolation F (z n)
      = ∑ j : K, ∑ k : K, posPart (averageInternalRegret (fun m => (play m).1)
          (fun m k' => F k' (play m).2) n j k) := by
    intro n
    unfold noCRegretViolation
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [comparisonGain_eq_averageInternalRegret F z play hEmp n j k]
  simp_rw [hEq]
  simpa using tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
    (fun k _ => tendsto_zero_of_vanishesAboveZero_posPart (hRegret j k)))

/-! ### Internal regret and correlated equilibria -/

variable {N : Type uN} [Fintype N] [DecidableEq N]

/-- Player `i`'s comparison gain at a correlated distribution: replace
recommendation `j` by action `k`. -/
noncomputable def playerComparisonGain
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (q : CorrelatedDistribution G) (i : N) (j k : G.strategy i) : ℝ :=
  ∑ ρ : G.Profile,
    if ρ i = j then q.val ρ * (G.payoff (deviate ρ i k) i - G.payoff ρ i) else 0

/-- Playerwise no-internal-regret half-space set. -/
def PlayerNoInternalRegretSet
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (i : N) : Set (CorrelatedDistribution G) :=
  {q | ∀ j k : G.strategy i, playerComparisonGain G q i j k ≤ 0}

/-- Intersection of all playerwise no-internal-regret sets. -/
def AllPlayersNoInternalRegretSet
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)] :
    Set (CorrelatedDistribution G) :=
  {q | ∀ i : N, q ∈ PlayerNoInternalRegretSet G i}

/-- Ex-post algebraic core of [MFoGT Proposition 7.3.17]: the intersection of the
playerwise no-internal-regret sets is exactly the signalwise obedience set. -/
theorem allPlayersNoInternalRegretSet_eq_signalwiseCED
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)] :
    AllPlayersNoInternalRegretSet G = SignalwiseCorrelatedEquilibriumDistributions G := by
  have hsign : ∀ (q : CorrelatedDistribution G) (i : N) (j k : G.strategy i),
      obedienceDifference q i j k = -playerComparisonGain G q i j k := by
    intro q i j k
    simp only [obedienceDifference, playerComparisonGain, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    by_cases hc : ρ i = j <;> simp [hc]; ring
  ext q
  rw [mem_signalwiseCorrelatedEquilibriumDistributions_iff_obedience]
  simp only [AllPlayersNoInternalRegretSet, PlayerNoInternalRegretSet, Set.mem_setOf_eq, hsign]
  constructor
  · intro h i j k; linarith [h i j k]
  · intro h i j k; linarith [h i j k]

/-- **MFoGT Proposition 7.3.17.** The intersection of all playerwise
no-internal-regret sets is the Nash-based correlated-equilibrium distribution
set. -/
theorem allPlayersNoInternalRegretSet_eq_CED
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)] :
    AllPlayersNoInternalRegretSet G = CorrelatedEquilibriumDistributions G := by
  calc
    AllPlayersNoInternalRegretSet G =
        SignalwiseCorrelatedEquilibriumDistributions G :=
      allPlayersNoInternalRegretSet_eq_signalwiseCED G
    _ = CorrelatedEquilibriumDistributions G :=
      (correlatedEquilibriumDistributions_eq_signalwise G).symm

/-- A sequence of correlated distributions is the empirical distribution of the
realized play path in `G`. -/
def IsEmpiricalCorrelatedDistribution
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : ℕ → CorrelatedDistribution G) (play : ℕ → G.Profile) : Prop :=
  ∀ n : ℕ, ∀ ρ : G.Profile,
    (z n).val ρ =
      ((n + 1 : ℝ)⁻¹) * ∑ t : Fin (n + 1), if play t.val = ρ then 1 else 0

/-- Violation of the signalwise obedience set: the sum of the positive parts of
all playerwise comparison-gain inequalities. -/
noncomputable def signalwiseCEDViolation (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : CorrelatedDistribution G) : ℝ :=
  ∑ i : N, ∑ j : G.strategy i, ∑ k : G.strategy i, posPart (playerComparisonGain G z i j k)

lemma signalwiseCEDViolation_nonneg (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : CorrelatedDistribution G) : 0 ≤ signalwiseCEDViolation G z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => posPart_nonneg _

lemma signalwiseCEDViolation_continuous (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)] :
    Continuous (signalwiseCEDViolation G) := by
  unfold signalwiseCEDViolation posPart playerComparisonGain
  refine continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => Continuous.max ?_ continuous_const
  refine continuous_finsetSum _ fun ρ _ => ?_
  by_cases h : ρ i = j
  · simpa only [h, if_true] using
      Continuous.mul ((continuous_apply ρ).comp continuous_subtype_val) continuous_const
  · simpa only [h, if_false] using continuous_const

lemma signalwiseCEDViolation_eq_zero_iff (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : CorrelatedDistribution G) :
    signalwiseCEDViolation G z = 0 ↔ z ∈ AllPlayersNoInternalRegretSet G := by
  unfold signalwiseCEDViolation
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => posPart_nonneg _]
  simp only [Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ (Finset.univ : Finset (G.strategy _))) =>
      Finset.sum_nonneg fun _ _ => posPart_nonneg _,
    Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ (Finset.univ : Finset (G.strategy _))) =>
      posPart_nonneg _,
    posPart_eq_zero_iff, AllPlayersNoInternalRegretSet, PlayerNoInternalRegretSet,
    Set.mem_setOf_eq, Finset.mem_univ, true_implies]

/-- Under an empirical correlated distribution, player `i`'s comparison gain from replacing
recommendation `j` by action `k` coincides exactly with `i`'s average internal regret from `j`
to `k`. -/
lemma playerComparisonGain_eq_averageInternalRegret
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : ℕ → CorrelatedDistribution G) (play : ℕ → G.Profile)
    (hEmp : IsEmpiricalCorrelatedDistribution G z play)
    (n : ℕ) (i : N) (j k : G.strategy i) :
    playerComparisonGain G (z n) i j k
      = averageInternalRegret (fun m => play m i)
          (fun m s => G.payoff (deviate (play m) i s) i) n j k := by
  have hcollapse : ∀ t : Fin (n + 1),
      (∑ ρ : G.Profile, if ρ i = j then
          (if play t.val = ρ then (1 : ℝ) else 0) *
            (G.payoff (deviate ρ i k) i - G.payoff ρ i)
        else 0)
        = if play t.val i = j then
            G.payoff (deviate (play t.val) i k) i - G.payoff (deviate (play t.val) i j) i
          else 0 := by
    intro t
    rw [Finset.sum_eq_single (play t.val)]
    · by_cases h : play t.val i = j
      · rw [if_pos h, if_pos h, if_pos rfl, one_mul,
          show deviate (play t.val) i j = play t.val from by
            simp only [deviate, ← h, Function.update_eq_self]]
      · rw [if_neg h, if_neg h]
    · intro ρ _ hρ
      simp [Ne.symm hρ]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [playerComparisonGain, averageInternalRegret, internalRegretStage]
  simp_rw [hEmp n, mul_assoc, Finset.sum_mul]
  simp_rw [show ∀ ρ : G.Profile, (if ρ i = j then
        (n + 1 : ℝ)⁻¹ * ∑ t : Fin (n + 1), (if play t.val = ρ then (1 : ℝ) else 0) *
            (G.payoff (deviate ρ i k) i - G.payoff ρ i)
      else 0) = (n + 1 : ℝ)⁻¹ * (if ρ i = j then
          ∑ t : Fin (n + 1), (if play t.val = ρ then (1 : ℝ) else 0) *
              (G.payoff (deviate ρ i k) i - G.payoff ρ i)
        else 0) from fun ρ => by split <;> ring]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [show ∀ ρ : G.Profile, (if ρ i = j then
        ∑ t : Fin (n + 1), (if play t.val = ρ then (1 : ℝ) else 0) *
            (G.payoff (deviate ρ i k) i - G.payoff ρ i)
      else 0) = ∑ t : Fin (n + 1), (if ρ i = j then
          (if play t.val = ρ then (1 : ℝ) else 0) *
            (G.payoff (deviate ρ i k) i - G.payoff ρ i)
        else 0) from fun ρ => by
          split
          · rfl
          · simp]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => hcollapse t

/-- Signalwise-obedience form of the pathwise implication in
[MFoGT, Proposition 7.3.18]. If every player has no internal regret, the
empirical distribution approaches the signalwise obedience set. -/
theorem noInternalRegret_allPlayers_empiricalDistribution_approaches_signalwiseCED
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : ℕ → CorrelatedDistribution G) (play : ℕ → G.Profile)
    (hEmp : IsEmpiricalCorrelatedDistribution G z play)
    (hRegret : ∀ i : N,
      HasNoInternalRegret (fun n => play n i)
        (fun n s => G.payoff (deviate (play n) i s) i)) :
    EconCSLib.ApproachesSet z (SignalwiseCorrelatedEquilibriumDistributions G) := by
  have hSet : SignalwiseCorrelatedEquilibriumDistributions G =
      {x | signalwiseCEDViolation G x = 0} := by
    ext x
    rw [Set.mem_setOf_eq, signalwiseCEDViolation_eq_zero_iff,
      ← allPlayersNoInternalRegretSet_eq_signalwiseCED]
  rw [hSet]
  apply approachesSet_zeroSet_of_tendsto_violation (signalwiseCEDViolation G)
    (signalwiseCEDViolation_continuous G) (signalwiseCEDViolation_nonneg G)
  have hEq : ∀ n, signalwiseCEDViolation G (z n)
      = ∑ i : N, ∑ j : G.strategy i, ∑ k : G.strategy i,
          posPart (averageInternalRegret (fun m => play m i)
            (fun m s => G.payoff (deviate (play m) i s) i) n j k) := by
    intro n
    unfold signalwiseCEDViolation
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by
        rw [playerComparisonGain_eq_averageInternalRegret G z play hEmp n i j k]
  simp_rw [hEq]
  simpa using tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
    (fun j _ => tendsto_finsetSum Finset.univ
      (fun k _ => tendsto_zero_of_vanishesAboveZero_posPart (hRegret i j k))))

/-- Pathwise form of [MFoGT, Proposition 7.3.18]. If every player has no
internal regret, the empirical distribution approaches the Nash-based set
`CED(G)` from [MFoGT, Section 7.2]. -/
theorem noInternalRegret_allPlayers_empiricalDistribution_approaches_CED
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (z : ℕ → CorrelatedDistribution G) (play : ℕ → G.Profile)
    (hEmp : IsEmpiricalCorrelatedDistribution G z play)
    (hRegret : ∀ i : N,
      HasNoInternalRegret (fun n => play n i)
        (fun n s => G.payoff (deviate (play n) i s) i)) :
    EconCSLib.ApproachesSet z (CorrelatedEquilibriumDistributions G) := by
  rw [correlatedEquilibriumDistributions_eq_signalwise]
  exact noInternalRegret_allPlayers_empiricalDistribution_approaches_signalwiseCED
    G z play hEmp hRegret

namespace NoRegretProbability

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω]

/-! ### Empirical distributions and games, almost surely -/

/-- A random sequence of joint distributions is the empirical distribution of a
random play path almost surely. -/
def IsEmpiricalJointDistributionAE {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (P : MeasureTheory.Measure Ω)
    (z : ℕ → Ω → JointDistribution K L) (play : ℕ → Ω → K × L) : Prop :=
  ∀ᵐ ω ∂P,
    IsEmpiricalJointDistribution (fun n => z n ω) (fun n => play n ω)

/-- Almost-sure form of the pathwise implication in [MFoGT, Proposition
7.3.13], conditional on the supplied random play having no external regret. -/
theorem noExternalRegret_empiricalDistribution_approaches_hannan_ae
    {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (P : MeasureTheory.Measure Ω) (F : K → L → ℝ)
    [MeasureTheory.IsProbabilityMeasure P]
    (z : ℕ → Ω → JointDistribution K L) (play : ℕ → Ω → K × L)
    (hEmp : IsEmpiricalJointDistributionAE P z play)
    (hRegret : HasNoExternalRegretAE P
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2)) :
    EconCSLib.ApproachesSetAE P z (HannanSet F) := by
  filter_upwards [hEmp, hRegret] with ω hEmpω hRegretω
  exact noExternalRegret_empiricalDistribution_approaches_hannan F
    (fun n => z n ω) (fun n => play n ω) hEmpω hRegretω

/-- Generated-process form of [MFoGT, Proposition 7.3.13] for the
proportional external-regret-matching rule. If the opponent-induced payoff
vector is fixed before the player's fresh stage randomization and remains in
`[-1, 1]`, the empirical joint distribution approaches the player's Hannan
set almost surely. -/
theorem externalRegretMatchingStrategy_empiricalDistribution_approaches_hannan_ae
    {K : Type uK} {L : Type uL}
    [Fintype K] [Nonempty K] [DecidableEq K]
    [Fintype L] [DecidableEq L]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ) (F : K → L → ℝ)
    (z : ℕ → Ω → JointDistribution K L) (play : ℕ → Ω → K × L)
    (hEmp : IsEmpiricalJointDistributionAE P z play)
    (hgen : IsGeneratedByExternalStrategyAE P ℱ (externalRegretMatchingStrategy K)
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2))
    (hbounded : IsBoundedPayoffProcessAE P
      (fun n ω k => F k (play n ω).2)) :
    EconCSLib.ApproachesSetAE P z (HannanSet F) := by
  apply noExternalRegret_empiricalDistribution_approaches_hannan_ae
    P F z play hEmp
  exact
    (externalRegretMatchingStrategy_hasNoExternalRegretOnGeneratedProcessesAE
      P ℱ)
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2)
      hgen hbounded

/-- Almost-sure form of the pathwise implication in [MFoGT, Proposition
7.3.16], conditional on the supplied random play having no internal regret. -/
theorem noInternalRegret_empiricalDistribution_approaches_playerSet_ae
    {K : Type uK} {L : Type uL}
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (P : MeasureTheory.Measure Ω) (F : K → L → ℝ)
    [MeasureTheory.IsProbabilityMeasure P]
    (z : ℕ → Ω → JointDistribution K L) (play : ℕ → Ω → K × L)
    (hEmp : IsEmpiricalJointDistributionAE P z play)
    (hRegret : HasNoInternalRegretAE P
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2)) :
    EconCSLib.ApproachesSetAE P z (NoCRegretSet F) := by
  filter_upwards [hEmp, hRegret] with ω hEmpω hRegretω
  exact noInternalRegret_empiricalDistribution_approaches_playerSet F
    (fun n => z n ω) (fun n => play n ω) hEmpω hRegretω

/-- Generated-process form of [MFoGT, Proposition 7.3.16] for the
invariant-measure internal-regret-matching rule. Under the same nonanticipation
and `[-1, 1]` boundedness conditions as the one-player learning theorem, the
empirical joint distribution approaches the player's no-comparison-regret set
almost surely. -/
theorem internalRegretMatchingStrategy_empiricalDistribution_approaches_playerSet_ae
    {K : Type uK} {L : Type uL}
    [Fintype K] [Nonempty K] [DecidableEq K]
    [Fintype L] [DecidableEq L]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ mΩ) (F : K → L → ℝ)
    (z : ℕ → Ω → JointDistribution K L) (play : ℕ → Ω → K × L)
    (hEmp : IsEmpiricalJointDistributionAE P z play)
    (hgen : IsGeneratedByExternalStrategyAE P ℱ (internalRegretMatchingStrategy K)
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2))
    (hbounded : IsBoundedPayoffProcessAE P
      (fun n ω k => F k (play n ω).2)) :
    EconCSLib.ApproachesSetAE P z (NoCRegretSet F) := by
  apply noInternalRegret_empiricalDistribution_approaches_playerSet_ae
    P F z play hEmp
  exact
    (internalRegretMatchingStrategy_hasNoInternalRegretOnGeneratedProcessesAE
      P ℱ)
      (fun n ω => (play n ω).1)
      (fun n ω k => F k (play n ω).2)
      hgen hbounded

/-- A random sequence of correlated distributions is the empirical distribution
of a random play path almost surely. -/
def IsEmpiricalCorrelatedDistributionAE
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (P : MeasureTheory.Measure Ω)
    (z : ℕ → Ω → CorrelatedDistribution G) (play : ℕ → Ω → G.Profile) : Prop :=
  ∀ᵐ ω ∂P,
    IsEmpiricalCorrelatedDistribution G (fun n => z n ω) (fun n => play n ω)

/-- Almost-sure signalwise-obedience form of the pathwise implication in
[MFoGT, Proposition 7.3.18]. -/
theorem noInternalRegret_allPlayers_empiricalDistribution_approaches_signalwiseCED_ae
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (z : ℕ → Ω → CorrelatedDistribution G) (play : ℕ → Ω → G.Profile)
    (hEmp : IsEmpiricalCorrelatedDistributionAE G P z play)
    (hRegret : ∀ i : N,
      HasNoInternalRegretAE P
        (fun n ω => play n ω i)
        (fun n ω s => G.payoff (deviate (play n ω) i s) i)) :
    EconCSLib.ApproachesSetAE P z (SignalwiseCorrelatedEquilibriumDistributions G) := by
  have hRegret' : ∀ᵐ ω ∂P, ∀ i : N,
      HasNoInternalRegret (fun n => play n ω i)
        (fun n s => G.payoff (deviate (play n ω) i s) i) :=
    MeasureTheory.ae_all_iff.mpr hRegret
  filter_upwards [hEmp, hRegret'] with ω hEmpω hRegretω
  exact noInternalRegret_allPlayers_empiricalDistribution_approaches_signalwiseCED G
    (fun n => z n ω) (fun n => play n ω) hEmpω hRegretω

/-- Almost-sure form of [MFoGT, Proposition 7.3.18], conditional on every
player having no internal regret under the common play law. The target is the
Nash-based set `CED(G)` defined in [MFoGT, Section 7.2]. -/
theorem noInternalRegret_allPlayers_empiricalDistribution_approaches_CED_ae
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] [∀ i : N, DecidableEq (G.strategy i)]
    (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (z : ℕ → Ω → CorrelatedDistribution G) (play : ℕ → Ω → G.Profile)
    (hEmp : IsEmpiricalCorrelatedDistributionAE G P z play)
    (hRegret : ∀ i : N,
      HasNoInternalRegretAE P
        (fun n ω => play n ω i)
        (fun n ω s => G.payoff (deviate (play n ω) i s) i)) :
    EconCSLib.ApproachesSetAE P z (CorrelatedEquilibriumDistributions G) := by
  rw [correlatedEquilibriumDistributions_eq_signalwise]
  exact noInternalRegret_allPlayers_empiricalDistribution_approaches_signalwiseCED_ae
    G P z play hEmp hRegret

end NoRegretProbability

end StrategicGame
