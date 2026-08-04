/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NoRegret.Calibration
import EconCSLib.GameTheory.StrategicGame.NoRegret.EmpiricalDistribution
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Stochastic realizations of finite no-regret procedures

This module constructs probability laws for the finite learning rules in the
sibling `NoRegret` modules. The construction uses the Ionescu--Tulcea
trajectory measure on a discrete copy of the action type. Coordinate `0` is a
dummy, and coordinate `n + 1` is the stage-`n` action; the filtration at `n`
therefore represents the information available before that action.

The main theorems realize the strategies in [MFoGT, Propositions 7.3.4,
7.3.7, and 7.3.10] against arbitrary finite-history predictable environments.
For [MFoGT, Proposition 7.3.18], the module constructs the joint law in which
all players independently apply internal-regret matching.

## Main results

* `externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable`
* `internalRegretMatchingStrategy_hasNoInternalRegretAE_against_predictable`
* `exists_forecastRule_isEpsilonCalibratedAE_against_predictable`
* `allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae`
* `correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess`

## References

* [MFoGT] Chapter 7, Section 7.3
* Ionescu--Tulcea extension theorem, as implemented by Mathlib's `trajMeasure`
-/

open Finset BigOperators Filter Topology
open scoped MeasureTheory ENNReal

namespace StrategicGame.NoRegretProbability

universe uA
universe uN uS

/-- A copy of a finite type equipped with the discrete measurable space. -/
def FiniteSample (A : Type uA) := A

namespace FiniteSample

def equiv (A : Type uA) : FiniteSample A ≃ A := Equiv.refl A

instance instFintype (A : Type uA) [Fintype A] : Fintype (FiniteSample A) :=
  Fintype.ofEquiv A (equiv A).symm

instance instDecidableEq (A : Type uA) [DecidableEq A] : DecidableEq (FiniteSample A) :=
  (equiv A).decidableEq

instance instMeasurableSpace (A : Type uA) : MeasurableSpace (FiniteSample A) := ⊤

instance instDiscreteMeasurableSpace (A : Type uA) :
    DiscreteMeasurableSpace (FiniteSample A) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def of (a : A) : FiniteSample A := a

def val (a : FiniteSample A) : A := a

instance instNonempty (A : Type uA) [Nonempty A] : Nonempty (FiniteSample A) :=
  ⟨of (Classical.choice ‹Nonempty A›)⟩

@[simp] lemma val_of (a : A) : val (of a) = a := rfl
@[simp] lemma of_val (a : FiniteSample A) : of (val a) = a := rfl
@[simp] lemma of_inj {a b : A} : of a = of b ↔ a = b := by rfl

end FiniteSample

/-- A finite probability vector as a probability mass function. -/
noncomputable def simplexPMF {A : Type uA} [Fintype A]
    (p : stdSimplex ℝ A) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.val a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => p.2.1 a), p.2.2]
    norm_num)

@[simp] lemma simplexPMF_apply {A : Type uA} [Fintype A]
    (p : stdSimplex ℝ A) (a : A) : simplexPMF p a = ENNReal.ofReal (p.val a) := rfl

/-- A history-dependent randomized rule on a finite action set. -/
abbrev FiniteTrajectoryRule (A : Type uA) [Fintype A] :=
  (n : ℕ) → (Fin n → A) → stdSimplex ℝ A

/-- The actual stage actions encoded by the shifted canonical trajectory. -/
def canonicalPlay {A : Type uA} (path : ℕ → FiniteSample A) (n : ℕ) : A :=
  FiniteSample.val (path (n + 1))

/-- The finite action history before stage `n` encoded by a canonical trajectory prefix. -/
def canonicalHistory {A : Type uA} (path : ℕ → FiniteSample A) (n : ℕ) : Fin n → A :=
  fun t => canonicalPlay path t.val

/-- The probability measure on the discrete copy of `A` associated with `p`. -/
noncomputable def simplexSampleMeasure {A : Type uA} [Fintype A]
    (p : stdSimplex ℝ A) : MeasureTheory.Measure (FiniteSample A) :=
  ((simplexPMF p).map FiniteSample.of).toMeasure

instance simplexSampleMeasure.instIsProbabilityMeasure {A : Type uA} [Fintype A]
    (p : stdSimplex ℝ A) : MeasureTheory.IsProbabilityMeasure (simplexSampleMeasure p) :=
  by rw [simplexSampleMeasure]; infer_instance

@[simp] lemma simplexSampleMeasure_real_singleton
    {A : Type uA} [Fintype A] [DecidableEq A]
    (p : stdSimplex ℝ A) (a : A) :
    (simplexSampleMeasure p).real {FiniteSample.of a} = p.val a := by
  change ENNReal.toReal
    (((simplexPMF p).map FiniteSample.of).toMeasure {FiniteSample.of a}) = p.val a
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), PMF.map_apply]
  simp [simplexPMF, ENNReal.toReal_ofReal (p.2.1 a)]

@[simp] lemma simplexPMF_map_of_apply
    {A : Type uA} [Fintype A] [DecidableEq A]
    (p : stdSimplex ℝ A) (a : FiniteSample A) :
    ((simplexPMF p).map FiniteSample.of) a =
      ENNReal.ofReal (p.val (FiniteSample.val a)) := by
  rw [PMF.map_apply]
  rw [tsum_eq_single (FiniteSample.val a)]
  · simp [simplexPMF]
  · intro b hb
    rw [if_neg]
    intro h
    apply hb
    exact (congrArg FiniteSample.val h).symm

/-- The one-step kernel induced by a finite history-dependent randomized rule. -/
noncomputable def finiteTrajectoryKernel {A : Type uA} [Fintype A]
    (q : FiniteTrajectoryRule A) (n : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic n) → FiniteSample A) (FiniteSample A) :=
  ProbabilityTheory.Kernel.ofFunOfCountable (fun x =>
    simplexSampleMeasure (q n fun t => FiniteSample.val
      (x ⟨t.val + 1, by simp only [Finset.mem_Iic]; omega⟩)))

instance finiteTrajectoryKernel.instIsMarkovKernel {A : Type uA} [Fintype A]
    (q : FiniteTrajectoryRule A) (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (finiteTrajectoryKernel q n) :=
  by
    constructor
    intro x
    change MeasureTheory.IsProbabilityMeasure
      (simplexSampleMeasure (q n fun t => FiniteSample.val
        (x ⟨t.val + 1, by simp only [Finset.mem_Iic]; omega⟩)))
    infer_instance

/-- The Ionescu--Tulcea trajectory measure generated by `q`. Coordinate zero is a
dummy; coordinate `n+1` is the action at stage `n`. -/
noncomputable def finiteTrajectoryMeasure {A : Type uA} [Fintype A] [Nonempty A]
    (q : FiniteTrajectoryRule A) : MeasureTheory.Measure (ℕ → FiniteSample A) :=
  ProbabilityTheory.Kernel.trajMeasure
    (MeasureTheory.Measure.dirac (FiniteSample.of (Classical.choice ‹Nonempty A›)))
    (finiteTrajectoryKernel q)

instance finiteTrajectoryMeasure.instIsProbabilityMeasure
    {A : Type uA} [Fintype A] [Nonempty A] (q : FiniteTrajectoryRule A) :
    MeasureTheory.IsProbabilityMeasure (finiteTrajectoryMeasure q) :=
  by rw [finiteTrajectoryMeasure]; infer_instance

lemma canonicalHistory_eq_prefix {A : Type uA} (path : ℕ → FiniteSample A) (n : ℕ) :
    canonicalHistory path n = fun t => FiniteSample.val
      (Preorder.frestrictLe n path ⟨t.val + 1, by
        simp only [Finset.mem_Iic]; omega⟩) := rfl

/-- The conditional distribution of stage `n` is exactly `q` evaluated at the
realized action history before stage `n`. -/
lemma finiteTrajectory_condProb
    {A : Type uA} [Fintype A] [Nonempty A] [DecidableEq A]
    (q : FiniteTrajectoryRule A) (n : ℕ) (a : A) :
    (fun path => (q n (canonicalHistory path n)).val a)
      =ᵐ[finiteTrajectoryMeasure q]
        MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
          (finiteTrajectoryMeasure q)
          (fun path => if canonicalPlay path n = a then 1 else 0) := by
  have hcd := ProbabilityTheory.Kernel.condDistrib_trajMeasure
    (X := fun _ => FiniteSample A)
    (μ₀ := MeasureTheory.Measure.dirac
      (FiniteSample.of (Classical.choice ‹Nonempty A›)))
    (κ := finiteTrajectoryKernel q) (a := n)
  have hcdReal :
      (fun x => (ProbabilityTheory.condDistrib
          (fun path : ℕ → FiniteSample A => path (n + 1))
          (Preorder.frestrictLe n) (finiteTrajectoryMeasure q) x).real
            {FiniteSample.of a})
        =ᵐ[MeasureTheory.Measure.map (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)]
      (fun x => (finiteTrajectoryKernel q n x).real {FiniteSample.of a}) := by
    have hcd' :
        ⇑(ProbabilityTheory.condDistrib
          (fun path : ℕ → FiniteSample A => path (n + 1))
          (Preorder.frestrictLe n) (finiteTrajectoryMeasure q))
          =ᵐ[MeasureTheory.Measure.map (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)]
            ⇑(finiteTrajectoryKernel q n) := by
      simpa only [finiteTrajectoryMeasure] using hcd
    filter_upwards [hcd'] with x hx
    rw [hx]
  have hcdPath := MeasureTheory.ae_eq_comp
    (Preorder.measurable_frestrictLe n).aemeasurable hcdReal
  have hcond := ProbabilityTheory.condDistrib_ae_eq_condExp
    (μ := finiteTrajectoryMeasure q)
    (X := Preorder.frestrictLe n)
    (Y := fun path : ℕ → FiniteSample A => path (n + 1))
    (s := {FiniteSample.of a})
    (show Measurable (Preorder.frestrictLe (π := fun _ : ℕ => FiniteSample A) n) from
      Preorder.measurable_frestrictLe n)
    (show Measurable (fun path : ℕ → FiniteSample A => path (n + 1)) from
      measurable_pi_apply (n + 1))
    (MeasurableSet.singleton _)
  have hcond' :
      (fun path => (ProbabilityTheory.condDistrib
          (fun x : ℕ → FiniteSample A => x (n + 1)) (Preorder.frestrictLe n)
          (finiteTrajectoryMeasure q) (Preorder.frestrictLe n path)).real
            {FiniteSample.of a})
        =ᵐ[finiteTrajectoryMeasure q]
      MeasureTheory.condExp (MeasureTheory.Filtration.piLE n) (finiteTrajectoryMeasure q)
        (((fun path : ℕ → FiniteSample A => path (n + 1)) ⁻¹' {FiniteSample.of a}).indicator
          (fun _ => (1 : ℝ))) := by
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    exact hcond
  have hindicator :
      ((fun path : ℕ → FiniteSample A => path (n + 1)) ⁻¹' {FiniteSample.of a}).indicator
          (fun _ => (1 : ℝ))
        = fun path => if canonicalPlay path n = a then 1 else 0 := by
    funext path
    by_cases h : canonicalPlay path n = a
    · have hs : path (n + 1) = FiniteSample.of a := by
        apply (FiniteSample.equiv A).injective
        exact h
      simp [Set.indicator, hs, h]
    · have hs : path (n + 1) ≠ FiniteSample.of a := by
        intro hs
        apply h
        exact congrArg FiniteSample.val hs
      simp [Set.indicator, hs, h]
  rw [hindicator] at hcond'
  filter_upwards [hcdPath, hcond'] with path hpath hcondpath
  rw [← hcondpath]
  change
    (ProbabilityTheory.condDistrib (fun x : ℕ → FiniteSample A => x (n + 1))
        (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)
        (Preorder.frestrictLe n path)).real {FiniteSample.of a}
      = (finiteTrajectoryKernel q n (Preorder.frestrictLe n path)).real
          {FiniteSample.of a} at hpath
  calc
    (q n (canonicalHistory path n)).val a
        = (finiteTrajectoryKernel q n (Preorder.frestrictLe n path)).real
            {FiniteSample.of a} := by
          change (q n (canonicalHistory path n)).val a =
            (simplexSampleMeasure (q n fun t => FiniteSample.val
              (Preorder.frestrictLe n path ⟨t.val + 1, by
                simp only [Finset.mem_Iic]; omega⟩))).real
              {FiniteSample.of a}
          rw [simplexSampleMeasure_real_singleton]
          congr 2
    _ = (ProbabilityTheory.condDistrib (fun x : ℕ → FiniteSample A => x (n + 1))
          (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)
          (Preorder.frestrictLe n path)).real {FiniteSample.of a} := hpath.symm

/-- Conditional expectation of any real function of the fresh action under the
canonical trajectory law. -/
lemma finiteTrajectory_condExp_apply
    {A : Type uA} [Fintype A] [Nonempty A] [DecidableEq A]
    (q : FiniteTrajectoryRule A) (n : ℕ) (f : A → ℝ) :
    MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
        (finiteTrajectoryMeasure q)
        (fun path => f (canonicalPlay path n))
      =ᵐ[finiteTrajectoryMeasure q]
        fun path => ∑ a : A, (q n (canonicalHistory path n)).val a * f a := by
  let fs : FiniteSample A → ℝ := fun a => f (FiniteSample.val a)
  have hfs_meas : MeasureTheory.StronglyMeasurable fs :=
    (measurable_of_countable fs).stronglyMeasurable
  have hcomp_int : MeasureTheory.Integrable
      (fun path : ℕ → FiniteSample A => fs (path (n + 1)))
      (finiteTrajectoryMeasure q) := by
    apply MeasureTheory.Integrable.of_bound
      ((hfs_meas.measurable.comp (measurable_pi_apply (n + 1))).aestronglyMeasurable)
      (∑ a : A, |f a|)
    filter_upwards with path
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (f a))
      (Finset.mem_univ (canonicalPlay path n))
  have hcond := ProbabilityTheory.condExp_ae_eq_integral_condDistrib
    (μ := finiteTrajectoryMeasure q)
    (X := Preorder.frestrictLe n)
    (Y := fun path : ℕ → FiniteSample A => path (n + 1))
    (f := fs)
    (show Measurable (Preorder.frestrictLe (π := fun _ : ℕ => FiniteSample A) n) from
      Preorder.measurable_frestrictLe n)
    (measurable_pi_apply (n + 1)).aemeasurable hfs_meas hcomp_int
  have hcond' :
      MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
          (finiteTrajectoryMeasure q)
          (fun path => fs (path (n + 1)))
        =ᵐ[finiteTrajectoryMeasure q]
          fun path => ∫ a, fs a ∂ProbabilityTheory.condDistrib
            (fun x : ℕ → FiniteSample A => x (n + 1))
            (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)
            (Preorder.frestrictLe n path) := by
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
    exact hcond
  have hcd := ProbabilityTheory.Kernel.condDistrib_trajMeasure
    (X := fun _ => FiniteSample A)
    (μ₀ := MeasureTheory.Measure.dirac
      (FiniteSample.of (Classical.choice ‹Nonempty A›)))
    (κ := finiteTrajectoryKernel q) (a := n)
  have hcd' :
      ⇑(ProbabilityTheory.condDistrib
        (fun path : ℕ → FiniteSample A => path (n + 1))
        (Preorder.frestrictLe n) (finiteTrajectoryMeasure q))
        =ᵐ[MeasureTheory.Measure.map (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)]
          ⇑(finiteTrajectoryKernel q n) := by
    simpa only [finiteTrajectoryMeasure] using hcd
  have hcdPath := MeasureTheory.ae_eq_comp
    (Preorder.measurable_frestrictLe n).aemeasurable hcd'
  filter_upwards [hcond', hcdPath] with path hcondPath hkernelPath
  change MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
      (finiteTrajectoryMeasure q) (fun path => fs (path (n + 1))) path = _
  rw [hcondPath]
  change ProbabilityTheory.condDistrib
      (fun x : ℕ → FiniteSample A => x (n + 1))
      (Preorder.frestrictLe n) (finiteTrajectoryMeasure q)
      (Preorder.frestrictLe n path) =
    finiteTrajectoryKernel q n (Preorder.frestrictLe n path) at hkernelPath
  rw [hkernelPath]
  change (∫ a, fs a ∂simplexSampleMeasure (q n fun t => FiniteSample.val
      (Preorder.frestrictLe n path ⟨t.val + 1, by
        simp only [Finset.mem_Iic]; omega⟩))) = _
  have hhist :
      (fun t : Fin n => FiniteSample.val
        (Preorder.frestrictLe n path ⟨t.val + 1, by
          simp only [Finset.mem_Iic]; omega⟩)) =
        canonicalHistory path n := rfl
  rw [hhist]
  rw [simplexSampleMeasure, PMF.integral_eq_sum]
  simp only [simplexPMF_map_of_apply]
  simp_rw [ENNReal.toReal_ofReal ((q n (canonicalHistory path n)).2.1 _)]
  simp only [fs, smul_eq_mul]
  exact (FiniteSample.equiv A).sum_comp
    (fun a => (q n (canonicalHistory path n)).val a * f a)

/-- Any function of the prefix through coordinate `n` is measurable for the
canonical filtration at `n`. -/
lemma measurable_piLE_of_eq_comp_frestrictLe
    {A : Type uA} [Fintype A] {Z : Type*} [MeasurableSpace Z]
    (n : ℕ) (f : (ℕ → FiniteSample A) → Z)
    (g : ((i : Finset.Iic n) → FiniteSample A) → Z)
    (hfg : f = g ∘ Preorder.frestrictLe n) :
    Measurable[MeasureTheory.Filtration.piLE n] f := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  rw [hfg]
  exact (measurable_of_countable g).comp
    (comap_measurable
      (m := (inferInstance : MeasurableSpace ((i : Finset.Iic n) → FiniteSample A)))
      (Preorder.frestrictLe (π := fun _ : ℕ => FiniteSample A) n))

/-! ## External online strategies -/

/-- A bounded payoff vector selected before the stage-`n` randomization, as a
function of the realized action history through stage `n-1`. -/
abbrev PredictablePayoffRule (K : Type uA) :=
  (n : ℕ) → (Fin n → K) → K → ℝ

/-- The prefix of `hist` strictly before the past stage `t`. -/
def historyBefore {K : Type uA} {n : ℕ} (hist : Fin n → K) (t : Fin n) : Fin t.val → K :=
  fun s => hist ⟨s.val, lt_trans s.isLt t.isLt⟩

/-- The history-only action rule obtained by feeding a predictable payoff rule
to an external online strategy. -/
noncomputable def externalTrajectoryRule
    {K : Type uA} [Fintype K]
    (σ : ExternalOnlineStrategy K) (U : PredictablePayoffRule K) :
    FiniteTrajectoryRule K :=
  fun n hist => σ n (hist, fun t => U t.val (historyBefore hist t))

/-- Canonical payoff process associated with a predictable payoff rule. -/
def canonicalPayoff
    {K : Type uA} (U : PredictablePayoffRule K)
    (n : ℕ) (path : ℕ → FiniteSample K) (k : K) : ℝ :=
  U n (canonicalHistory path n) k

/-- The canonical probability measure generated jointly by `σ` and `U`. -/
noncomputable def externalTrajectoryMeasure
    {K : Type uA} [Fintype K] [Nonempty K]
    (σ : ExternalOnlineStrategy K) (U : PredictablePayoffRule K) :
    MeasureTheory.Measure (ℕ → FiniteSample K) :=
  finiteTrajectoryMeasure (externalTrajectoryRule σ U)

instance externalTrajectoryMeasure.instIsProbabilityMeasure
    {K : Type uA} [Fintype K] [Nonempty K]
    (σ : ExternalOnlineStrategy K) (U : PredictablePayoffRule K) :
    MeasureTheory.IsProbabilityMeasure (externalTrajectoryMeasure σ U) := by
  rw [externalTrajectoryMeasure]
  infer_instance

/-- The canonical process is a genuine realization of the online strategy
against the specified predictable payoff rule. -/
theorem externalTrajectory_isGeneratedByExternalStrategyAE
    {K : Type uA} [Fintype K] [Nonempty K] [DecidableEq K]
    (σ : ExternalOnlineStrategy K) (U : PredictablePayoffRule K) :
    IsGeneratedByExternalStrategyAE
      (externalTrajectoryMeasure σ U) MeasureTheory.Filtration.piLE σ
      (fun n path => canonicalPlay path n)
      (fun n path k => canonicalPayoff U n path k) := by
  let q : FiniteTrajectoryRule K := externalTrajectoryRule σ U
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n t k
    let g : ((i : Finset.Iic n) → FiniteSample K) → ℝ := fun x =>
      if FiniteSample.val (x ⟨t.val + 1, by
        have ht := t.isLt
        simp only [Finset.mem_Iic]
        omega⟩) = k then 1 else 0
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (actionIndicator (fun m path => canonicalPlay path m) t.val k) g
    funext path
    rfl
  · intro n t k
    let g : ((i : Finset.Iic n) → FiniteSample K) → ℝ := fun x =>
      U t.val (fun s => FiniteSample.val (x ⟨s.val + 1, by
        have hs := s.isLt
        have ht := t.isLt
        simp only [Finset.mem_Iic]
        omega⟩)) k
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (fun path => canonicalPayoff U t.val path k) g
    funext path
    rfl
  · intro n k
    let g : ((i : Finset.Iic n) → FiniteSample K) → ℝ := fun x =>
      (σ n
        (fun t => FiniteSample.val (x ⟨t.val + 1, by
            simp only [Finset.mem_Iic]; omega⟩),
         fun t k' => U t.val
          (fun s => FiniteSample.val (x ⟨s.val + 1, by
            have hs := s.isLt
            have ht := t.isLt
            simp only [Finset.mem_Iic]
            omega⟩)) k')).val k
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (externalStrategyProbability σ (fun m path => canonicalPlay path m)
        (fun m path k' => canonicalPayoff U m path k') n k) g
    funext path
    rfl
  · intro n k
    have h := finiteTrajectory_condProb (externalTrajectoryRule σ U) n k
    change
      (fun path =>
        (σ n (externalHistoryOf
          (fun m => canonicalPlay path m)
          (fun m k' => canonicalPayoff U m path k') n)).val k)
        =ᵐ[externalTrajectoryMeasure σ U]
      MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
        (externalTrajectoryMeasure σ U)
        (actionIndicator (fun m path => canonicalPlay path m) n k)
    simpa only [externalTrajectoryMeasure, externalTrajectoryRule, externalHistoryOf,
      canonicalPayoff, actionIndicator] using h
  · intro n k
    let g : ((i : Finset.Iic n) → FiniteSample K) → ℝ := fun x =>
      U n (fun t => FiniteSample.val (x ⟨t.val + 1, by
        simp only [Finset.mem_Iic]; omega⟩)) k
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (fun path => canonicalPayoff U n path k) g
    funext path
    rfl

/-- Uniform boundedness of every payoff vector selected by a predictable rule. -/
def IsBoundedPredictablePayoffRule {K : Type uA} (U : PredictablePayoffRule K) : Prop :=
  ∀ n hist k, -1 ≤ U n hist k ∧ U n hist k ≤ 1

lemma canonicalPayoff_isBoundedPayoffProcessAE
    {K : Type uA} [Fintype K] [Nonempty K]
    (σ : ExternalOnlineStrategy K) {U : PredictablePayoffRule K}
    (hU : IsBoundedPredictablePayoffRule U) :
    IsBoundedPayoffProcessAE (externalTrajectoryMeasure σ U)
      (fun n path k => canonicalPayoff U n path k) := by
  filter_upwards with path
  intro n k
  exact hU n (canonicalHistory path n) k

/-- Constructed-process form of [MFoGT, Proposition 7.3.4]: external-regret
matching has no external regret almost surely against every bounded
finite-history predictable payoff rule. -/
theorem externalRegretMatchingStrategy_hasNoExternalRegretAE_against_predictable
    {K : Type uA} [Fintype K] [Nonempty K] [DecidableEq K]
    (U : PredictablePayoffRule K) (hU : IsBoundedPredictablePayoffRule U) :
    HasNoExternalRegretAE
      (externalTrajectoryMeasure (externalRegretMatchingStrategy K) U)
      (fun n path => canonicalPlay path n)
      (fun n path k => canonicalPayoff U n path k) := by
  apply externalRegretMatchingStrategy_hasNoExternalRegretOnGeneratedProcessesAE
    (externalTrajectoryMeasure (externalRegretMatchingStrategy K) U)
    MeasureTheory.Filtration.piLE
  · exact externalTrajectory_isGeneratedByExternalStrategyAE
      (externalRegretMatchingStrategy K) U
  · exact canonicalPayoff_isBoundedPayoffProcessAE
      (externalRegretMatchingStrategy K) hU

/-- Constructed-process form of [MFoGT, Proposition 7.3.7]: invariant-measure
internal-regret matching has no internal regret almost surely against every
bounded finite-history predictable payoff rule. -/
theorem internalRegretMatchingStrategy_hasNoInternalRegretAE_against_predictable
    {K : Type uA} [Fintype K] [Nonempty K] [DecidableEq K]
    (U : PredictablePayoffRule K) (hU : IsBoundedPredictablePayoffRule U) :
    HasNoInternalRegretAE
      (externalTrajectoryMeasure (internalRegretMatchingStrategy K) U)
      (fun n path => canonicalPlay path n)
      (fun n path k => canonicalPayoff U n path k) := by
  apply internalRegretMatchingStrategy_hasNoInternalRegretOnGeneratedProcessesAE
    (externalTrajectoryMeasure (internalRegretMatchingStrategy K) U)
    MeasureTheory.Filtration.piLE
  · exact externalTrajectory_isGeneratedByExternalStrategyAE
      (internalRegretMatchingStrategy K) U
  · exact canonicalPayoff_isBoundedPayoffProcessAE
      (internalRegretMatchingStrategy K) hU

/-! ## Forecasting strategies -/

/-- A nonanticipating outcome rule: the stage-`n` outcome may depend on the
forecasts strictly before stage `n`, but not on the fresh stage-`n`
randomization. -/
abbrev PredictableOutcomeRule (F : Type*) (Out : Type*) :=
  (n : ℕ) → (Fin n → F) → Out

/-- The history-only forecast rule obtained by feeding a predictable outcome
rule to a forecasting strategy. -/
noncomputable def forecastTrajectoryRule
    {Out : Type*} [Fintype Out] {V : ForecastGrid Out}
    (φ : ForecastStrategy Out V) (O : PredictableOutcomeRule V.point Out) :
    FiniteTrajectoryRule V.point :=
  fun n hist => φ n (hist, fun t => O t.val (historyBefore hist t))

/-- The outcome process induced by a predictable outcome rule on the canonical
forecast path. -/
def canonicalOutcome
    {Out : Type*} [Fintype Out] {V : ForecastGrid Out}
    (O : PredictableOutcomeRule V.point Out)
    (n : ℕ) (path : ℕ → FiniteSample V.point) : Out :=
  O n (canonicalHistory path n)

/-- The canonical probability law jointly generated by `φ` and `O`. -/
noncomputable def forecastTrajectoryMeasure
    {Out : Type*} [Fintype Out] {V : ForecastGrid Out} [Nonempty V.point]
    (φ : ForecastStrategy Out V) (O : PredictableOutcomeRule V.point Out) :
    MeasureTheory.Measure (ℕ → FiniteSample V.point) :=
  finiteTrajectoryMeasure (forecastTrajectoryRule φ O)

instance forecastTrajectoryMeasure.instIsProbabilityMeasure
    {Out : Type*} [Fintype Out] {V : ForecastGrid Out} [Nonempty V.point]
    (φ : ForecastStrategy Out V) (O : PredictableOutcomeRule V.point Out) :
    MeasureTheory.IsProbabilityMeasure (forecastTrajectoryMeasure φ O) := by
  rw [forecastTrajectoryMeasure]
  infer_instance

/-- The canonical forecast/outcome process is a genuine realization of `φ`
against `O`. -/
theorem forecastTrajectory_isGeneratedByForecastStrategyAE
    {Out : Type*} [Fintype Out] [DecidableEq Out]
    {V : ForecastGrid Out} [Nonempty V.point]
    (φ : ForecastStrategy Out V) (O : PredictableOutcomeRule V.point Out) :
    IsGeneratedByForecastStrategyAE
      (forecastTrajectoryMeasure φ O) MeasureTheory.Filtration.piLE φ
      (fun n path => canonicalPlay path n)
      (fun n path => canonicalOutcome O n path) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n t v
    let g : ((i : Finset.Iic n) → FiniteSample V.point) → ℝ := fun x =>
      if FiniteSample.val (x ⟨t.val + 1, by
        have ht := t.isLt
        simp only [Finset.mem_Iic]
        omega⟩) = v then 1 else 0
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (forecastIndicator (fun m path => canonicalPlay path m) t.val v) g
    funext path
    rfl
  · intro n t out
    let g : ((i : Finset.Iic n) → FiniteSample V.point) → ℝ := fun x =>
      if O t.val (fun s => FiniteSample.val (x ⟨s.val + 1, by
        have hs := s.isLt
        have ht := t.isLt
        simp only [Finset.mem_Iic]
        omega⟩)) = out then 1 else 0
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (outcomeIndicator (fun m path => canonicalOutcome O m path) t.val out) g
    funext path
    rfl
  · intro n v
    let g : ((i : Finset.Iic n) → FiniteSample V.point) → ℝ := fun x =>
      (φ n
        (fun t => FiniteSample.val (x ⟨t.val + 1, by
            simp only [Finset.mem_Iic]; omega⟩),
         fun t => O t.val (fun s => FiniteSample.val (x ⟨s.val + 1, by
            have hs := s.isLt
            have ht := t.isLt
            simp only [Finset.mem_Iic]
            omega⟩)))).val v
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (forecastStrategyProbability φ
        (fun m path => canonicalPlay path m)
        (fun m path => canonicalOutcome O m path) n v) g
    funext path
    rfl
  · intro n v
    have h := finiteTrajectory_condProb (forecastTrajectoryRule φ O) n v
    change
      (fun path =>
        (φ n
          (fun t => canonicalPlay path t.val,
           fun t => canonicalOutcome O t.val path)).val v)
        =ᵐ[forecastTrajectoryMeasure φ O]
      MeasureTheory.condExp (MeasureTheory.Filtration.piLE n)
        (forecastTrajectoryMeasure φ O)
        (forecastIndicator (fun m path => canonicalPlay path m) n v)
    simpa only [forecastTrajectoryMeasure, forecastTrajectoryRule,
      canonicalOutcome, forecastIndicator] using h
  · intro n out
    let g : ((i : Finset.Iic n) → FiniteSample V.point) → ℝ := fun x =>
      if O n (fun t => FiniteSample.val (x ⟨t.val + 1, by
        simp only [Finset.mem_Iic]; omega⟩)) = out then 1 else 0
    apply measurable_piLE_of_eq_comp_frestrictLe n
      (outcomeIndicator (fun m path => canonicalOutcome O m path) n out) g
    funext path
    rfl

/-- Constructed-process form of [MFoGT, Proposition 7.3.10]. For every
`ε > 0`, there is a finite-grid forecasting rule that is ε-calibrated almost
surely against every finite-history predictable outcome rule. -/
theorem exists_forecastRule_isEpsilonCalibratedAE_against_predictable
    (Out : Type*) [Fintype Out] [DecidableEq Out] [Nonempty Out]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : ForecastGrid Out) (hV : Nonempty V.point),
      let _ : Nonempty V.point := hV
      ∃ φ : ForecastStrategy Out V,
        ∀ O : PredictableOutcomeRule V.point Out,
          IsEpsilonCalibratedAE (forecastTrajectoryMeasure φ O) V ε
            (fun m path => canonicalPlay path m)
            (fun m path => canonicalOutcome O m path) := by
  obtain ⟨V, hVne, hmesh⟩ := exists_forecastGrid_meshLe Out hε
  letI : Nonempty V.point := hVne
  refine ⟨V, hVne, calibratedForecastStrategy V, ?_⟩
  intro O
  have hgen := forecastTrajectory_isGeneratedByForecastStrategyAE
    (calibratedForecastStrategy V) O
  have hno := calibratedForecastStrategy_hasNoInternalRegretAE_of_generatedProcess
    V (forecastTrajectoryMeasure (calibratedForecastStrategy V) O)
    MeasureTheory.Filtration.piLE hgen
  unfold IsEpsilonCalibratedAE IsEpsilonCalibrated
  filter_upwards [hno] with path hpath
  exact isEpsilonCalibrated_of_hasNoInternalRegret hε.le hmesh hpath

/-! ## Simultaneous play by independent player procedures -/

/-- The joint mixed action obtained by multiplying the players' mixed-action
probabilities. -/
noncomputable def independentProfileAction
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    (p : MixedProfile G) : stdSimplex ℝ G.Profile := by
  classical
  refine ⟨fun s => ∏ i : N, (p i).val (s i), ?_, ?_⟩
  · intro s
    exact Finset.prod_nonneg fun i _ => (p i).2.1 (s i)
  · rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun i _ => (p i).2.2

@[simp] lemma independentProfileAction_val
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    (p : MixedProfile G) (s : G.Profile) :
    (independentProfileAction G p).val s = ∏ i : N, (p i).val (s i) := rfl

lemma independentProfileAction_split_sum
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    (p : MixedProfile G) (i : N) (F : G.Profile → ℝ) :
    ∑ s : G.Profile, (independentProfileAction G p).val s * F s =
      ∑ opp : ∀ j : {j : N // j ≠ i}, G.strategy j,
        ∑ a : G.strategy i,
          ((p i).val a * ∏ j : {j : N // j ≠ i}, (p j).val (opp j)) *
            F ((Equiv.piSplitAt i G.strategy).symm (a, opp)) := by
  classical
  let e := Equiv.piSplitAt i G.strategy
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  change
    (∑ opp : ∀ j : {j : N // j ≠ i}, G.strategy j,
      ∑ a : G.strategy i,
        (independentProfileAction G p).val (e.symm (a, opp)) * F (e.symm (a, opp))) =
      ∑ opp : ∀ j : {j : N // j ≠ i}, G.strategy j,
        ∑ a : G.strategy i,
          ((p i).val a * ∏ j : {j : N // j ≠ i}, (p j).val (opp j)) *
            F (e.symm (a, opp))
  apply Finset.sum_congr rfl
  intro opp _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (∏ j : N, (p j).val ((e.symm (a, opp)) j)) = _
  calc
    (∏ j : N, (p j).val ((e.symm (a, opp)) j)) =
        (p i).val ((e.symm (a, opp)) i) *
          (∏ j ∈ Finset.univ.erase i, (p j).val ((e.symm (a, opp)) j)) := by
            rw [Finset.mul_prod_erase Finset.univ
              (fun j => (p j).val ((e.symm (a, opp)) j)) (Finset.mem_univ i)]
    _ = (p i).val a * ∏ j : {j : N // j ≠ i}, (p j).val (opp j) := by
      have hi : (e.symm (a, opp)) i = a := by
        simp [e, Equiv.piSplitAt_symm_apply]
      have hopp :
          (∏ j ∈ Finset.univ.erase i, (p j).val ((e.symm (a, opp)) j)) =
            ∏ j : {j : N // j ≠ i}, (p j).val (opp j) := by
        rw [Finset.prod_subtype (p := fun j : N => j ≠ i)
          (Finset.univ.erase i) (by simp)]
        apply Finset.prod_congr rfl
        intro j _
        simp [e, Equiv.piSplitAt_symm_apply, j.property]
      rw [hi, hopp]

lemma deviate_piSplitAt_symm
    {N : Type uN} [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ) (i : N)
    (a b : G.strategy i)
    (opp : ∀ j : {j : N // j ≠ i}, G.strategy j) :
    deviate ((Equiv.piSplitAt i G.strategy).symm (a, opp)) i b =
      (Equiv.piSplitAt i G.strategy).symm (b, opp) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp only [Profile.deviate_same]
    simpa only [Equiv.piSplitAt_apply] using
      (congrArg Prod.fst
        (Equiv.apply_symm_apply (Equiv.piSplitAt i G.strategy) (b, opp))).symm
  · rw [Profile.deviate_of_ne _ _ _ hki]
    have ha := congrArg Prod.snd
      (Equiv.apply_symm_apply (Equiv.piSplitAt i G.strategy) (a, opp))
    have hb := congrArg Prod.snd
      (Equiv.apply_symm_apply (Equiv.piSplitAt i G.strategy) (b, opp))
    exact congrFun ha ⟨k, hki⟩ |>.trans (congrFun hb ⟨k, hki⟩).symm

/-- The expected internal-regret matrix under independent simultaneous mixing
is an opponents-profile mixture of the usual one-player expected matrices. -/
lemma independentProfileAction_expectedInternalRegret
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (p : MixedProfile G) (i : N) (j ℓ : G.strategy i) :
    (∑ s : G.Profile, (independentProfileAction G p).val s *
      internalRegretStage (s i) (fun b => G.payoff (deviate s i b) i) j ℓ) =
      ∑ opp : ∀ k : {k : N // k ≠ i}, G.strategy k,
        (∏ k : {k : N // k ≠ i}, (p k).val (opp k)) *
          expectedInternalRegret (p i)
            (fun b => G.payoff ((Equiv.piSplitAt i G.strategy).symm (b, opp)) i) j ℓ := by
  classical
  rw [independentProfileAction_split_sum G p i]
  apply Finset.sum_congr rfl
  intro opp _
  unfold expectedInternalRegret
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hi : ((Equiv.piSplitAt i G.strategy).symm (a, opp)) i = a := by
    simpa only [Equiv.piSplitAt_apply] using
      congrArg Prod.fst (Equiv.apply_symm_apply (Equiv.piSplitAt i G.strategy) (a, opp))
  have hpayoff :
      (fun b => G.payoff
        (deviate ((Equiv.piSplitAt i G.strategy).symm (a, opp)) i b) i) =
        fun b => G.payoff ((Equiv.piSplitAt i G.strategy).symm (b, opp)) i := by
    funext b
    rw [deviate_piSplitAt_symm G i a b opp]
  rw [hi, hpayoff]
  ring

/-- Averaging over independent opponents preserves the invariant-measure
orthogonality used by the internal-regret proof. -/
lemma independentProfileAction_internalRegret_orthogonal
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (p : MixedProfile G) (i : N) (A : G.strategy i → G.strategy i → ℝ)
    (hInv : IsInvariantMeasureFor A (p i)) :
    matrixInner A (fun j ℓ =>
      ∑ s : G.Profile, (independentProfileAction G p).val s *
        internalRegretStage (s i) (fun b => G.payoff (deviate s i b) i) j ℓ) = 0 := by
  classical
  unfold matrixInner
  simp_rw [independentProfileAction_expectedInternalRegret G p i]
  simp_rw [Finset.mul_sum]
  have hswap1 :
      (∑ j : G.strategy i, ∑ ℓ : G.strategy i,
        ∑ opp : ∀ k : {k : N // k ≠ i}, G.strategy k,
          A j ℓ * ((∏ k : {k : N // k ≠ i}, (p k).val (opp k)) *
            expectedInternalRegret (p i)
              (fun b => G.payoff ((Equiv.piSplitAt i G.strategy).symm (b, opp)) i) j ℓ)) =
      ∑ j : G.strategy i,
        ∑ opp : ∀ k : {k : N // k ≠ i}, G.strategy k,
          ∑ ℓ : G.strategy i,
            A j ℓ * ((∏ k : {k : N // k ≠ i}, (p k).val (opp k)) *
              expectedInternalRegret (p i)
                (fun b => G.payoff ((Equiv.piSplitAt i G.strategy).symm (b, opp)) i) j ℓ) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hswap1, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro opp _
  let w : ℝ := ∏ k : {k : N // k ≠ i}, (p k).val (opp k)
  let U : G.strategy i → ℝ :=
    fun b => G.payoff ((Equiv.piSplitAt i G.strategy).symm (b, opp)) i
  calc
    (∑ j : G.strategy i, ∑ ℓ : G.strategy i,
        A j ℓ * (w * expectedInternalRegret (p i) U j ℓ)) =
        w * matrixInner A (expectedInternalRegret (p i) U) := by
          unfold matrixInner
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ℓ _
          ring
    _ = 0 := by
      rw [invariantMeasure_internalRegret_orthogonal A (p i) U hInv, mul_zero]

/-- The mixed profile prescribed after a finite joint-action history when every
player runs the invariant-measure internal-regret procedure. -/
noncomputable def simultaneousInternalRegretMixedProfile
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (n : ℕ) (hist : Fin n → G.Profile) : MixedProfile G :=
  fun i => internalRegretMatchingStrategy (G.strategy i) n
    (fun t => hist t i,
      fun t a => G.payoff (deviate (hist t) i a) i)

/-- The joint history rule obtained by independently sampling the mixed action
prescribed by every player's internal-regret procedure. -/
noncomputable def allPlayersInternalRegretTrajectoryRule
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    FiniteTrajectoryRule G.Profile :=
  fun n hist => independentProfileAction G
    (simultaneousInternalRegretMixedProfile G n hist)

/-- The canonical joint-play law generated by independent player procedures. -/
noncomputable def allPlayersInternalRegretTrajectoryMeasure
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    MeasureTheory.Measure (ℕ → FiniteSample G.Profile) :=
  finiteTrajectoryMeasure (allPlayersInternalRegretTrajectoryRule G)

instance allPlayersInternalRegretTrajectoryMeasure.instIsProbabilityMeasure
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    MeasureTheory.IsProbabilityMeasure (allPlayersInternalRegretTrajectoryMeasure G) := by
  rw [allPlayersInternalRegretTrajectoryMeasure]
  infer_instance

/-- A uniform absolute payoff bound obtained by summing over the finite game. -/
noncomputable def strategicGamePayoffBound
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] : ℝ :=
  ∑ s : G.Profile, ∑ i : N, |G.payoff s i|

/-- The uniform absolute payoff bound is nonnegative. -/
lemma strategicGamePayoffBound_nonneg
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)] :
    0 ≤ strategicGamePayoffBound G :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every payoff is bounded in absolute value by `strategicGamePayoffBound`. -/
lemma abs_payoff_le_strategicGamePayoffBound
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    (s : G.Profile) (i : N) :
    |G.payoff s i| ≤ strategicGamePayoffBound G := by
  calc
    |G.payoff s i| ≤ ∑ j : N, |G.payoff s j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (G.payoff s j)) (Finset.mem_univ i)
    _ ≤ ∑ t : G.Profile, ∑ j : N, |G.payoff t j| :=
      Finset.single_le_sum
        (fun t _ => Finset.sum_nonneg fun j _ => abs_nonneg (G.payoff t j))
        (Finset.mem_univ s)

/-- Every player's procedure has no internal regret almost surely under the
actual jointly generated law. This is the stochastic content needed before
applying MFoGT Proposition 7.3.18. -/
theorem allPlayersInternalRegretTrajectory_hasNoInternalRegretAE
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (i : N) :
    HasNoInternalRegretAE (allPlayersInternalRegretTrajectoryMeasure G)
      (fun n path => canonicalPlay path n i)
      (fun n path a => G.payoff (deviate (canonicalPlay path n) i a) i) := by
  let q : FiniteTrajectoryRule G.Profile := allPlayersInternalRegretTrajectoryRule G
  let P : MeasureTheory.Measure (ℕ → FiniteSample G.Profile) :=
    allPlayersInternalRegretTrajectoryMeasure G
  let 𝒢 : MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace (ℕ → FiniteSample G.Profile)) :=
    { seq := fun n => MeasureTheory.Filtration.piLE (n + 1)
      mono' := fun n m hnm =>
        (MeasureTheory.Filtration.piLE : MeasureTheory.Filtration ℕ
          (inferInstance : MeasurableSpace (ℕ → FiniteSample G.Profile))).mono (by omega)
      le' := fun n =>
        (MeasureTheory.Filtration.piLE : MeasureTheory.Filtration ℕ
          (inferInstance : MeasurableSpace (ℕ → FiniteSample G.Profile))).le (n + 1) }
  let x : ℕ → (ℕ → FiniteSample G.Profile) →
      (G.strategy i × G.strategy i) → ℝ := fun n path jl =>
    internalRegretStage (canonicalPlay path n i)
      (fun a => G.payoff (deviate (canonicalPlay path n) i a) i) jl.1 jl.2
  let y : ℕ → (ℕ → FiniteSample G.Profile) →
      (G.strategy i × G.strategy i) → ℝ := fun n path jl =>
    ∑ s : G.Profile, (q n (canonicalHistory path n)).val s *
      internalRegretStage (s i) (fun a => G.payoff (deviate s i a) i) jl.1 jl.2
  have hadapted : MeasureTheory.Adapted 𝒢 x := by
    intro n
    show Measurable[MeasureTheory.Filtration.piLE (n + 1)] (x n)
    let g : ((k : Finset.Iic (n + 1)) → FiniteSample G.Profile) →
        (G.strategy i × G.strategy i) → ℝ := fun pref jl =>
      internalRegretStage (FiniteSample.val (pref ⟨n + 1, by simp⟩) i)
        (fun a => G.payoff
          (deviate (FiniteSample.val (pref ⟨n + 1, by simp⟩)) i a) i) jl.1 jl.2
    apply measurable_piLE_of_eq_comp_frestrictLe (n + 1) (x n) g
    funext path
    rfl
  let B : ℝ := strategicGamePayoffBound G
  have hBnonneg : 0 ≤ B := strategicGamePayoffBound_nonneg G
  have hbound : ∀ path n jl, |x n path jl| ≤ 2 * B := by
    intro path n jl
    change |internalRegretStage (canonicalPlay path n i)
      (fun a => G.payoff (deviate (canonicalPlay path n) i a) i) jl.1 jl.2| ≤ 2 * B
    unfold internalRegretStage
    split
    · calc
        |G.payoff (deviate (canonicalPlay path n) i jl.2) i -
            G.payoff (deviate (canonicalPlay path n) i jl.1) i| ≤
            |G.payoff (deviate (canonicalPlay path n) i jl.2) i| +
              |G.payoff (deviate (canonicalPlay path n) i jl.1) i| := abs_sub _ _
        _ ≤ B + B := add_le_add
          (abs_payoff_le_strategicGamePayoffBound G _ i)
          (abs_payoff_le_strategicGamePayoffBound G _ i)
        _ = 2 * B := by ring
    · simp [hBnonneg]
  have hbounded : IsUniformlyBoundedVectorProcessAE P x := by
    intro jl
    refine ⟨2 * B, mul_nonneg (by norm_num) hBnonneg, ?_⟩
    filter_upwards with path
    intro n
    exact hbound path n jl
  have hintegrable : ∀ n jl, MeasureTheory.Integrable (fun path => x n path jl) P := by
    intro n jl
    have hmeas : MeasureTheory.StronglyMeasurable (fun path => x n path jl) :=
      ((measurable_pi_apply jl).comp (hadapted n)).stronglyMeasurable.mono (𝒢.le n)
    apply MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable (2 * B)
    filter_upwards with path
    simpa only [Real.norm_eq_abs] using hbound path n jl
  have hcondExp : IsConditionalExpectationSequence P 𝒢 x y := by
    refine ⟨hintegrable, ?_⟩
    intro n jl
    have h := finiteTrajectory_condExp_apply q (n + 1)
      (fun s : G.Profile =>
        internalRegretStage (s i) (fun a => G.payoff (deviate s i a) i) jl.1 jl.2)
    change (fun path => y (n + 1) path jl) =ᵐ[P]
      MeasureTheory.condExp (MeasureTheory.Filtration.piLE (n + 1)) P
        (fun path => x (n + 1) path jl)
    simpa only [P, allPlayersInternalRegretTrajectoryMeasure, q, x, y] using h.symm
  have hblackwell : BlackwellNegativeOrthantConditionAE P x y := by
    filter_upwards with path
    intro n
    set r : (G.strategy i × G.strategy i) → ℝ :=
      averageVector (fun m => x m path) n with hr_def
    set A : G.strategy i → G.strategy i → ℝ := fun j ℓ => posPart (r (j, ℓ))
      with hA_def
    set p : MixedProfile G := simultaneousInternalRegretMixedProfile G (n + 1)
      (canonicalHistory path (n + 1)) with hp_def
    have hInv : IsInvariantMeasureFor A (p i) := by
      rw [hp_def]
      change IsInvariantMeasureFor
        (fun j ℓ => posPart
          (averageInternalRegret (fun m => canonicalPlay path m i)
            (fun m a => G.payoff (deviate (canonicalPlay path m) i a) i) n j ℓ))
        (internalRegretMatchingStrategy (G.strategy i) (n + 1)
          (fun t => canonicalHistory path (n + 1) t i,
            fun t a => G.payoff (deviate (canonicalHistory path (n + 1) t) i a) i))
      simpa only [canonicalHistory] using
        internalRegretMatchingStrategy_isInvariantMeasureFor_average
          (fun m => canonicalPlay path m i)
          (fun m a => G.payoff (deviate (canonicalPlay path m) i a) i) n
    have horth := independentProfileAction_internalRegret_orthogonal G p i A hInv
    have hy : ∀ j ℓ, y (n + 1) path (j, ℓ) =
        ∑ s : G.Profile, (independentProfileAction G p).val s *
          internalRegretStage (s i) (fun a => G.payoff (deviate s i a) i) j ℓ := by
      intro j ℓ
      simp only [y, q, allPlayersInternalRegretTrajectoryRule, hp_def]
    have hkey : ∑ jl : G.strategy i × G.strategy i,
        vectorPosPart r jl * y (n + 1) path jl = 0 := by
      calc
        (∑ jl : G.strategy i × G.strategy i,
            vectorPosPart r jl * y (n + 1) path jl) =
            ∑ j : G.strategy i, ∑ ℓ : G.strategy i,
              A j ℓ * (∑ s : G.Profile, (independentProfileAction G p).val s *
                internalRegretStage (s i) (fun a => G.payoff (deviate s i a) i) j ℓ) := by
                  rw [Fintype.sum_prod_type]
                  apply Finset.sum_congr rfl
                  intro j _
                  apply Finset.sum_congr rfl
                  intro ℓ _
                  rw [hy j ℓ]
                  rfl
        _ = matrixInner A (fun j ℓ =>
              ∑ s : G.Profile, (independentProfileAction G p).val s *
                internalRegretStage (s i) (fun a => G.payoff (deviate s i a) i) j ℓ) := rfl
        _ = 0 := horth
    have hkey2 : ∑ jl : G.strategy i × G.strategy i,
        vectorPosPart r jl * negativeOrthantProjection r jl = 0 :=
      Finset.sum_eq_zero fun jl _ => vectorPosPart_mul_negativeOrthantProjection_eq_zero r jl
    show ∑ jl : G.strategy i × G.strategy i,
      vectorPosPart r jl * (y (n + 1) path jl - negativeOrthantProjection r jl) ≤ 0
    rw [show (∑ jl : G.strategy i × G.strategy i,
        vectorPosPart r jl * (y (n + 1) path jl - negativeOrthantProjection r jl)) =
      (∑ jl : G.strategy i × G.strategy i, vectorPosPart r jl * y (n + 1) path jl) -
        ∑ jl : G.strategy i × G.strategy i,
          vectorPosPart r jl * negativeOrthantProjection r jl from by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro jl _
            ring]
    rw [hkey, hkey2]
    norm_num
  have happroach := blackwell_approach_negativeOrthant_ae P 𝒢 x y
    hadapted hbounded hcondExp hblackwell
  filter_upwards [happroach] with path hpath
  intro j ℓ
  have hcoord := hpath (j, ℓ)
  simpa only [x] using hcoord

/-- The empirical distribution of the canonical joint play through stage `n`. -/
noncomputable def canonicalEmpiricalCorrelatedDistribution
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (n : ℕ) (path : ℕ → FiniteSample G.Profile) : CorrelatedDistribution G := by
  classical
  refine ⟨fun s => ((n + 1 : ℝ)⁻¹) *
    ∑ t : Fin (n + 1), if canonicalPlay path t.val = s then 1 else 0, ?_, ?_⟩
  · intro s
    positivity
  · change (∑ s : G.Profile, ((n + 1 : ℝ)⁻¹) *
        ∑ t : Fin (n + 1), if canonicalPlay path t.val = s then 1 else 0) = 1
    rw [← Finset.mul_sum]
    have hswap :
        (∑ s : G.Profile, ∑ t : Fin (n + 1),
          if canonicalPlay path t.val = s then (1 : ℝ) else 0) =
        ∑ t : Fin (n + 1), ∑ s : G.Profile,
          if canonicalPlay path t.val = s then (1 : ℝ) else 0 := Finset.sum_comm
    rw [hswap]
    simp
    field_simp

/-- The canonical empirical distribution is the empirical distribution of the
canonical joint-play path. -/
lemma canonicalEmpiricalCorrelatedDistribution_isEmpirical
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)]
    (path : ℕ → FiniteSample G.Profile) :
    IsEmpiricalCorrelatedDistribution G
      (fun n => canonicalEmpiricalCorrelatedDistribution G n path)
      (fun n => canonicalPlay path n) := by
  intro n s
  rfl

/-- Constructed-process form of [MFoGT, Proposition 7.3.18]: if every player
independently uses internal-regret matching, the empirical distribution of
joint play approaches `CED(G)` almost surely. -/
theorem allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    EconCSLib.ApproachesSetAE (allPlayersInternalRegretTrajectoryMeasure G)
      (fun n path => canonicalEmpiricalCorrelatedDistribution G n path)
      (CorrelatedEquilibriumDistributions G) := by
  apply noInternalRegret_allPlayers_empiricalDistribution_approaches_CED_ae G
    (allPlayersInternalRegretTrajectoryMeasure G)
    (fun n path => canonicalEmpiricalCorrelatedDistribution G n path)
    (fun n path => canonicalPlay path n)
  · filter_upwards with path
    exact canonicalEmpiricalCorrelatedDistribution_isEmpirical G path
  · intro i
    exact allPlayersInternalRegretTrajectory_hasNoInternalRegretAE G i

/-- Existence consequence following [MFoGT, Proposition 7.3.18]: every finite
real-payoff game with nonempty action sets has a correlated equilibrium
distribution. -/
theorem correlatedEquilibriumDistributions_nonempty_of_internalRegretProcess
    {N : Type uN} [Fintype N] [DecidableEq N]
    (G : StrategicGame.{uN, 0, uS} N ℝ)
    [∀ i : N, Fintype (G.strategy i)]
    [∀ i : N, Nonempty (G.strategy i)]
    [∀ i : N, DecidableEq (G.strategy i)] :
    (CorrelatedEquilibriumDistributions G).Nonempty := by
  have hAE := allPlayersInternalRegret_empiricalDistribution_approaches_CED_ae G
  rw [EconCSLib.ApproachesSetAE] at hAE
  obtain ⟨path, hpath⟩ := hAE.exists
  obtain ⟨M, hM⟩ := hpath 1 zero_lt_one
  obtain ⟨q, hq, _⟩ := hM M le_rfl
  exact ⟨q, hq⟩

end StrategicGame.NoRegretProbability
