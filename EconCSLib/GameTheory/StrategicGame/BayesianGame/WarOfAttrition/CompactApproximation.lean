/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.BayesianGame.WarOfAttrition

/-!
# Compact-support approximation in the Bayesian war of attrition

This module proves item 3 of [MFoGT, Example 7.4.1]. Each private-value law
has a continuous density that is strictly positive on a compact interval
`[v - εₙ, v + εₙ]` and zero off its interior, with `εₙ → 0`.

The proof has two substantive parts:

* the displayed pure strategy is an actual symmetric Bayesian equilibrium
  against every nonnegative concession-time deviation;
* the CDF order isomorphism realizes each type law from one uniform random
  variable. The cumulative-hazard identity bounds the candidate action by
  `εₙ` times the same exponential quantile, and dominated convergence gives
  weak convergence of the equilibrium action laws to `Q_v`.

No coupling, equilibrium, or convergence certificate is stored in the model.
They are all derived from its density, CDF, and shrinking-support hypotheses.

## Main declarations

* `CompactDensityModel` - a regular compact-support private-value model;
* `CompactDensityModel.candidate_isSymmetricBayesianEquilibrium` - equilibrium
  of the source's displayed strategy;
* `CompactDensityModel.regularEquilibrium_eq_candidate` - uniqueness in the
  locally absolutely continuous regular class;
* `CompactActionLawSequence` - models supported on shrinking intervals;
* `CompactActionLawSequence.candidate_isEquilibrium` - equilibrium at every
  index;
* `CompactActionLawSequence.convergesToExponentialLaw` - convergence of the
  equilibrium action laws to `Q_v`.

## References

* [MFoGT] Chapter 7, Example 7.4.1
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace StrategicGame.WarOfAttrition

/-- A compactly supported positive-density private-value model. -/
structure CompactDensityModel where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  typeLaw : Measure ℝ
  [typeLaw_probability : IsProbabilityMeasure typeLaw]
  density : ℝ → ℝ
  continuous_density : Continuous density
  density_nonnegative : ∀ x, 0 ≤ density x
  density_pos : ∀ x ∈ Ioo lower upper, 0 < density x
  density_zero_off_support : ∀ x ∉ Ioo lower upper, density x = 0
  typeLaw_eq_withDensity :
    typeLaw =
      volume.withDensity (fun x => ENNReal.ofReal (density x))
  hasDerivAt_cdf :
    ∀ x, HasDerivAt (cdf typeLaw) (density x) x
  cdf_lower : cdf typeLaw lower = 0
  cdf_upper : cdf typeLaw upper = 1

attribute [instance] CompactDensityModel.typeLaw_probability

namespace CompactDensityModel

theorem continuous_cdf (M : CompactDensityModel) :
    Continuous (cdf M.typeLaw) :=
  continuous_iff_continuousAt.mpr fun x =>
    (M.hasDerivAt_cdf x).continuousAt

theorem strictMonoOn_cdf (M : CompactDensityModel) :
    StrictMonoOn (cdf M.typeLaw) (Icc M.lower M.upper) := by
  apply strictMonoOn_of_deriv_pos
    (convex_Icc M.lower M.upper) M.continuous_cdf.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(M.hasDerivAt_cdf x).deriv]
  exact M.density_pos x hx

theorem image_cdf_Icc (M : CompactDensityModel) :
    cdf M.typeLaw '' Icc M.lower M.upper = unitInterval := by
  rw [M.continuous_cdf.continuousOn.image_Icc_of_monotoneOn
    M.lower_lt_upper.le M.strictMonoOn_cdf.monotoneOn]
  simp [M.cdf_lower, M.cdf_upper, unitInterval]

noncomputable def cdfOrderIso (M : CompactDensityModel) :
    Icc M.lower M.upper ≃o unitInterval :=
  (M.strictMonoOn_cdf.orderIso (cdf M.typeLaw)
      (Icc M.lower M.upper)).trans
    (OrderIso.setCongr _ _ M.image_cdf_Icc)

@[simp]
theorem cdfOrderIso_apply_coe (M : CompactDensityModel)
    (x : Icc M.lower M.upper) :
    ((M.cdfOrderIso x : unitInterval) : ℝ) = cdf M.typeLaw x := rfl

noncomputable def typeQuantile (M : CompactDensityModel)
    (u : unitInterval) : ℝ :=
  M.cdfOrderIso.symm u

theorem measurable_typeQuantile (M : CompactDensityModel) :
    Measurable M.typeQuantile :=
  M.cdfOrderIso.symm.continuous.measurable.subtype_val

theorem typeQuantile_mem (M : CompactDensityModel) (u : unitInterval) :
    M.typeQuantile u ∈ Icc M.lower M.upper :=
  (M.cdfOrderIso.symm u).property

@[simp]
theorem cdf_typeQuantile (M : CompactDensityModel) (u : unitInterval) :
    cdf M.typeLaw (M.typeQuantile u) = u := by
  have h := M.cdfOrderIso.apply_symm_apply u
  exact congrArg Subtype.val h

theorem map_typeQuantile (M : CompactDensityModel) :
    volume.map M.typeQuantile = M.typeLaw := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply M.measurable_typeQuantile measurableSet_Iic]
  rcases lt_or_ge x M.lower with hx | hx
  · have hempty :
        M.typeQuantile ⁻¹' Iic x = ∅ := by
      ext u
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (hx.trans_le (M.typeQuantile_mem u).1)
    rw [hempty]
    simp only [measure_empty]
    rw [← ofReal_cdf M.typeLaw x]
    have hzero : cdf M.typeLaw x = 0 := by
      exact le_antisymm
        ((monotone_cdf M.typeLaw hx.le).trans_eq M.cdf_lower)
        (cdf_nonneg M.typeLaw x)
    simp [hzero]
  · rcases lt_or_ge x M.upper with hxupper | hxupper
    · let xu : Icc M.lower M.upper := ⟨x, hx, hxupper.le⟩
      let cu : unitInterval :=
        M.cdfOrderIso xu
      have hpreimage :
          M.typeQuantile ⁻¹' Iic x = Iic cu := by
        ext u
        change M.cdfOrderIso.symm u ≤ xu ↔ u ≤ cu
        constructor
        · intro h
          have h' := M.cdfOrderIso.monotone h
          simpa [cu] using h'
        · intro h
          have h' := M.cdfOrderIso.symm.monotone h
          simpa [cu] using h'
      rw [hpreimage, unitInterval.volume_Iic]
      rw [← ofReal_cdf M.typeLaw x]
      congr 1
    · have huniv :
          M.typeQuantile ⁻¹' Iic x = Set.univ := by
        ext u
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (M.typeQuantile_mem u).2.trans hxupper
      rw [huniv]
      rw [measure_univ, ← ofReal_cdf M.typeLaw x]
      have hone : cdf M.typeLaw x = 1 := by
        exact le_antisymm
          (cdf_le_one M.typeLaw x)
          (M.cdf_upper ▸ monotone_cdf M.typeLaw hxupper)
      simp [hone]

theorem cdf_eq_zero_of_le_lower (M : CompactDensityModel) {x : ℝ}
    (hx : x ≤ M.lower) :
    cdf M.typeLaw x = 0 :=
  le_antisymm
    ((monotone_cdf M.typeLaw hx).trans_eq M.cdf_lower)
    (cdf_nonneg M.typeLaw x)

theorem cdf_eq_one_of_upper_le (M : CompactDensityModel) {x : ℝ}
    (hx : M.upper ≤ x) :
    cdf M.typeLaw x = 1 :=
  le_antisymm
    (cdf_le_one M.typeLaw x)
    (M.cdf_upper ▸ monotone_cdf M.typeLaw hx)

theorem survival_pos_of_lt_upper (M : CompactDensityModel) {x : ℝ}
    (hx : x < M.upper) :
    0 < 1 - cdf M.typeLaw x := by
  rcases le_total x M.lower with hxl | hlx
  · rw [M.cdf_eq_zero_of_le_lower hxl]
    norm_num
  · have hstrict :
        cdf M.typeLaw x < cdf M.typeLaw M.upper :=
      M.strictMonoOn_cdf ⟨hlx, hx.le⟩
        ⟨M.lower_lt_upper.le, le_rfl⟩ hx
    rw [M.cdf_upper] at hstrict
    linarith

noncomputable def candidateRaw (M : CompactDensityModel)
    (value : ℝ) : ℝ :=
  ∫ t in 0..value,
    t * M.density t / (1 - cdf M.typeLaw t)

theorem continuousOn_candidateIntegrand_below_upper
    (M : CompactDensityModel) {b : ℝ} (hb : b < M.upper) :
    ContinuousOn
      (fun t => t * M.density t / (1 - cdf M.typeLaw t))
      (Icc 0 b) := by
  refine
    (continuousOn_id.mul M.continuous_density.continuousOn).div
      (continuousOn_const.sub M.continuous_cdf.continuousOn) ?_
  intro x hx
  exact (M.survival_pos_of_lt_upper (hx.2.trans_lt hb)).ne'

theorem candidateRaw_hasDerivAt (M : CompactDensityModel) {x : ℝ}
    (hx : x < M.upper) :
    HasDerivAt M.candidateRaw
      (x * M.density x / (1 - cdf M.typeLaw x)) x := by
  let integrand :=
    fun t => t * M.density t / (1 - cdf M.typeLaw t)
  have hupper0 : 0 < M.upper :=
    M.lower_pos.trans M.lower_lt_upper
  have hmax : max 0 x < M.upper := max_lt hupper0 hx
  have hcontinuous :
      ContinuousOn integrand (uIcc 0 x) := by
    refine
      (continuousOn_id.mul M.continuous_density.continuousOn).div
        (continuousOn_const.sub M.continuous_cdf.continuousOn) ?_
    intro t ht
    have htmax : t ≤ max 0 x := by
      rcases mem_uIcc.mp ht with htx | htx
      · exact htx.2.trans (le_max_right 0 x)
      · exact htx.2.trans (le_max_left 0 x)
    exact
      (M.survival_pos_of_lt_upper
        (htmax.trans_lt hmax)).ne'
  have hint : IntervalIntegrable integrand volume 0 x :=
    hcontinuous.intervalIntegrable
  have hmeas : Measurable integrand := by
    dsimp [integrand]
    exact
      (measurable_id.mul M.continuous_density.measurable).div
        (measurable_const.sub M.continuous_cdf.measurable)
  have hcontAt : ContinuousAt integrand x := by
    exact
      (continuousAt_id.mul M.continuous_density.continuousAt).div
        (continuousAt_const.sub M.continuous_cdf.continuousAt)
        (M.survival_pos_of_lt_upper hx).ne'
  simpa [candidateRaw, integrand] using
    intervalIntegral.integral_hasDerivAt_right hint
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter hcontAt

/-- The compact-support candidate, defined arbitrarily as zero at and above
the null upper endpoint. -/
noncomputable def candidate (M : CompactDensityModel) (value : ℝ) : ℝ :=
  if value < M.upper then M.candidateRaw value else 0

theorem candidate_eq_raw (M : CompactDensityModel) {value : ℝ}
    (hvalue : value < M.upper) :
    M.candidate value = M.candidateRaw value := by
  simp [candidate, hvalue]

theorem continuousOn_candidateRaw_below_upper
    (M : CompactDensityModel) :
    ContinuousOn M.candidateRaw (Iio M.upper) := by
  intro x hx
  exact
    (M.candidateRaw_hasDerivAt hx).continuousAt.continuousWithinAt

theorem continuousOn_candidate_below_upper (M : CompactDensityModel) :
    ContinuousOn M.candidate (Iio M.upper) := by
  intro x hx
  exact
    (M.continuousOn_candidateRaw_below_upper x hx).congr_of_mem
      (fun y hy => M.candidate_eq_raw hy) hx

theorem measurable_candidate (M : CompactDensityModel) :
    Measurable M.candidate := by
  rw [show M.candidate =
      (Iio M.upper).piecewise M.candidateRaw 0 by
    funext x
    simp [candidate, Set.piecewise]]
  exact M.continuousOn_candidateRaw_below_upper.measurable_piecewise
    continuous_const.continuousOn measurableSet_Iio

noncomputable def cumulativeHazard (M : CompactDensityModel)
    (value : ℝ) : ℝ :=
  -Real.log (1 - cdf M.typeLaw value)

theorem cumulativeHazard_nonnegative (M : CompactDensityModel) {value : ℝ}
    (hvalue : value < M.upper) :
    0 ≤ M.cumulativeHazard value := by
  unfold cumulativeHazard
  have hs0 := (M.survival_pos_of_lt_upper hvalue).le
  have hs1 : 1 - cdf M.typeLaw value ≤ 1 := by
    linarith [cdf_nonneg M.typeLaw value]
  exact neg_nonneg.mpr (Real.log_nonpos hs0 hs1)

theorem integral_hazardDensity (M : CompactDensityModel) {value : ℝ}
    (hvalue0 : 0 ≤ value) (hvalue : value < M.upper) :
    (∫ t in 0..value,
        M.density t / (1 - cdf M.typeLaw t)) =
      M.cumulativeHazard value := by
  let H := fun x : ℝ => -Real.log (1 - cdf M.typeLaw x)
  let h := fun x : ℝ => M.density x / (1 - cdf M.typeLaw x)
  have hcontinuousH : ContinuousOn H (Icc 0 value) := by
    intro x hx
    have hs :
        1 - cdf M.typeLaw x ≠ 0 :=
      (M.survival_pos_of_lt_upper (hx.2.trans_lt hvalue)).ne'
    exact
      (((hasDerivAt_const x (1 : ℝ)).sub
        (M.hasDerivAt_cdf x)).log hs).neg.continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Ioo 0 value, HasDerivAt H (h x) x := by
    intro x hx
    have hs :
        1 - cdf M.typeLaw x ≠ 0 :=
      (M.survival_pos_of_lt_upper (hx.2.trans hvalue)).ne'
    convert
      (((hasDerivAt_const x (1 : ℝ)).sub
        (M.hasDerivAt_cdf x)).log hs).neg using 1
    all_goals
      dsimp [H, h]
      ring
  have hhcont :
      ContinuousOn h (Icc 0 value) := by
    dsimp [h]
    refine
      M.continuous_density.continuousOn.div
        (continuousOn_const.sub M.continuous_cdf.continuousOn) ?_
    intro x hx
    exact
      (M.survival_pos_of_lt_upper (hx.2.trans_lt hvalue)).ne'
  have hhcont' : ContinuousOn h (uIcc 0 value) := by
    simpa [uIcc_of_le hvalue0] using hhcont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvalue0
    hcontinuousH hderiv hhcont'.intervalIntegrable]
  have hcdf0 :
      cdf M.typeLaw 0 = 0 :=
    M.cdf_eq_zero_of_le_lower M.lower_pos.le
  simp [H, cumulativeHazard, hcdf0]

theorem candidate_nonnegative (M : CompactDensityModel) {value : ℝ}
    (hvalue : value ∈ Ico M.lower M.upper) :
    0 ≤ M.candidate value := by
  rw [M.candidate_eq_raw hvalue.2, candidateRaw]
  apply intervalIntegral.integral_nonneg
    (M.lower_pos.le.trans hvalue.1)
  intro t ht
  exact div_nonneg
    (mul_nonneg ht.1 (M.density_nonnegative t))
    (M.survival_pos_of_lt_upper (ht.2.trans_lt hvalue.2)).le

theorem candidate_lower (M : CompactDensityModel) :
    M.candidate M.lower = 0 := by
  rw [M.candidate_eq_raw M.lower_lt_upper, candidateRaw]
  have hzero :
      (∫ t in 0..M.lower,
        t * M.density t / (1 - cdf M.typeLaw t)) =
        ∫ _t in 0..M.lower, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht_not_support : t ∉ Ioo M.lower M.upper := by
      intro h
      exact (not_lt_of_ge (by
        rcases mem_uIcc.mp ht with ht | ht
        · exact ht.2
        · exact ht.2.trans M.lower_pos.le)) h.1
    simp [M.density_zero_off_support t ht_not_support]
  rw [hzero]
  simp

theorem candidate_hasDerivAt (M : CompactDensityModel) {value : ℝ}
    (hvalue : value < M.upper) :
    HasDerivAt M.candidate
      (value * M.density value /
        (1 - cdf M.typeLaw value)) value := by
  apply (M.candidateRaw_hasDerivAt hvalue).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hvalue] with x hx
  exact M.candidate_eq_raw hx

theorem strictMonoOn_candidate (M : CompactDensityModel) :
    StrictMonoOn M.candidate (Ico M.lower M.upper) := by
  apply strictMonoOn_of_deriv_pos
    (convex_Ico M.lower M.upper)
    (M.continuousOn_candidate_below_upper.mono Ico_subset_Iio_self)
  intro x hx
  rw [interior_Ico] at hx
  rw [(M.candidate_hasDerivAt hx.2).deriv]
  exact div_pos
    (mul_pos (M.lower_pos.trans hx.1)
      (M.density_pos x hx))
    (M.survival_pos_of_lt_upper hx.2)

theorem lower_mul_cumulativeHazard_le_candidate
    (M : CompactDensityModel) {value : ℝ}
    (hvalue : value ∈ Ico M.lower M.upper) :
    M.lower * M.cumulativeHazard value ≤ M.candidate value := by
  let h :=
    fun t : ℝ => M.density t / (1 - cdf M.typeLaw t)
  let excess :=
    fun t : ℝ => (t - M.lower) * h t
  have hvalue0 : 0 ≤ value :=
    M.lower_pos.le.trans hvalue.1
  have hhcont : ContinuousOn h (Icc 0 value) := by
    dsimp [h]
    refine
      M.continuous_density.continuousOn.div
        (continuousOn_const.sub M.continuous_cdf.continuousOn) ?_
    intro t ht
    exact
      (M.survival_pos_of_lt_upper
        (ht.2.trans_lt hvalue.2)).ne'
  have hcandcont :
      ContinuousOn
        (fun t =>
          t * M.density t / (1 - cdf M.typeLaw t))
        (Icc 0 value) := by
    exact
      (continuousOn_id.mul M.continuous_density.continuousOn).div
        (continuousOn_const.sub M.continuous_cdf.continuousOn)
        (fun t ht =>
          (M.survival_pos_of_lt_upper
            (ht.2.trans_lt hvalue.2)).ne')
  have hhcontU : ContinuousOn h (uIcc 0 value) := by
    simpa [uIcc_of_le hvalue0] using hhcont
  have hcandcontU :
      ContinuousOn
        (fun t =>
          t * M.density t / (1 - cdf M.typeLaw t))
        (uIcc 0 value) := by
    simpa [uIcc_of_le hvalue0] using hcandcont
  have hdiff :
      M.candidate value -
          M.lower * M.cumulativeHazard value =
        ∫ t in 0..value, excess t := by
    rw [M.candidate_eq_raw hvalue.2, candidateRaw,
      ← M.integral_hazardDensity hvalue0 hvalue.2,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        hcandcontU.intervalIntegrable
        (hhcontU.const_mul M.lower).intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [excess, h]
    ring
  rw [← sub_nonneg, hdiff]
  apply intervalIntegral.integral_nonneg hvalue0
  intro t ht
  have hsurvival :
      0 < 1 - cdf M.typeLaw t :=
    M.survival_pos_of_lt_upper (ht.2.trans_lt hvalue.2)
  have hh_nonneg : 0 ≤ h t :=
    div_nonneg (M.density_nonnegative t) hsurvival.le
  rcases le_total M.lower t with hlt | htl
  · exact mul_nonneg (sub_nonneg.mpr hlt) hh_nonneg
  · have hdensity : M.density t = 0 := by
      apply M.density_zero_off_support
      exact fun hs => (not_lt_of_ge htl) hs.1
    dsimp [excess, h]
    rw [hdensity]
    simp

theorem candidate_surjOn_nonnegative (M : CompactDensityModel) :
    SurjOn M.candidate (Ico M.lower M.upper) (Ici 0) := by
  intro ownTime hownTime
  let q : unitInterval :=
    ⟨1 - Real.exp (-ownTime / M.lower), by
      constructor
      · have hexp : Real.exp (-ownTime / M.lower) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr
            (by
              simpa [neg_div] using
                (neg_nonpos.mpr
                  (div_nonneg hownTime M.lower_pos.le)))
        linarith
      · linarith [Real.exp_pos (-ownTime / M.lower)]⟩
  let a := M.typeQuantile q
  have ha_lower : M.lower ≤ a :=
    (M.typeQuantile_mem q).1
  have hq_lt : (q : ℝ) < 1 := by
    dsimp [q]
    linarith [Real.exp_pos (-ownTime / M.lower)]
  have ha_upper : a < M.upper := by
    by_contra h
    have haupper : M.upper ≤ a := le_of_not_gt h
    have haeq : a = M.upper :=
      le_antisymm (M.typeQuantile_mem q).2 haupper
    have hcdf :
        cdf M.typeLaw a = (q : ℝ) := by
      simp [a]
    rw [haeq, M.cdf_upper] at hcdf
    linarith
  have hhazard :
      M.cumulativeHazard a = ownTime / M.lower := by
    rw [cumulativeHazard, M.cdf_typeQuantile q]
    dsimp [q]
    rw [show 1 - (1 - Real.exp (-ownTime / M.lower)) =
        Real.exp (-ownTime / M.lower) by ring,
      Real.log_exp]
    ring
  have hcandidate_ge :
      ownTime ≤ M.candidate a := by
    calc
      ownTime = M.lower * M.cumulativeHazard a := by
        rw [hhazard]
        field_simp [M.lower_pos.ne']
      _ ≤ M.candidate a :=
        M.lower_mul_cumulativeHazard_le_candidate
          ⟨ha_lower, ha_upper⟩
  have himage :
      Icc (M.candidate M.lower) (M.candidate a) ⊆
        M.candidate '' Icc M.lower a :=
    intermediate_value_Icc (ha_lower)
      (M.continuousOn_candidate_below_upper.mono
        (fun x hx => hx.2.trans_lt ha_upper))
  obtain ⟨cutoff, hcutoff, hcutoff_eq⟩ :=
    himage ⟨by simpa [M.candidate_lower] using hownTime,
      hcandidate_ge⟩
  exact
    ⟨cutoff, ⟨hcutoff.1, hcutoff.2.trans_lt ha_upper⟩,
      hcutoff_eq⟩

theorem density_integrable (M : CompactDensityModel) :
    Integrable M.density := by
  have hlintegral :
      ∫⁻ x, ENNReal.ofReal (M.density x) = 1 := by
    have hprob := measure_univ (μ := M.typeLaw)
    rw [M.typeLaw_eq_withDensity,
      withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hprob
    simpa using hprob
  refine
    ⟨M.continuous_density.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have h :
      (fun x => ENNReal.ofReal ‖M.density x‖) =
        (fun x => ENNReal.ofReal (M.density x)) := by
    funext x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (M.density_nonnegative x)]
  rw [h, hlintegral]
  simp

theorem integral_density (M : CompactDensityModel) :
    ∫ x, M.density x = 1 := by
  have hlintegral :
      ∫⁻ x, ENNReal.ofReal (M.density x) = 1 := by
    have hprob := measure_univ (μ := M.typeLaw)
    rw [M.typeLaw_eq_withDensity,
      withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hprob
    simpa using hprob
  apply ENNReal.ofReal_eq_one.mp
  rw [ofReal_integral_eq_lintegral_ofReal M.density_integrable
    (ae_of_all _ M.density_nonnegative)]
  exact hlintegral

theorem integral_density_Iic (M : CompactDensityModel) {x : ℝ}
    (hx : x ∈ Icc M.lower M.upper) :
    ∫ t in Iic x, M.density t = cdf M.typeLaw x := by
  have hinterval :
      (∫ t in M.lower..x, M.density t) =
        cdf M.typeLaw x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      M.continuous_cdf.continuousOn
      (fun t _ => M.hasDerivAt_cdf t)
      (M.continuous_density.intervalIntegrable M.lower x),
      M.cdf_lower, sub_zero]
  have hbelow :
      (∫ t in Iic M.lower, M.density t) = 0 := by
    have hzero :
        (fun t => M.density t) =ᵐ[volume.restrict (Iic M.lower)]
          (fun _ => 0) := by
      have hne :
          ∀ᵐ t : ℝ ∂volume, t ≠ M.lower := by
        rw [ae_iff]
        simpa only [not_ne_iff, setOf_eq_eq_singleton] using
          (measure_singleton (μ := volume) M.lower)
      change
        ∀ᵐ t ∂volume.restrict (Iic M.lower),
          M.density t = 0
      rw [ae_restrict_iff' measurableSet_Iic]
      filter_upwards [hne] with t ht htle
      exact M.density_zero_off_support t
        (fun hs => ht (le_antisymm htle hs.1.le))
    rw [integral_congr_ae hzero]
    simp
  calc
    (∫ t in Iic x, M.density t) =
        (∫ t in Iic M.lower, M.density t) +
          ∫ t in Ioc M.lower x, M.density t := by
      rw [← Iic_union_Ioc_eq_Iic hx.1,
        setIntegral_union (Iic_disjoint_Ioc le_rfl)
          measurableSet_Ioc
          M.density_integrable.integrableOn
          M.density_integrable.integrableOn]
    _ = ∫ t in M.lower..x, M.density t := by
      rw [hbelow, zero_add, intervalIntegral.integral_of_le hx.1]
    _ = cdf M.typeLaw x := hinterval

theorem integral_density_Ioi (M : CompactDensityModel) {x : ℝ}
    (hx : x ∈ Icc M.lower M.upper) :
    ∫ t in Ioi x, M.density t =
      1 - cdf M.typeLaw x := by
  have hsplit :=
    integral_add_compl (s := Iic x) measurableSet_Iic
      M.density_integrable
  rw [compl_Iic, M.integral_density_Iic hx,
    M.integral_density] at hsplit
  linarith

theorem typeIntegral_eq_density (M : CompactDensityModel)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂M.typeLaw =
      ∫ x, M.density x * f x := by
  rw [M.typeLaw_eq_withDensity]
  rw [integral_withDensity_eq_integral_toReal_smul
    M.continuous_density.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [smul_eq_mul, M.density_nonnegative x]

theorem typeIntegrable_iff_density (M : CompactDensityModel)
    (f : ℝ → ℝ) :
    Integrable f M.typeLaw ↔
      Integrable (fun x => M.density x * f x) := by
  rw [M.typeLaw_eq_withDensity]
  rw [integrable_withDensity_iff
    M.continuous_density.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [] with x
  simp [M.density_nonnegative x]
  ring

theorem ae_mem_Ioo (M : CompactDensityModel) :
    ∀ᵐ x ∂M.typeLaw, x ∈ Ioo M.lower M.upper := by
  rw [ae_iff]
  change M.typeLaw ((Ioo M.lower M.upper)ᶜ) = 0
  rw [M.typeLaw_eq_withDensity,
    withDensity_apply _ measurableSet_Ioo.compl]
  rw [lintegral_eq_zero_iff
    M.continuous_density.measurable.ennreal_ofReal]
  change
    ∀ᵐ x ∂volume.restrict (Ioo M.lower M.upper)ᶜ,
      ENNReal.ofReal (M.density x) = 0
  rw [ae_restrict_iff' measurableSet_Ioo.compl]
  filter_upwards [] with x hx
  rw [M.density_zero_off_support x hx]
  simp

noncomputable def interimExpectedPayoff
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (value ownTime : ℝ) : ℝ :=
  ∫ opponentValue,
    payoff value ownTime (strategy opponentValue) ∂M.typeLaw

noncomputable def cutoffExpectedPayoff
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (value cutoff : ℝ) : ℝ :=
  (∫ t in M.lower..cutoff,
      (value - strategy t) * M.density t) -
    strategy cutoff * (1 - cdf M.typeLaw cutoff)

theorem payoff_candidate_integrable (M : CompactDensityModel)
    {value ownTime : ℝ} (hvalue : 0 ≤ value)
    (hownTime : 0 ≤ ownTime) :
    Integrable
      (fun opponentValue =>
        payoff value ownTime (M.candidate opponentValue))
      M.typeLaw := by
  have hmeasurable :
      Measurable
        (fun opponentValue =>
          payoff value ownTime (M.candidate opponentValue)) := by
    unfold payoff
    exact Measurable.ite
      (measurableSet_lt M.measurable_candidate measurable_const)
      (measurable_const.sub M.measurable_candidate)
      measurable_const
  apply Integrable.of_bound
    hmeasurable.aestronglyMeasurable (value + ownTime)
  filter_upwards [M.ae_mem_Ioo] with opponentValue hopponent
  have haction :
      0 ≤ M.candidate opponentValue :=
    M.candidate_nonnegative ⟨hopponent.1.le, hopponent.2⟩
  unfold payoff
  split_ifs with hwin
  · rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg hownTime]
    linarith

theorem densityWeightedCandidatePayoff_ae
    (M : CompactDensityModel) (value cutoff : ℝ)
    (hcutoff : cutoff ∈ Ico M.lower M.upper) :
    (fun t =>
      M.density t *
        payoff value (M.candidate cutoff) (M.candidate t)) =ᵐ[volume]
      (fun t =>
        (Ioc M.lower cutoff).indicator
            (fun t =>
              (value - M.candidate t) * M.density t) t +
          (Ioi cutoff).indicator
            (fun t =>
              -M.candidate cutoff * M.density t) t) := by
  have hnecutoff :
      ∀ᵐ t : ℝ ∂volume, t ≠ cutoff := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) cutoff)
  filter_upwards [hnecutoff] with t htcutoff
  by_cases htlow : t ≤ M.lower
  · have hdensity :
        M.density t = 0 :=
      M.density_zero_off_support t
        (fun ht => (not_lt_of_ge htlow) ht.1)
    have hwin : t ∉ Ioc M.lower cutoff :=
      fun ht => (not_lt_of_ge htlow) ht.1
    have hlose : t ∉ Ioi cutoff :=
      fun ht => (not_lt_of_ge (htlow.trans hcutoff.1)) ht
    simp [hdensity, hwin, hlose]
  · have ht_lower : M.lower < t := lt_of_not_ge htlow
    rcases lt_or_gt_of_ne htcutoff with htc | hct
    · have ht_upper : t < M.upper :=
        htc.trans hcutoff.2
      have hwin : t ∈ Ioc M.lower cutoff :=
        ⟨ht_lower, htc.le⟩
      have hlose : t ∉ Ioi cutoff :=
        fun h => lt_asymm h htc
      rw [Set.indicator_of_mem hwin,
        Set.indicator_of_notMem hlose]
      rw [payoff, if_pos
        (M.strictMonoOn_candidate
          ⟨ht_lower.le, ht_upper⟩ hcutoff htc)]
      ring
    · have hwin : t ∉ Ioc M.lower cutoff :=
        fun h => (not_lt_of_ge h.2) hct
      have hlose : t ∈ Ioi cutoff := hct
      rw [Set.indicator_of_notMem hwin,
        Set.indicator_of_mem hlose]
      by_cases htupper : t < M.upper
      · rw [payoff, if_neg
          (not_lt_of_ge
            (M.strictMonoOn_candidate hcutoff
              ⟨ht_lower.le, htupper⟩ hct).le)]
        ring
      · have hdensity :
          M.density t = 0 :=
        M.density_zero_off_support t
          (fun ht => htupper ht.2)
        simp [hdensity]

theorem interimExpectedPayoff_eq_cutoff
    (M : CompactDensityModel) (value cutoff : ℝ)
    (hcutoff : cutoff ∈ Ico M.lower M.upper) :
    M.interimExpectedPayoff M.candidate value
        (M.candidate cutoff) =
      M.cutoffExpectedPayoff M.candidate value cutoff := by
  unfold interimExpectedPayoff
  rw [M.typeIntegral_eq_density]
  rw [integral_congr_ae
    (M.densityWeightedCandidatePayoff_ae value cutoff hcutoff)]
  let win :=
    fun t : ℝ =>
      (value - M.candidate t) * M.density t
  let lose :=
    fun t : ℝ =>
      -M.candidate cutoff * M.density t
  change
    (∫ t,
      (Ioc M.lower cutoff).indicator win t +
        (Ioi cutoff).indicator lose t) =
      M.cutoffExpectedPayoff M.candidate value cutoff
  have hwin : IntegrableOn win (Ioc M.lower cutoff) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      hcutoff.1]
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hcutoff.1, win] using
      (continuousOn_const.sub
        (M.continuousOn_candidate_below_upper.mono
          (fun t ht => ht.2.trans_lt hcutoff.2))).mul
        M.continuous_density.continuousOn
  have hlose : IntegrableOn lose (Ioi cutoff) :=
    (M.density_integrable.const_mul
      (-M.candidate cutoff)).integrableOn
  rw [integral_add
    (hwin.integrable_indicator measurableSet_Ioc)
    (hlose.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioi,
    ← intervalIntegral.integral_of_le hcutoff.1]
  have hlose_eq :
      (∫ t in Ioi cutoff, lose t) =
        -M.candidate cutoff *
          (1 - cdf M.typeLaw cutoff) := by
    rw [show
      (∫ t in Ioi cutoff, lose t) =
        -M.candidate cutoff *
          ∫ t in Ioi cutoff, M.density t by
      rw [← integral_const_mul]]
    rw [M.integral_density_Ioi
      ⟨hcutoff.1, hcutoff.2.le⟩]
  rw [hlose_eq]
  unfold cutoffExpectedPayoff
  dsimp [win]
  ring

/-- Actual a.e. Bayesian best response against a symmetric pure strategy. -/
def IsSymmetricBayesianEquilibrium
    (M : CompactDensityModel) (strategy : ℝ → ℝ) : Prop :=
  Measurable strategy ∧
    ∀ᵐ value ∂M.typeLaw,
      value ∈ Ioo M.lower M.upper ∧
        ∀ ownTime, 0 ≤ ownTime →
          Integrable
            (fun opponentValue =>
              payoff value ownTime (strategy opponentValue))
            M.typeLaw ∧
          (∫ opponentValue,
              payoff value ownTime (strategy opponentValue)
                ∂M.typeLaw) ≤
            ∫ opponentValue,
              payoff value (strategy value)
                (strategy opponentValue) ∂M.typeLaw

theorem densityWeightedStrategyPayoff_ae
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (hstrict : StrictMonoOn strategy (Ico M.lower M.upper))
    (value cutoff : ℝ)
    (hcutoff : cutoff ∈ Ico M.lower M.upper) :
    (fun t =>
      M.density t *
        payoff value (strategy cutoff) (strategy t)) =ᵐ[volume]
      (fun t =>
        (Ioc M.lower cutoff).indicator
            (fun t => (value - strategy t) * M.density t) t +
          (Ioi cutoff).indicator
            (fun t => -strategy cutoff * M.density t) t) := by
  have hnecutoff :
      ∀ᵐ t : ℝ ∂volume, t ≠ cutoff := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) cutoff)
  filter_upwards [hnecutoff] with t htcutoff
  by_cases htlow : t ≤ M.lower
  · have hdensity :
        M.density t = 0 :=
      M.density_zero_off_support t
        (fun ht => (not_lt_of_ge htlow) ht.1)
    have hwin : t ∉ Ioc M.lower cutoff :=
      fun ht => (not_lt_of_ge htlow) ht.1
    have hlose : t ∉ Ioi cutoff :=
      fun ht => (not_lt_of_ge (htlow.trans hcutoff.1)) ht
    simp [hdensity, hwin, hlose]
  · have ht_lower : M.lower < t := lt_of_not_ge htlow
    rcases lt_or_gt_of_ne htcutoff with htc | hct
    · have ht_upper : t < M.upper :=
        htc.trans hcutoff.2
      have hwin : t ∈ Ioc M.lower cutoff :=
        ⟨ht_lower, htc.le⟩
      have hlose : t ∉ Ioi cutoff :=
        fun h => lt_asymm h htc
      rw [Set.indicator_of_mem hwin,
        Set.indicator_of_notMem hlose]
      rw [payoff, if_pos
        (hstrict ⟨ht_lower.le, ht_upper⟩ hcutoff htc)]
      ring
    · have hwin : t ∉ Ioc M.lower cutoff :=
        fun h => (not_lt_of_ge h.2) hct
      have hlose : t ∈ Ioi cutoff := hct
      rw [Set.indicator_of_notMem hwin,
        Set.indicator_of_mem hlose]
      by_cases htupper : t < M.upper
      · rw [payoff, if_neg
          (not_lt_of_ge
            (hstrict hcutoff
              ⟨ht_lower.le, htupper⟩ hct).le)]
        ring
      · have hdensity :
          M.density t = 0 :=
        M.density_zero_off_support t
          (fun ht => htupper ht.2)
        simp [hdensity]

theorem interimExpectedPayoff_eq_cutoff_of_strictMono
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (hcontinuous : ContinuousOn strategy (Ico M.lower M.upper))
    (hstrict : StrictMonoOn strategy (Ico M.lower M.upper))
    (value cutoff : ℝ)
    (hcutoff : cutoff ∈ Ico M.lower M.upper) :
    M.interimExpectedPayoff strategy value (strategy cutoff) =
      M.cutoffExpectedPayoff strategy value cutoff := by
  unfold interimExpectedPayoff
  rw [M.typeIntegral_eq_density]
  rw [integral_congr_ae
    (M.densityWeightedStrategyPayoff_ae
      strategy hstrict value cutoff hcutoff)]
  let win :=
    fun t : ℝ => (value - strategy t) * M.density t
  let lose :=
    fun t : ℝ => -strategy cutoff * M.density t
  change
    (∫ t,
      (Ioc M.lower cutoff).indicator win t +
        (Ioi cutoff).indicator lose t) =
      M.cutoffExpectedPayoff strategy value cutoff
  have hwin : IntegrableOn win (Ioc M.lower cutoff) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      hcutoff.1]
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hcutoff.1, win] using
      (continuousOn_const.sub
        (hcontinuous.mono
          (fun t ht =>
            ⟨ht.1, ht.2.trans_lt hcutoff.2⟩))).mul
        M.continuous_density.continuousOn
  have hlose : IntegrableOn lose (Ioi cutoff) :=
    (M.density_integrable.const_mul
      (-strategy cutoff)).integrableOn
  rw [integral_add
    (hwin.integrable_indicator measurableSet_Ioc)
    (hlose.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioi,
    ← intervalIntegral.integral_of_le hcutoff.1]
  have hlose_eq :
      (∫ t in Ioi cutoff, lose t) =
        -strategy cutoff *
          (1 - cdf M.typeLaw cutoff) := by
    rw [show
      (∫ t in Ioi cutoff, lose t) =
        -strategy cutoff *
          ∫ t in Ioi cutoff, M.density t by
      rw [← integral_const_mul]]
    rw [M.integral_density_Ioi
      ⟨hcutoff.1, hcutoff.2.le⟩]
  rw [hlose_eq]
  unfold cutoffExpectedPayoff
  dsimp [win]
  ring

/-- Regular pure symmetric equilibria used for the source's uniqueness claim
on compact type supports. -/
structure IsRegularSymmetricBayesianEquilibrium
    (M : CompactDensityModel) (strategy : ℝ → ℝ) : Prop where
  equilibrium : M.IsSymmetricBayesianEquilibrium strategy
  map_lower : strategy M.lower = 0
  nonnegative :
    ∀ x ∈ Ico M.lower M.upper, 0 ≤ strategy x
  strictMonoOn :
    StrictMonoOn strategy (Ico M.lower M.upper)
  continuousOn :
    ContinuousOn strategy (Ico M.lower M.upper)
  differentiableAt :
    ∀ x ∈ Ioo M.lower M.upper,
      DifferentiableAt ℝ strategy x

theorem continuousOn_candidateCutoffExpectedPayoff
    (M : CompactDensityModel) (value : ℝ) {b : ℝ}
    (hb : b ∈ Ico M.lower M.upper) :
    ContinuousOn
      (fun x =>
        M.cutoffExpectedPayoff M.candidate value x)
      (Icc M.lower b) := by
  let winIntegrand :=
    fun t =>
      (value - M.candidate t) * M.density t
  have hstrategy :
      ContinuousOn M.candidate (Icc M.lower b) :=
    M.continuousOn_candidate_below_upper.mono
      (fun x hx => hx.2.trans_lt hb.2)
  have hwin :
      ContinuousOn winIntegrand (Icc M.lower b) :=
    (continuousOn_const.sub hstrategy).mul
      M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume M.lower b := by
    have hwinU : ContinuousOn winIntegrand (uIcc M.lower b) := by
      simpa [uIcc_of_le hb.1] using hwin
    exact hwinU.intervalIntegrable
  have hprimitive :
      ContinuousOn
        (fun x => ∫ t in M.lower..x, winIntegrand t)
        (Icc M.lower b) := by
    simpa [uIcc_of_le hb.1] using
      intervalIntegral.continuousOn_primitive_interval'
        hwin_integrable left_mem_uIcc
  unfold cutoffExpectedPayoff
  exact hprimitive.sub
    (hstrategy.mul
      (continuousOn_const.sub
        M.continuous_cdf.continuousOn))

theorem candidateCutoffExpectedPayoff_hasDerivAt
    (M : CompactDensityModel) {value cutoff : ℝ}
    (hcutoff : cutoff ∈ Ioo M.lower M.upper) :
    HasDerivAt
      (fun x =>
        M.cutoffExpectedPayoff M.candidate value x)
      ((value - cutoff) * M.density cutoff) cutoff := by
  let winIntegrand :=
    fun t =>
      (value - M.candidate t) * M.density t
  have hstrategy :
      HasDerivAt M.candidate
        (cutoff * M.density cutoff /
          (1 - cdf M.typeLaw cutoff)) cutoff :=
    M.candidate_hasDerivAt hcutoff.2
  have hstrategy_continuousOn :
      ContinuousOn M.candidate (Icc M.lower cutoff) :=
    M.continuousOn_candidate_below_upper.mono
      (fun x hx => hx.2.trans_lt hcutoff.2)
  have hwin_continuousOn :
      ContinuousOn winIntegrand (Icc M.lower cutoff) :=
    (continuousOn_const.sub hstrategy_continuousOn).mul
      M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume M.lower cutoff := by
    have hwinU :
        ContinuousOn winIntegrand (uIcc M.lower cutoff) := by
      simpa [uIcc_of_le hcutoff.1.le] using hwin_continuousOn
    exact hwinU.intervalIntegrable
  have hwin_continuousAt :
      ContinuousAt winIntegrand cutoff :=
    (continuousAt_const.sub hstrategy.continuousAt).mul
      M.continuous_density.continuousAt
  have hfirst :
      HasDerivAt
        (fun x => ∫ t in M.lower..x, winIntegrand t)
        (winIntegrand cutoff) cutoff :=
    intervalIntegral.integral_hasDerivAt_right
      hwin_integrable
      (((M.measurable_candidate.const_sub value).mul
        M.continuous_density.measurable).aestronglyMeasurable
        |>.stronglyMeasurableAtFilter)
      hwin_continuousAt
  have hsurvival :
      HasDerivAt
        (fun x => 1 - cdf M.typeLaw x)
        (-M.density cutoff) cutoff := by
    simpa only [zero_sub] using
      (hasDerivAt_const cutoff (1 : ℝ)).sub
        (M.hasDerivAt_cdf cutoff)
  have hsecond :
      HasDerivAt
        (fun x =>
          M.candidate x * (1 - cdf M.typeLaw x))
        ((cutoff * M.density cutoff /
            (1 - cdf M.typeLaw cutoff)) *
              (1 - cdf M.typeLaw cutoff) +
          M.candidate cutoff * (-M.density cutoff))
        cutoff :=
    hstrategy.mul hsurvival
  unfold cutoffExpectedPayoff
  convert hfirst.sub hsecond using 1
  field_simp
    [(M.survival_pos_of_lt_upper hcutoff.2).ne']
  ring

theorem candidateCutoffExpectedPayoff_le
    (M : CompactDensityModel) {value cutoff : ℝ}
    (hvalue : value ∈ Ioo M.lower M.upper)
    (hcutoff : cutoff ∈ Ico M.lower M.upper) :
    M.cutoffExpectedPayoff M.candidate value cutoff ≤
      M.cutoffExpectedPayoff M.candidate value value := by
  let derivative :=
    fun t => (value - t) * M.density t
  have hderivative_continuous : Continuous derivative :=
    (continuous_const.sub continuous_id).mul
      M.continuous_density
  rcases le_total cutoff value with hcv | hvc
  · have hFTC :
        (∫ t in cutoff..value, derivative t) =
          M.cutoffExpectedPayoff M.candidate value value -
            M.cutoffExpectedPayoff M.candidate value cutoff := by
      refine
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hcv ?_ ?_ ?_
      · exact
          (M.continuousOn_candidateCutoffExpectedPayoff
            value ⟨hvalue.1.le, hvalue.2⟩).mono
              (Icc_subset_Icc_left hcutoff.1)
      · intro t ht
        exact
          M.candidateCutoffExpectedPayoff_hasDerivAt
            ⟨hcutoff.1.trans_lt ht.1, ht.2.trans hvalue.2⟩
      · exact hderivative_continuous.intervalIntegrable _ _
    have hnonneg :
        0 ≤ ∫ t in cutoff..value, derivative t := by
      apply intervalIntegral.integral_nonneg hcv
      intro t ht
      exact mul_nonneg
        (sub_nonneg.mpr ht.2)
        (M.density_nonnegative t)
    linarith
  · have hFTC :
        (∫ t in value..cutoff, derivative t) =
          M.cutoffExpectedPayoff M.candidate value cutoff -
            M.cutoffExpectedPayoff M.candidate value value := by
      refine
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hvc ?_ ?_ ?_
      · exact
          (M.continuousOn_candidateCutoffExpectedPayoff
            value hcutoff).mono
              (Icc_subset_Icc_left hvalue.1.le)
      · intro t ht
        exact
          M.candidateCutoffExpectedPayoff_hasDerivAt
            ⟨hvalue.1.trans ht.1, ht.2.trans hcutoff.2⟩
      · exact hderivative_continuous.intervalIntegrable _ _
    have hnonpos :
        (∫ t in value..cutoff, derivative t) ≤ 0 := by
      have hzero :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
            volume value cutoff :=
        intervalIntegrable_const
      simpa using
        intervalIntegral.integral_mono_on hvc
          (hderivative_continuous.intervalIntegrable _ _)
          hzero
          (fun t ht =>
            mul_nonpos_of_nonpos_of_nonneg
              (sub_nonpos.mpr ht.1)
              (M.density_nonnegative t))
    linarith

theorem candidate_isSymmetricBayesianEquilibrium
    (M : CompactDensityModel) :
    M.IsSymmetricBayesianEquilibrium M.candidate := by
  refine ⟨M.measurable_candidate, ?_⟩
  filter_upwards [M.ae_mem_Ioo] with value hvalue
  refine ⟨hvalue, ?_⟩
  intro ownTime hownTime
  refine
    ⟨M.payoff_candidate_integrable
      (M.lower_pos.le.trans hvalue.1.le) hownTime, ?_⟩
  obtain ⟨cutoff, hcutoff, hcutoff_eq⟩ :=
    M.candidate_surjOn_nonnegative hownTime
  rw [← hcutoff_eq]
  rw [show
      (∫ opponentValue,
        payoff value (M.candidate cutoff)
          (M.candidate opponentValue) ∂M.typeLaw) =
        M.interimExpectedPayoff M.candidate value
          (M.candidate cutoff) by rfl]
  rw [M.interimExpectedPayoff_eq_cutoff
    value cutoff hcutoff]
  rw [show
      (∫ opponentValue,
        payoff value (M.candidate value)
          (M.candidate opponentValue) ∂M.typeLaw) =
        M.interimExpectedPayoff M.candidate value
          (M.candidate value) by rfl]
  rw [M.interimExpectedPayoff_eq_cutoff
    value value ⟨hvalue.1.le, hvalue.2⟩]
  exact M.candidateCutoffExpectedPayoff_le hvalue hcutoff

theorem candidate_isRegularSymmetricBayesianEquilibrium
    (M : CompactDensityModel) :
    M.IsRegularSymmetricBayesianEquilibrium M.candidate where
  equilibrium := M.candidate_isSymmetricBayesianEquilibrium
  map_lower := M.candidate_lower
  nonnegative := fun _ h =>
    M.candidate_nonnegative h
  strictMonoOn := M.strictMonoOn_candidate
  continuousOn :=
    M.continuousOn_candidate_below_upper.mono
      Ico_subset_Iio_self
  differentiableAt := fun _ h =>
    (M.candidate_hasDerivAt h.2).differentiableAt

private theorem absolutelyContinuousOnInterval_congr_of_eqOn
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlength => ?_⟩
  rw [show
      (∑ i ∈ Finset.range E.1,
          dist (g (E.2 i).1) (g (E.2 i).2)) =
        ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2) by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]]
  exact hmain E hE hlength

/-- The compact candidate satisfies the local absolute-continuity hypothesis
used in the regular uniqueness theorem. -/
theorem candidate_absolutelyContinuousOnInterval
    (M : CompactDensityModel) {b : ℝ}
    (hb : b ∈ Ico M.lower M.upper) :
    AbsolutelyContinuousOnInterval M.candidate M.lower b := by
  let integrand :=
    fun t : ℝ =>
      t * M.density t / (1 - cdf M.typeLaw t)
  have hintegrable :
      IntervalIntegrable integrand volume M.lower b := by
    have hcontinuous :
        ContinuousOn integrand (uIcc M.lower b) := by
      rw [uIcc_of_le hb.1]
      exact
        (M.continuousOn_candidateIntegrand_below_upper hb.2).mono
          (Icc_subset_Icc_left M.lower_pos.le)
    exact hcontinuous.intervalIntegrable
  have hprimitive :
      AbsolutelyContinuousOnInterval
        (fun x => ∫ t in M.lower..x, integrand t)
        M.lower b :=
    hintegrable.absolutelyContinuousOnInterval_intervalIntegral
      (c := M.lower) (by simp)
  apply absolutelyContinuousOnInterval_congr_of_eqOn hprimitive
  intro x hx
  rw [uIcc_of_le hb.1] at hx
  have hintegrable_lower :
      IntervalIntegrable integrand volume 0 M.lower := by
    have hcontinuous :
        ContinuousOn integrand (uIcc 0 M.lower) := by
      simpa [integrand, uIcc_of_le M.lower_pos.le] using
        M.continuousOn_candidateIntegrand_below_upper
          M.lower_lt_upper
    exact hcontinuous.intervalIntegrable
  have hintegrable_tail :
      IntervalIntegrable integrand volume M.lower x :=
    hintegrable.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le hb.1]
      exact Icc_subset_Icc_right hx.2)
  have hzero :
      (∫ t in 0..M.lower, integrand t) = 0 := by
    simpa [integrand, candidate, candidateRaw, M.lower_lt_upper] using
      M.candidate_lower
  rw [M.candidate_eq_raw (hx.2.trans_lt hb.2), candidateRaw,
    ← intervalIntegral.integral_add_adjacent_intervals
      hintegrable_lower hintegrable_tail,
    hzero, zero_add]

/-- Derivative of the exact cutoff payoff for an arbitrary regular strategy
on the compact type support. -/
theorem cutoffExpectedPayoff_hasDerivAt
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (hcontinuous :
      ContinuousOn strategy (Ico M.lower M.upper))
    (hmeasurable : Measurable strategy)
    {value cutoff d : ℝ}
    (hcutoff : cutoff ∈ Ioo M.lower M.upper)
    (hstrategy : HasDerivAt strategy d cutoff) :
    HasDerivAt
      (fun x => M.cutoffExpectedPayoff strategy value x)
      (value * M.density cutoff -
        d * (1 - cdf M.typeLaw cutoff)) cutoff := by
  let winIntegrand :=
    fun t => (value - strategy t) * M.density t
  have hwin_continuousOn :
      ContinuousOn winIntegrand (Icc M.lower cutoff) := by
    exact
      (continuousOn_const.sub
        (hcontinuous.mono fun x hx =>
          ⟨hx.1, hx.2.trans_lt hcutoff.2⟩)).mul
        M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume M.lower cutoff := by
    have hwinU :
        ContinuousOn winIntegrand (uIcc M.lower cutoff) := by
      simpa [uIcc_of_le hcutoff.1.le] using hwin_continuousOn
    exact hwinU.intervalIntegrable
  have hwin_continuousAt :
      ContinuousAt winIntegrand cutoff :=
    (continuousAt_const.sub hstrategy.continuousAt).mul
      M.continuous_density.continuousAt
  have hfirst :
      HasDerivAt
        (fun x => ∫ t in M.lower..x, winIntegrand t)
        (winIntegrand cutoff) cutoff :=
    intervalIntegral.integral_hasDerivAt_right
      hwin_integrable
      (MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
        (((measurable_const.sub hmeasurable).mul
          M.continuous_density.measurable).aestronglyMeasurable))
      hwin_continuousAt
  have hsurvival :
      HasDerivAt
        (fun x => 1 - cdf M.typeLaw x)
        (-M.density cutoff) cutoff := by
    simpa only [zero_sub] using
      (hasDerivAt_const cutoff (1 : ℝ)).sub
        (M.hasDerivAt_cdf cutoff)
  have hsecond :
      HasDerivAt
        (fun x =>
          strategy x * (1 - cdf M.typeLaw x))
        (d * (1 - cdf M.typeLaw cutoff) +
          strategy cutoff * (-M.density cutoff)) cutoff :=
    hstrategy.mul hsurvival
  unfold cutoffExpectedPayoff
  convert hfirst.sub hsecond using 1
  dsimp [winIntegrand]
  ring

theorem regularEquilibrium_deriv_eq_candidate_ae
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (R : M.IsRegularSymmetricBayesianEquilibrium strategy) :
    ∀ᵐ value ∂volume,
      value ∈ Ioo M.lower M.upper →
        deriv strategy value =
          value * M.density value /
            (1 - cdf M.typeLaw value) := by
  have hoptimal := R.equilibrium.2
  rw [M.typeLaw_eq_withDensity] at hoptimal
  have hweighted :=
    (ae_withDensity_iff
      M.continuous_density.measurable.ennreal_ofReal).mp hoptimal
  filter_upwards [hweighted] with value hvalue
  intro hvalue_mem
  have hdensity_ne :
      ENNReal.ofReal (M.density value) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr
      (M.density_pos value hvalue_mem)
  have hopt := (hvalue hdensity_ne).2
  have hstrategy :
      HasDerivAt strategy (deriv strategy value) value :=
    (R.differentiableAt value hvalue_mem).hasDerivAt
  have hcutoff_deriv :
      HasDerivAt
        (fun cutoff =>
          M.cutoffExpectedPayoff strategy value cutoff)
        (value * M.density value -
          deriv strategy value *
            (1 - cdf M.typeLaw value)) value :=
    M.cutoffExpectedPayoff_hasDerivAt strategy R.continuousOn
      R.equilibrium.1 (value := value) (cutoff := value)
      (d := deriv strategy value) hvalue_mem hstrategy
  have hlocalMax :
      IsLocalMax
        (fun cutoff =>
          M.cutoffExpectedPayoff strategy value cutoff)
        value := by
    filter_upwards
      [Ioo_mem_nhds hvalue_mem.1 hvalue_mem.2] with cutoff hcutoff
    have hcutoffIco :
        cutoff ∈ Ico M.lower M.upper :=
      ⟨hcutoff.1.le, hcutoff.2⟩
    have hvalueIco :
        value ∈ Ico M.lower M.upper :=
      ⟨hvalue_mem.1.le, hvalue_mem.2⟩
    have hactual :=
      (hopt (strategy cutoff)
        (R.nonnegative cutoff hcutoffIco)).2
    rw [← M.typeLaw_eq_withDensity] at hactual
    rw [show
        (∫ opponentValue,
          payoff value (strategy cutoff)
            (strategy opponentValue) ∂M.typeLaw) =
          M.interimExpectedPayoff strategy value
            (strategy cutoff) by rfl] at hactual
    rw [M.interimExpectedPayoff_eq_cutoff_of_strictMono
      strategy R.continuousOn R.strictMonoOn
      value cutoff hcutoffIco] at hactual
    rw [show
        (∫ opponentValue,
          payoff value (strategy value)
            (strategy opponentValue) ∂M.typeLaw) =
          M.interimExpectedPayoff strategy value
            (strategy value) by rfl] at hactual
    rw [M.interimExpectedPayoff_eq_cutoff_of_strictMono
      strategy R.continuousOn R.strictMonoOn
      value value hvalueIco] at hactual
    exact hactual
  have hzero :=
    hlocalMax.hasDerivAt_eq_zero hcutoff_deriv
  field_simp
    [(M.survival_pos_of_lt_upper hvalue_mem.2).ne']
  linarith

/-- Uniqueness of the compact-support pure symmetric equilibrium in the
explicit regularity class. -/
theorem regularEquilibrium_eq_candidate
    (M : CompactDensityModel) (strategy : ℝ → ℝ)
    (R : M.IsRegularSymmetricBayesianEquilibrium strategy)
    (habsolutelyContinuous :
      ∀ b, b ∈ Ico M.lower M.upper →
        AbsolutelyContinuousOnInterval
          strategy M.lower b) :
    ∀ x, x ∈ Ico M.lower M.upper →
      strategy x = M.candidate x := by
  have hderiv :=
    M.regularEquilibrium_deriv_eq_candidate_ae strategy R
  intro x hx
  have hderiv_interval :
      ∀ᵐ t ∂volume, t ∈ uIoc M.lower x →
        deriv strategy t =
          t * M.density t /
            (1 - cdf M.typeLaw t) := by
    filter_upwards [hderiv] with t ht
    intro htmem
    rw [uIoc_of_le hx.1] at htmem
    exact ht ⟨htmem.1, htmem.2.trans_lt hx.2⟩
  have hcandidate_integrable_lower :
      IntervalIntegrable
        (fun t =>
          t * M.density t /
            (1 - cdf M.typeLaw t))
        volume 0 M.lower := by
    have hcont :=
      M.continuousOn_candidateIntegrand_below_upper
        M.lower_lt_upper
    have hcontU :
        ContinuousOn
          (fun t =>
            t * M.density t /
              (1 - cdf M.typeLaw t))
          (uIcc 0 M.lower) := by
      simpa [uIcc_of_le M.lower_pos.le] using hcont
    exact hcontU.intervalIntegrable
  have hcandidate_integrable_tail :
      IntervalIntegrable
        (fun t =>
          t * M.density t /
            (1 - cdf M.typeLaw t))
        volume M.lower x := by
    have hcont :=
      M.continuousOn_candidateIntegrand_below_upper hx.2
    have hcontU :
        ContinuousOn
          (fun t =>
            t * M.density t /
              (1 - cdf M.typeLaw t))
          (uIcc M.lower x) := by
      rw [uIcc_of_le hx.1]
      exact hcont.mono
        (Icc_subset_Icc_left M.lower_pos.le)
    exact hcontU.intervalIntegrable
  calc
    strategy x =
        ∫ t in M.lower..x, deriv strategy t := by
      rw [(habsolutelyContinuous x hx).integral_deriv_eq_sub,
        R.map_lower, sub_zero]
    _ = ∫ t in M.lower..x,
        t * M.density t /
          (1 - cdf M.typeLaw t) :=
      intervalIntegral.integral_congr_ae hderiv_interval
    _ = M.candidate x := by
      rw [M.candidate_eq_raw hx.2,
        candidateRaw,
        ← intervalIntegral.integral_add_adjacent_intervals
          hcandidate_integrable_lower
          hcandidate_integrable_tail]
      have hzero :
          (∫ t in 0..M.lower,
            t * M.density t /
              (1 - cdf M.typeLaw t)) = 0 := by
        simpa [candidate, candidateRaw, M.lower_lt_upper] using
          M.candidate_lower
      rw [hzero, zero_add]

/-- The source's key shrinking-support estimate, derived from the density
support rather than assumed as a coupling certificate. -/
theorem dist_candidate_center_mul_hazard_le
    (M : CompactDensityModel) {v error value : ℝ}
    (hlower : M.lower = v - error)
    (hupper : M.upper = v + error)
    (hvalue : value ∈ Ico M.lower M.upper) :
    dist (M.candidate value) (v * M.cumulativeHazard value) ≤
      error * M.cumulativeHazard value := by
  let h :=
    fun t : ℝ => M.density t / (1 - cdf M.typeLaw t)
  let centered :=
    fun t : ℝ => (t - v) * h t
  have hvalue0 : 0 ≤ value :=
    M.lower_pos.le.trans hvalue.1
  have hhcont : ContinuousOn h (Icc 0 value) := by
    dsimp [h]
    refine
      M.continuous_density.continuousOn.div
        (continuousOn_const.sub M.continuous_cdf.continuousOn) ?_
    intro t ht
    exact
      (M.survival_pos_of_lt_upper
        (ht.2.trans_lt hvalue.2)).ne'
  have hcenteredcont : ContinuousOn centered (Icc 0 value) :=
    (continuousOn_id.sub continuousOn_const).mul hhcont
  have hcandcont :
      ContinuousOn
        (fun t =>
          t * M.density t / (1 - cdf M.typeLaw t))
        (Icc 0 value) := by
    exact
      (continuousOn_id.mul M.continuous_density.continuousOn).div
        (continuousOn_const.sub M.continuous_cdf.continuousOn)
        (fun t ht =>
          (M.survival_pos_of_lt_upper
            (ht.2.trans_lt hvalue.2)).ne')
  have hhcontU : ContinuousOn h (uIcc 0 value) := by
    simpa [uIcc_of_le hvalue0] using hhcont
  have hcandcontU :
      ContinuousOn
        (fun t =>
          t * M.density t / (1 - cdf M.typeLaw t))
        (uIcc 0 value) := by
    simpa [uIcc_of_le hvalue0] using hcandcont
  have hdiff :
      M.candidate value - v * M.cumulativeHazard value =
        ∫ t in 0..value, centered t := by
    rw [M.candidate_eq_raw hvalue.2, candidateRaw,
      ← M.integral_hazardDensity hvalue0 hvalue.2,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        hcandcontU.intervalIntegrable
        (hhcontU.const_mul v).intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [centered, h]
    ring
  rw [Real.dist_eq, hdiff]
  have hbound :
      ∀ᵐ t ∂volume, t ∈ Ioc 0 value →
        ‖centered t‖ ≤ error * h t := by
    filter_upwards [] with t ht
    have hsurvival :
        0 < 1 - cdf M.typeLaw t :=
      M.survival_pos_of_lt_upper (ht.2.trans_lt hvalue.2)
    have hh_nonneg : 0 ≤ h t :=
      div_nonneg (M.density_nonnegative t) hsurvival.le
    by_cases htsupport : t ∈ Ioo M.lower M.upper
    · have htv : |t - v| ≤ error := by
        rw [hlower, hupper] at htsupport
        exact abs_le.mpr
          ⟨by linarith [htsupport.1], by linarith [htsupport.2]⟩
      rw [show ‖centered t‖ = |t - v| * h t by
        simp [centered, Real.norm_eq_abs,
          abs_of_nonneg hh_nonneg]]
      exact mul_le_mul_of_nonneg_right htv hh_nonneg
    · have hhzero : h t = 0 := by
        simp [h, M.density_zero_off_support t htsupport]
      dsimp [centered]
      rw [hhzero]
      simp
  calc
    ‖∫ t in 0..value, centered t‖
        ≤ ∫ t in 0..value, error * h t :=
      intervalIntegral.norm_integral_le_of_norm_le hvalue0 hbound
        (hhcontU.const_mul error).intervalIntegrable
    _ = error * M.cumulativeHazard value := by
      rw [intervalIntegral.integral_const_mul,
        M.integral_hazardDensity hvalue0 hvalue.2]

end CompactDensityModel

/-- Quantile realization of an exponential concession time from `U[0,1]`.
The endpoint `u = 1` is immaterial because it is Lebesgue-null. -/
noncomputable def exponentialQuantile (v : ℝ) (u : unitInterval) : ℝ :=
  -v * Real.log (1 - (u : ℝ))

theorem measurable_exponentialQuantile (v : ℝ) :
    Measurable (exponentialQuantile v) := by
  unfold exponentialQuantile
  exact measurable_const.mul
    ((measurable_const.sub measurable_subtype_coe).log)

theorem exponentialQuantile_nonnegative {v : ℝ} (hv : 0 < v)
    (u : unitInterval) :
    0 ≤ exponentialQuantile v u := by
  unfold exponentialQuantile
  have hq0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.2.2
  have hq1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.2.1]
  have hlog := Real.log_nonpos hq0 hq1
  nlinarith

lemma exponentialQuantile_le_iff {v t : ℝ} (hv : 0 < v)
    {u : unitInterval} (hu : u ≠ 1) :
    exponentialQuantile v u ≤ t ↔
      (u : ℝ) ≤ 1 - Real.exp (-t / v) := by
  have hu_lt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (by
    intro h
    apply hu
    ext
    simpa using h)
  have hq : 0 < 1 - (u : ℝ) := sub_pos.mpr hu_lt
  unfold exponentialQuantile
  constructor
  · intro h
    have hlog : -t / v ≤ Real.log (1 - (u : ℝ)) := by
      rw [div_le_iff₀ hv]
      nlinarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hq] at hexp
    linarith
  · intro h
    have hexp :
        Real.exp (-t / v) ≤ 1 - (u : ℝ) := by
      linarith
    have hlog :
        -t / v ≤ Real.log (1 - (u : ℝ)) := by
      have := Real.log_le_log (Real.exp_pos _) hexp
      simpa using this
    rw [div_le_iff₀ hv] at hlog
    nlinarith

/-- The exponential quantile pushes the uniform law to `Q_v`. -/
theorem map_exponentialQuantile (v : ℝ) (hv : 0 < v) :
    volume.map (exponentialQuantile v) =
      (exponentialConcessionLaw v hv).measure := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_exponentialQuantile v) measurableSet_Iic]
  rcases lt_or_ge t 0 with ht | ht
  · have hempty :
        exponentialQuantile v ⁻¹' Iic t = ∅ := by
      ext u
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt (ht.trans_le (exponentialQuantile_nonnegative hv u))
    rw [hempty]
    rw [← ofReal_cdf (exponentialConcessionLaw v hv).measure t]
    simp [cdf_exponentialConcessionLaw v hv t, not_le.mpr ht]
  · let q : unitInterval :=
      ⟨1 - Real.exp (-t / v), by
        constructor
        · have hexp : Real.exp (-t / v) ≤ 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr
              (by
                simpa [neg_div] using
                  (neg_nonpos.mpr (div_nonneg ht hv.le)))
          linarith
        · linarith [Real.exp_pos (-t / v)]⟩
    have hne :
        ∀ᵐ u : unitInterval ∂volume, u ≠ 1 := by
      rw [ae_iff]
      simpa only [not_ne_iff, setOf_eq_eq_singleton] using
        (measure_singleton (μ := (volume : Measure unitInterval))
          (1 : unitInterval))
    have hpreimage :
        exponentialQuantile v ⁻¹' Iic t =ᵐ[volume] Iic q := by
      filter_upwards [hne] with u hu
      change (exponentialQuantile v u ≤ t) = (u ≤ q)
      apply propext
      simpa [q] using exponentialQuantile_le_iff hv hu
    rw [measure_congr hpreimage, unitInterval.volume_Iic]
    rw [← ofReal_cdf (exponentialConcessionLaw v hv).measure t]
    rw [cdf_exponentialConcessionLaw v hv t, if_pos ht]

structure CompactActionLawSequence (v : ℝ) where
  value_pos : 0 < v
  model : ℕ → CompactDensityModel
  error : ℕ → ℝ
  error_nonnegative : ∀ n, 0 ≤ error n
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  lower_eq : ∀ n, (model n).lower = v - error n
  upper_eq : ∀ n, (model n).upper = v + error n

namespace CompactActionLawSequence

noncomputable def actionLaw {v : ℝ}
    (S : CompactActionLawSequence v) (n : ℕ) : Measure ℝ :=
  (S.model n).typeLaw.map (S.model n).candidate

instance actionLaw_probability {v : ℝ}
    (S : CompactActionLawSequence v) (n : ℕ) :
    IsProbabilityMeasure (S.actionLaw n) :=
  Measure.isProbabilityMeasure_map
    (S.model n).measurable_candidate.aemeasurable

theorem actionLaw_eq_uniform_map {v : ℝ}
    (S : CompactActionLawSequence v) (n : ℕ) :
    S.actionLaw n =
      volume.map
        ((S.model n).candidate ∘
          (S.model n).typeQuantile) := by
  rw [actionLaw, ← (S.model n).map_typeQuantile,
    Measure.map_map
      (S.model n).measurable_candidate
      (S.model n).measurable_typeQuantile]

theorem candidate_quantile_dist_exponentialQuantile_le
    {v : ℝ} (S : CompactActionLawSequence v)
    (n : ℕ) (u : unitInterval) :
    dist
        ((S.model n).candidate
          ((S.model n).typeQuantile u))
        (exponentialQuantile v u) ≤
      S.error n * (-Real.log (1 - (u : ℝ))) := by
  by_cases hu : u = 1
  · subst u
    have hquantile :
        (S.model n).typeQuantile (1 : unitInterval) =
          (S.model n).upper := by
      apply (S.model n).strictMonoOn_cdf.injOn
      · exact (S.model n).typeQuantile_mem 1
      · exact
          ⟨(S.model n).lower_lt_upper.le, le_rfl⟩
      rw [(S.model n).cdf_typeQuantile,
        (S.model n).cdf_upper]
      rfl
    simp [CompactDensityModel.candidate, hquantile,
      exponentialQuantile]
  · have hu_lt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (by
      intro h
      apply hu
      ext
      simpa using h)
    let a := (S.model n).typeQuantile u
    have ha_lower :
        (S.model n).lower ≤ a :=
      ((S.model n).typeQuantile_mem u).1
    have ha_upper : a < (S.model n).upper := by
      by_contra h
      have haupper :
          (S.model n).upper ≤ a := le_of_not_gt h
      have haeq : a = (S.model n).upper :=
        le_antisymm
          ((S.model n).typeQuantile_mem u).2 haupper
      have hcdf :
          cdf (S.model n).typeLaw a = (u : ℝ) := by
        simp [a]
      rw [haeq, (S.model n).cdf_upper] at hcdf
      linarith
    have hdist :=
      (S.model n).dist_candidate_center_mul_hazard_le
        (S.lower_eq n) (S.upper_eq n)
        ⟨ha_lower, ha_upper⟩
    have hhazard :
        (S.model n).cumulativeHazard a =
          -Real.log (1 - (u : ℝ)) := by
      rw [CompactDensityModel.cumulativeHazard]
      simp [a]
    have hcenter :
        v * (S.model n).cumulativeHazard a =
          exponentialQuantile v u := by
      rw [hhazard]
      unfold exponentialQuantile
      ring
    rw [hcenter, hhazard] at hdist
    exact hdist

def ConvergesToExponentialLaw {v : ℝ}
    (S : CompactActionLawSequence v) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto
      (fun n => ∫ x, f x ∂S.actionLaw n)
      atTop
      (𝓝
        (∫ x, f x
          ∂(exponentialConcessionLaw v S.value_pos).measure))

theorem candidate_isEquilibrium {v : ℝ}
    (S : CompactActionLawSequence v) (n : ℕ) :
    (S.model n).IsSymmetricBayesianEquilibrium
      (S.model n).candidate :=
  (S.model n).candidate_isSymmetricBayesianEquilibrium

theorem convergesToExponentialLaw {v : ℝ}
    (S : CompactActionLawSequence v) :
    S.ConvergesToExponentialLaw := by
  intro f
  have hpointwise :
      ∀ u : unitInterval,
        Tendsto
          (fun n =>
            f ((S.model n).candidate
              ((S.model n).typeQuantile u)))
          atTop
          (𝓝 (f (exponentialQuantile v u))) := by
    intro u
    apply f.continuous.continuousAt.tendsto.comp
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      (Eventually.of_forall fun n =>
        S.candidate_quantile_dist_exponentialQuantile_le n u)
    simpa using
      S.error_tendsto_zero.mul_const
        (-Real.log (1 - (u : ℝ)))
  have hDCT :
      Tendsto
        (fun n =>
          ∫ u,
            f ((S.model n).candidate
              ((S.model n).typeQuantile u)))
        atTop
        (𝓝
          (∫ u, f (exponentialQuantile v u))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ : unitInterval => ‖f‖)
    · intro n
      exact
        (f.continuous.measurable.comp
          ((S.model n).measurable_candidate.comp
            (S.model n).measurable_typeQuantile)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with u
      exact f.norm_coe_le_norm _
    · exact ae_of_all _ hpointwise
  have hintegral_action (n : ℕ) :
      (∫ x, f x ∂S.actionLaw n) =
        ∫ u,
          f ((S.model n).candidate
            ((S.model n).typeQuantile u)) := by
    rw [S.actionLaw_eq_uniform_map n]
    exact integral_map
      (((S.model n).measurable_candidate.comp
        (S.model n).measurable_typeQuantile).aemeasurable)
      f.continuous.measurable.aestronglyMeasurable
  have hintegral_limit :
      (∫ x, f x
          ∂(exponentialConcessionLaw v S.value_pos).measure) =
        ∫ u, f (exponentialQuantile v u) := by
    rw [← map_exponentialQuantile v S.value_pos]
    exact integral_map
      (measurable_exponentialQuantile v).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simpa only [hintegral_action, hintegral_limit] using hDCT

end CompactActionLawSequence

end StrategicGame.WarOfAttrition
