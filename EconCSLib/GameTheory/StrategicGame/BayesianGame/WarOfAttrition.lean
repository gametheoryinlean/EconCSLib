/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.BayesianGame.Continuous
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Exponential

/-!
# Continuous Bayesian war of attrition

This module formalizes the continuous model and the first two analytic claims
in [MFoGT, Example 7.4.1]. Concession times and private values live in
`ℝ_{\ge 0}`, represented by nonnegative real numbers together with explicit
support conditions on their probability laws.

No expectation is used without an integrability statement. Results for
density models explicitly record positivity of the survival function on the
domain of division, differentiability of the cumulative distribution, and the
almost-everywhere nature of distributional conclusions. The companion module
`WarOfAttrition.CompactApproximation` proves the compact-support equilibrium
and weak-convergence claim in item 3.

## Main declarations

* `payoff` - the source's tie-losing payoff convention;
* `ConcessionLaw` - a probability law supported on nonnegative times;
* `exponentialConcessionLaw` and `cdf_exponentialConcessionLaw` - the law
  `Q_v(t) = 1 - exp(-t/v)` for `v > 0`;
* `isSymmetricEquilibrium_exponentialConcessionLaw` - equilibrium against all
  integrable probability-law deviations;
* `RegularFullSupportEquilibrium.exponential` and
  `RegularFullSupportEquilibrium.measure_eq_exponential` - a non-vacuous
  regular class and uniqueness in the complete-information case;
* `DensityModel.candidateStrategy` - the private-value formula
  `∫₀ᵃ t g(t)/(1-G(t)) dt`;
* `DensityModel.candidate_isRegularSymmetricEquilibrium` and
  `DensityModel.regularEquilibrium_eq_candidate` - actual-payoff equilibrium
  and uniqueness in an explicit regularity class;
* `WarOfAttrition.CompactApproximation` - companion module for item 3.

## References

* [MFoGT] Chapter 7, Example 7.4.1
* Bishop and Cannings, "A Generalized War of Attrition" (1978)
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace StrategicGame.WarOfAttrition

/-- Payoff to a player of value `value` who concedes at `ownTime` when the
opponent concedes at `opponentTime`. Ties are losses, as in
[MFoGT, Example 7.4.1]. -/
noncomputable def payoff (value ownTime opponentTime : ℝ) : ℝ :=
  if opponentTime < ownTime then value - opponentTime else -ownTime

/-- A probability law of concession times with full mass on `ℝ_{\ge 0}`. -/
structure ConcessionLaw where
  /-- Distribution of the concession time. -/
  measure : Measure ℝ
  /-- Total mass is one. -/
  [isProbabilityMeasure : IsProbabilityMeasure measure]
  /-- Negative concession times occur only on a null set. -/
  ae_nonnegative : ∀ᵐ t ∂measure, 0 ≤ t

attribute [instance] ConcessionLaw.isProbabilityMeasure

/-- Expected payoff of the pure concession time `ownTime` against `opponent`.
The companion predicate `PurePayoffIntegrable` records when this integral is a
genuine expectation rather than Lean's default value for a nonintegrable
function. -/
noncomputable def pureExpectedPayoff (value ownTime : ℝ)
    (opponent : ConcessionLaw) : ℝ :=
  ∫ opponentTime, payoff value ownTime opponentTime ∂opponent.measure

/-- Explicit integrability side condition for a pure deviation. -/
def PurePayoffIntegrable (value ownTime : ℝ)
    (opponent : ConcessionLaw) : Prop :=
  Integrable (payoff value ownTime) opponent.measure

/-- Ex-ante payoff when the player's concession time has law `own` and the
opponent's concession time independently has law `opponent`. -/
noncomputable def mixedExpectedPayoff (value : ℝ)
    (own opponent : ConcessionLaw) : ℝ :=
  ∫ ownTime, pureExpectedPayoff value ownTime opponent ∂own.measure

/-- The two iterated expectations defining a mixed payoff are genuinely
integrable. This is kept separate from `mixedExpectedPayoff` so equilibrium
statements cannot hide nonintegrability behind the totalized Bochner integral.
-/
def MixedPayoffIntegrable (value : ℝ)
    (own opponent : ConcessionLaw) : Prop :=
  (∀ᵐ ownTime ∂own.measure,
      PurePayoffIntegrable value ownTime opponent) ∧
    Integrable (fun ownTime => pureExpectedPayoff value ownTime opponent)
      own.measure

/-- A symmetric equilibrium law, quantified only over deviations for which the
payoff is a genuine iterated expectation. -/
def IsSymmetricEquilibrium (value : ℝ) (equilibrium : ConcessionLaw) : Prop :=
  MixedPayoffIntegrable value equilibrium equilibrium ∧
    ∀ deviation : ConcessionLaw,
      MixedPayoffIntegrable value deviation equilibrium →
        mixedExpectedPayoff value deviation equilibrium ≤
          mixedExpectedPayoff value equilibrium equilibrium

/-! ## The complete-information exponential law -/

/-- The source's complete-information candidate `Q_v`: exponential
concession time with mean `v`. The proof argument `hv` is data because no
probability law exists at the displayed rate unless `v > 0`. -/
noncomputable def exponentialConcessionLaw (v : ℝ) (hv : 0 < v) :
    ConcessionLaw where
  measure := expMeasure v⁻¹
  isProbabilityMeasure := isProbabilityMeasure_expMeasure (inv_pos.mpr hv)
  ae_nonnegative := by
    rw [ae_iff]
    rw [show {t : ℝ | ¬ 0 ≤ t} = Iio 0 by ext t; simp]
    suffices expMeasure v⁻¹ (Iic 0) = 0 by
      exact measure_mono_null Iio_subset_Iic_self this
    have hprob : IsProbabilityMeasure (expMeasure v⁻¹) :=
      isProbabilityMeasure_expMeasure (inv_pos.mpr hv)
    letI : IsProbabilityMeasure (expMeasure v⁻¹) := hprob
    rw [← ofReal_cdf]
    simp [cdf_expMeasure_eq (inv_pos.mpr hv)]

/-- The cumulative distribution function of `Q_v` is exactly the formula in
item 1 of [MFoGT, Example 7.4.1]. -/
theorem cdf_exponentialConcessionLaw (v : ℝ) (hv : 0 < v) (t : ℝ) :
    cdf (exponentialConcessionLaw v hv).measure t =
      if 0 ≤ t then 1 - Real.exp (-t / v) else 0 := by
  rw [exponentialConcessionLaw, cdf_expMeasure_eq (inv_pos.mpr hv)]
  congr 2
  field_simp [hv.ne']

/-- Rewrite an integral against a positive-rate exponential law as its
Lebesgue-density integral. -/
lemma expIntegral_eq_density (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂expMeasure r =
      ∫ x, exponentialPDFReal r x * f x := by
  rw [show expMeasure r =
      volume.withDensity (fun x => ENNReal.ofReal (exponentialPDFReal r x)) by
    rfl]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_exponentialPDFReal r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [smul_eq_mul, exponentialPDFReal_nonneg hr]

/-- Integrability against a positive-rate exponential law is equivalent to
integrability after multiplying by its Lebesgue density. -/
lemma expIntegrable_iff_density (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ) :
    Integrable f (expMeasure r) ↔
      Integrable (fun x => exponentialPDFReal r x * f x) := by
  rw [show expMeasure r =
      volume.withDensity (fun x => ENNReal.ofReal (exponentialPDFReal r x)) by
    rfl]
  rw [integrable_withDensity_iff
    (measurable_exponentialPDFReal r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [] with x
  simp [exponentialPDFReal_nonneg hr]
  ring

/-- Almost-everywhere decomposition of the density-weighted payoff into the
win interval and the loss tail. The two omitted endpoints are Lebesgue-null;
this is where the source's tie convention enters the proof. -/
lemma weightedPayoff_ae (v r s : ℝ) (hs : 0 ≤ s) :
    (fun t => exponentialPDFReal r t * payoff v s t) =ᵐ[volume]
      (fun t =>
        (Ioc 0 s).indicator
            (fun t => r * Real.exp (-r * t) * (v - t)) t +
          (Ioi s).indicator
            (fun t => r * Real.exp (-r * t) * (-s)) t) := by
  have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) 0)
  have hnes : ∀ᵐ t : ℝ ∂volume, t ≠ s := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) s)
  filter_upwards [hne0, hnes] with t ht0 hts
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · have hwin : t ∉ Ioc 0 s := by
      exact fun h => (not_lt_of_ge htneg.le) h.1
    have hlose : t ∉ Ioi s := by
      exact fun h => (not_lt_of_ge (htneg.le.trans hs)) h
    rw [Set.indicator_of_notMem hwin, Set.indicator_of_notMem hlose]
    simp [exponentialPDFReal, gammaPDFReal, htneg]
  · rcases lt_or_gt_of_ne hts with htl | htg
    · have hwin : t ∈ Ioc 0 s := ⟨htpos, htl.le⟩
      have hlose : t ∉ Ioi s := fun h => lt_asymm h htl
      rw [Set.indicator_of_mem hwin, Set.indicator_of_notMem hlose]
      rw [payoff, if_pos htl]
      simp [exponentialPDFReal, gammaPDFReal, htpos.le]
    · have hwin : t ∉ Ioc 0 s := fun h => (not_lt_of_ge h.2) htg
      have hlose : t ∈ Ioi s := htg
      rw [Set.indicator_of_notMem hwin, Set.indicator_of_mem hlose]
      rw [payoff, if_neg (not_lt_of_ge htg.le)]
      simp [exponentialPDFReal, gammaPDFReal, htpos.le]

/-- The density-weighted payoff of every nonnegative pure concession time is
integrable against Lebesgue measure. -/
lemma weightedPayoff_integrable (v r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    Integrable (fun t => exponentialPDFReal r t * payoff v s t) := by
  let win := fun t : ℝ => r * Real.exp (-r * t) * (v - t)
  let lose := fun t : ℝ => r * Real.exp (-r * t) * (-s)
  have hwin : IntegrableOn win (Ioc 0 s) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
    apply Continuous.intervalIntegrable (μ := volume)
    dsimp [win]
    fun_prop
  have hexp :
      IntegrableOn (fun t : ℝ => Real.exp (-r * t)) (Ioi s) := by
    simpa [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -r) (neg_lt_zero.mpr hr) s
  have hlose : IntegrableOn lose (Ioi s) := by
    have hconst := hexp.const_mul (r * (-s))
    refine hconst.congr ?_
    filter_upwards [] with t
    dsimp [lose]
    ring
  have hsum :
      Integrable
        (fun t =>
          (Ioc 0 s).indicator win t + (Ioi s).indicator lose t) :=
    (hwin.integrable_indicator measurableSet_Ioc).add
      (hlose.integrable_indicator measurableSet_Ioi)
  apply hsum.congr
  simpa [win, lose] using weightedPayoff_ae v r s hs |>.symm

/-- At rate `r = 1 / v`, the density-weighted pure payoff is zero. The proof
computes both the bounded win interval and the unbounded loss tail and proves
their integrability before adding the integrals. -/
lemma weightedPayoff_integral_eq_zero (v r s : ℝ) (hr : 0 < r)
    (hrv : r * v = 1) (hs : 0 ≤ s) :
    ∫ t, exponentialPDFReal r t * payoff v s t = 0 := by
  let win := fun t : ℝ => r * Real.exp (-r * t) * (v - t)
  let lose := fun t : ℝ => r * Real.exp (-r * t) * (-s)
  have hwin_interval :
      (∫ t in 0..s, win t) = s * Real.exp (-r * s) := by
    have hcont : Continuous fun t : ℝ => t * Real.exp (-r * t) := by
      fun_prop
    have hderiv :
        ∀ t : ℝ,
          HasDerivAt (fun x : ℝ => x * Real.exp (-r * x))
            (win t) t := by
      intro t
      have h :=
        (hasDerivAt_id t).mul
          (((hasDerivAt_id t).const_mul (-r)).exp)
      convert h using 1
      dsimp [win]
      linear_combination Real.exp (-r * t) * hrv
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
      hcont.continuousOn (fun t _ => hderiv t)
      ((by fun_prop : Continuous win).intervalIntegrable 0 s)]
    simp
  have hwin_set :
      (∫ t in Ioc 0 s, win t) = s * Real.exp (-r * s) := by
    rw [← intervalIntegral.integral_of_le hs]
    exact hwin_interval
  have hlose_set :
      (∫ t in Ioi s, lose t) = -s * Real.exp (-r * s) := by
    have hexp :=
      integral_exp_mul_Ioi (a := -r) (neg_lt_zero.mpr hr) s
    rw [show (∫ t in Ioi s, lose t) =
        (r * (-s)) * ∫ t in Ioi s, Real.exp (-r * t) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [lose]
      ring]
    rw [show (∫ t in Ioi s, Real.exp (-r * t)) =
        -Real.exp ((-r) * s) / (-r) by
      simpa [neg_mul] using hexp]
    field_simp [hr.ne']
  rw [integral_congr_ae (weightedPayoff_ae v r s hs)]
  change
    (∫ t, (Ioc 0 s).indicator win t + (Ioi s).indicator lose t) = 0
  have hwin_indicator :
      Integrable ((Ioc 0 s).indicator win) :=
    (show IntegrableOn win (Ioc 0 s) by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hs]
      exact
        (show Continuous win by
          dsimp [win]
          fun_prop).intervalIntegrable 0 s).integrable_indicator
            measurableSet_Ioc
  have hlose_indicator :
      Integrable ((Ioi s).indicator lose) := by
    have hexp :
        IntegrableOn (fun t : ℝ => Real.exp (-r * t)) (Ioi s) := by
      simpa [neg_mul] using
        integrableOn_exp_mul_Ioi (a := -r) (neg_lt_zero.mpr hr) s
    have hconst := hexp.const_mul (r * (-s))
    have hlose : IntegrableOn lose (Ioi s) := by
      refine hconst.congr ?_
      filter_upwards [] with t
      dsimp [lose]
      ring
    exact hlose.integrable_indicator measurableSet_Ioi
  calc
    (∫ t, (Ioc 0 s).indicator win t + (Ioi s).indicator lose t) =
        (∫ t, (Ioc 0 s).indicator win t) +
          ∫ t, (Ioi s).indicator lose t :=
      integral_add hwin_indicator hlose_indicator
    _ = (∫ t in Ioc 0 s, win t) + ∫ t in Ioi s, lose t := by
      rw [integral_indicator measurableSet_Ioc,
        integral_indicator measurableSet_Ioi]
    _ = 0 := by rw [hwin_set, hlose_set]; ring

/-- Every nonnegative pure concession time earns zero against `Q_v`. This is
the payoff identity behind the complete-information equilibrium. -/
theorem pureExpectedPayoff_exponential (v : ℝ) (hv : 0 < v)
    (ownTime : ℝ) (hownTime : 0 ≤ ownTime) :
    pureExpectedPayoff v ownTime (exponentialConcessionLaw v hv) = 0 := by
  unfold pureExpectedPayoff exponentialConcessionLaw
  rw [expIntegral_eq_density v⁻¹ (inv_pos.mpr hv)]
  exact weightedPayoff_integral_eq_zero v v⁻¹ ownTime
    (inv_pos.mpr hv) (inv_mul_cancel₀ hv.ne') hownTime

/-- The pure payoff in the preceding theorem is a genuine integral. -/
theorem purePayoffIntegrable_exponential (v : ℝ) (hv : 0 < v)
    (ownTime : ℝ) (hownTime : 0 ≤ ownTime) :
    PurePayoffIntegrable v ownTime (exponentialConcessionLaw v hv) := by
  unfold PurePayoffIntegrable exponentialConcessionLaw
  rw [expIntegrable_iff_density v⁻¹ (inv_pos.mpr hv)]
  exact weightedPayoff_integrable v v⁻¹ ownTime (inv_pos.mpr hv) hownTime

/-- Every nonnegative concession-time law has a genuine iterated expected
payoff against `Q_v`. Thus the integrability guard in the equilibrium
predicate does not exclude any admissible probability-law deviation in the
complete-information theorem. -/
theorem mixedPayoffIntegrable_exponentialOpponent (v : ℝ) (hv : 0 < v)
    (own : ConcessionLaw) :
    MixedPayoffIntegrable v own (exponentialConcessionLaw v hv) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [own.ae_nonnegative] with ownTime hownTime
    exact purePayoffIntegrable_exponential v hv ownTime hownTime
  · apply (integrable_const (c := (0 : ℝ))).congr
    filter_upwards [own.ae_nonnegative] with ownTime hownTime
    exact (pureExpectedPayoff_exponential v hv ownTime hownTime).symm

/-- The exponential law of mean `v` is a symmetric equilibrium of the
complete-information war of attrition. The quantification includes every
probability-law deviation supported almost everywhere on nonnegative times,
and compares only genuinely integrable iterated expectations. -/
theorem isSymmetricEquilibrium_exponentialConcessionLaw (v : ℝ) (hv : 0 < v) :
    IsSymmetricEquilibrium v (exponentialConcessionLaw v hv) := by
  let q := exponentialConcessionLaw v hv
  have hpure_zero :
      ∀ᵐ ownTime ∂q.measure, pureExpectedPayoff v ownTime q = 0 := by
    filter_upwards [q.ae_nonnegative] with ownTime hownTime
    exact pureExpectedPayoff_exponential v hv ownTime hownTime
  have hequilibrium_integrable :
      MixedPayoffIntegrable v q q := by
    exact mixedPayoffIntegrable_exponentialOpponent v hv q
  refine ⟨hequilibrium_integrable, ?_⟩
  intro deviation _
  have hdeviation_zero :
      ∀ᵐ ownTime ∂deviation.measure,
        pureExpectedPayoff v ownTime q = 0 := by
    filter_upwards [deviation.ae_nonnegative] with ownTime hownTime
    exact pureExpectedPayoff_exponential v hv ownTime hownTime
  have hdeviation_payoff :
      mixedExpectedPayoff v deviation q = 0 := by
    unfold mixedExpectedPayoff
    rw [integral_congr_ae hdeviation_zero]
    simp
  have hequilibrium_payoff :
      mixedExpectedPayoff v q q = 0 := by
    unfold mixedExpectedPayoff
    rw [integral_congr_ae hpure_zero]
    simp
  rw [hdeviation_payoff, hequilibrium_payoff]

/-- A regular full-support symmetric equilibrium for the
complete-information model.

The source's word "only" needs more than the bare mixed-equilibrium
inequality. This structure records the standard analytic class in which that
claim is valid: an absolutely continuous law whose density is continuous on
positive times, a differentiable CDF and pure payoff there, and indifference
at every nonnegative concession time. Continuity is deliberately not required
at zero: the exponential density jumps from zero on negative times to its
positive right limit. The derivative field is stated for the actual
expectation, not for a surrogate objective. -/
structure RegularFullSupportEquilibrium (v : ℝ)
    (law : ConcessionLaw) where
  /-- The common prize value is positive. -/
  value_pos : 0 < v
  /-- The law satisfies the full mixed-deviation equilibrium predicate. -/
  equilibrium : IsSymmetricEquilibrium v law
  /-- Lebesgue density of the concession law. -/
  density : ℝ → ℝ
  /-- The density is continuous on strictly positive concession times. -/
  continuous_density : ContinuousOn density (Ioi 0)
  /-- The density is nonnegative. -/
  density_nonnegative : ∀ x, 0 ≤ density x
  /-- The concession law is exactly the density-generated measure. -/
  measure_eq_withDensity :
    law.measure =
      volume.withDensity (fun x => ENNReal.ofReal (density x))
  /-- The CDF starts at zero. -/
  cdf_zero : cdf law.measure 0 = 0
  /-- The CDF is continuous from the right-hand model boundary. -/
  cdf_continuousAt_zero : ContinuousAt (cdf law.measure) 0
  /-- On positive times the CDF derivative is the density. -/
  cdf_hasDerivAt : ∀ s, 0 < s →
    HasDerivAt (cdf law.measure) (density s) s
  /-- Derivative of the actual pure expected payoff. -/
  payoff_hasDerivAt : ∀ s, 0 < s →
    HasDerivAt (fun t => pureExpectedPayoff v t law)
      (v * density s - (1 - cdf law.measure s)) s
  /-- Full-support mixing makes every nonnegative pure time indifferent. -/
  indifferent : ∀ s, 0 ≤ s →
    pureExpectedPayoff v s law =
      mixedExpectedPayoff v law law

namespace RegularFullSupportEquilibrium

/-- The exponential equilibrium belongs to the regular full-support class.
This non-vacuity witness is important: global continuity of the density at
zero would incorrectly exclude the source's own exponential candidate. -/
noncomputable def exponential (v : ℝ) (hv : 0 < v) :
    RegularFullSupportEquilibrium v (exponentialConcessionLaw v hv) where
  value_pos := hv
  equilibrium := isSymmetricEquilibrium_exponentialConcessionLaw v hv
  density := exponentialPDFReal v⁻¹
  continuous_density := by
    intro x hx
    change 0 < x at hx
    have heq :
        exponentialPDFReal v⁻¹ =ᶠ[𝓝 x]
          fun y => v⁻¹ * Real.exp (-(v⁻¹ * y)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      change 0 < y at hy
      simp [exponentialPDFReal, gammaPDFReal, hy.le]
    have hcontinuous :
        ContinuousAt (fun y : ℝ => v⁻¹ * Real.exp (-(v⁻¹ * y))) x := by
      fun_prop
    exact (hcontinuous.congr_of_eventuallyEq heq).continuousWithinAt
  density_nonnegative := exponentialPDFReal_nonneg (inv_pos.mpr hv)
  measure_eq_withDensity := by
    rfl
  cdf_zero := by
    simp [cdf_exponentialConcessionLaw v hv]
  cdf_continuousAt_zero := by
    have heq :
        cdf (exponentialConcessionLaw v hv).measure =
          fun t => max (1 - Real.exp (-t / v)) 0 := by
      funext t
      rw [cdf_exponentialConcessionLaw v hv t]
      by_cases ht : 0 ≤ t
      · rw [if_pos ht, max_eq_left]
        have harg : -t / v ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hv.le
        exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr harg)
      · have htneg : t < 0 := lt_of_not_ge ht
        rw [if_neg ht, max_eq_right]
        exact sub_nonpos.mpr
          (Real.one_le_exp_iff.mpr
            (div_nonneg (neg_nonneg.mpr htneg.le) hv.le))
    rw [heq]
    fun_prop
  cdf_hasDerivAt := by
    intro s hs
    have hlocal :
        (fun t => cdf (exponentialConcessionLaw v hv).measure t) =ᶠ[𝓝 s]
          fun t => 1 - Real.exp (-(v⁻¹ * t)) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      change 0 < t at ht
      rw [cdf_exponentialConcessionLaw v hv t, if_pos ht.le]
      congr 2
      field_simp [hv.ne']
    have hsmooth :
        HasDerivAt (fun t : ℝ => 1 - Real.exp (-(v⁻¹ * t)))
          (v⁻¹ * Real.exp (-(v⁻¹ * s))) s := by
      have hsum :=
        (hasDerivAt_const s (1 : ℝ)).add
          (hasDerivAt_neg_exp_mul_exp (r := v⁻¹) (x := s))
      convert hsum using 1
      all_goals simp
    have hactual := hsmooth.congr_of_eventuallyEq hlocal
    simpa [exponentialPDFReal, gammaPDFReal, hs.le] using hactual
  payoff_hasDerivAt := by
    intro s hs
    have hlocal :
        (fun t => pureExpectedPayoff v t (exponentialConcessionLaw v hv)) =ᶠ[𝓝 s]
          fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact pureExpectedPayoff_exponential v hv t ht.le
    have hzero :
        HasDerivAt
          (fun t => pureExpectedPayoff v t (exponentialConcessionLaw v hv))
          0 s :=
      (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hlocal
    convert hzero using 1
    rw [cdf_exponentialConcessionLaw v hv s, if_pos hs.le]
    simp [exponentialPDFReal, gammaPDFReal, hs.le]
    have hexp : -(v⁻¹ * s) = -s / v := by
      field_simp [hv.ne']
    rw [hexp]
    field_simp [hv.ne']
    ring
  indifferent := by
    have hpure_zero :
        ∀ᵐ ownTime ∂(exponentialConcessionLaw v hv).measure,
          pureExpectedPayoff v ownTime (exponentialConcessionLaw v hv) = 0 := by
      filter_upwards [(exponentialConcessionLaw v hv).ae_nonnegative] with
        ownTime hownTime
      exact pureExpectedPayoff_exponential v hv ownTime hownTime
    have hmixed :
        mixedExpectedPayoff v (exponentialConcessionLaw v hv)
            (exponentialConcessionLaw v hv) = 0 := by
      unfold mixedExpectedPayoff
      rw [integral_congr_ae hpure_zero]
      simp
    intro s hs
    rw [pureExpectedPayoff_exponential v hv s hs, hmixed]

/-- Uniqueness of the complete-information equilibrium in the explicit
regular full-support class: its measure is the exponential law `Q_v`.

The proof differentiates the actual indifference identity, solves the
resulting survival ODE, treats the boundary by continuity, and finally uses
CDF extensionality for probability measures. -/
theorem measure_eq_exponential {v : ℝ} {law : ConcessionLaw}
    (h : RegularFullSupportEquilibrium v law) :
    law.measure = (exponentialConcessionLaw v h.value_pos).measure := by
  have hode : ∀ s, 0 < s →
      v * h.density s = 1 - cdf law.measure s := by
    intro s hs
    have hlocal :
        IsLocalMax (fun t => pureExpectedPayoff v t law) s := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      rw [h.indifferent t ht.le, h.indifferent s hs.le]
    have hz := hlocal.hasDerivAt_eq_zero (h.payoff_hasDerivAt s hs)
    linarith
  let H := fun s : ℝ =>
    Real.exp (s / v) * (1 - cdf law.measure s)
  have hHderiv : ∀ s, 0 < s → HasDerivAt H 0 s := by
    intro s hs
    have hexp :
        HasDerivAt (fun t : ℝ => Real.exp (t / v))
          (v⁻¹ * Real.exp (s / v)) s := by
      simpa only [id_eq, one_div, mul_comm] using
        ((hasDerivAt_id s).div_const v).exp
    have hsurvival :
        HasDerivAt (fun t => 1 - cdf law.measure t)
          (-h.density s) s := by
      simpa only [zero_sub] using
        (hasDerivAt_const s (1 : ℝ)).sub (h.cdf_hasDerivAt s hs)
    dsimp [H]
    convert hexp.mul hsurvival using 1
    rw [← hode s hs]
    field_simp [h.value_pos.ne']
    ring
  have hHcontinuous : ContinuousOn H (Ici 0) := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      have hexpcont :
          ContinuousAt (fun t : ℝ => Real.exp (t / v)) 0 := by
        fun_prop
      exact
        (hexpcont.mul
          (continuousAt_const.sub
            h.cdf_continuousAt_zero)).continuousWithinAt
    · exact
        (hHderiv s
          (lt_of_le_of_ne hs (Ne.symm hs0))).continuousAt.continuousWithinAt
  have hHconstant : ∀ x, 0 < x → H x = 1 := by
    intro x hx
    have hconst : ∀ y, 0 < y → H y = H x := by
      intro y hy
      apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun z hz =>
          (hHderiv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hHderiv z hz).deriv)
        hy hx
    have hlim0 :
        Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H 0)) :=
      ((hHcontinuous (0 : ℝ) (by simp)).mono
        Ioi_subset_Ici_self).tendsto
    have heq :
        H =ᶠ[𝓝[>] (0 : ℝ)] fun _ => H x := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hconst y hy
    have hlimx :
        Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H x)) :=
      tendsto_const_nhds.congr' heq.symm
    have heq0 := tendsto_nhds_unique hlim0 hlimx
    simpa [H, h.cdf_zero] using heq0.symm
  have hcdf_nonneg : ∀ t, 0 ≤ t →
      cdf law.measure t = 1 - Real.exp (-t / v) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [h.cdf_zero]
    · have hHt := hHconstant t (lt_of_le_of_ne ht (Ne.symm ht0))
      have hsurvival :
          1 - cdf law.measure t = 1 / Real.exp (t / v) := by
        apply (eq_div_iff (Real.exp_ne_zero _)).2
        simpa [H, mul_comm] using hHt
      have hinv :
          1 / Real.exp (t / v) = Real.exp (-t / v) := by
        rw [one_div, ← Real.exp_neg]
        congr 2
        ring
      rw [hinv] at hsurvival
      linarith
  have hcdf_neg : ∀ t, t < 0 → cdf law.measure t = 0 := by
    intro t ht
    have hnegative : law.measure (Iio 0) = 0 := by
      have hae := law.ae_nonnegative
      rw [ae_iff] at hae
      simpa only [not_le, setOf_mem_eq, mem_Iio] using hae
    have hnull : law.measure (Iic t) = 0 :=
      measure_mono_null (fun _ hx => lt_of_le_of_lt hx ht) hnegative
    rw [cdf_eq_real, measureReal_def, hnull]
    simp
  apply Measure.eq_of_cdf
  ext t
  rw [cdf_exponentialConcessionLaw v h.value_pos t]
  split_ifs with ht
  · exact hcdf_nonneg t ht
  · exact hcdf_neg t (lt_of_not_ge ht)

end RegularFullSupportEquilibrium

/-! ## Private values with a density -/

/-- Analytic data for the private-value part of
[MFoGT, Example 7.4.1].

The fields state the hypotheses suppressed by the textbook's short display:
`g` is a nonnegative continuous density on nonnegative values, `G` is its
cumulative distribution, and the survival probability is strictly positive at
every finite nonnegative value where it appears in a denominator. -/
structure DensityModel where
  /-- Cumulative distribution function of private values. -/
  cdf : ℝ → ℝ
  /-- Density of private values. -/
  density : ℝ → ℝ
  /-- The density is continuous. -/
  continuous_density : Continuous density
  /-- Negative values have zero density. -/
  density_of_neg : ∀ {x}, x < 0 → density x = 0
  /-- The density is nonnegative. -/
  density_nonnegative : ∀ x, 0 ≤ density x
  /-- `G` is differentiable with derivative `g`. -/
  hasDerivAt_cdf : ∀ x, HasDerivAt cdf (density x) x
  /-- The CDF vanishes at zero; hence the value law has no atom at zero. -/
  cdf_zero : cdf 0 = 0
  /-- Survival is positive at every finite nonnegative value. -/
  survival_pos : ∀ x, 0 ≤ x → 0 < 1 - cdf x
  /-- The density has total mass one on the nonnegative half-line. -/
  density_integral_one :
    ∫⁻ x, ENNReal.ofReal (density x) = 1

namespace DensityModel

/-- Probability law on private values generated by `density`. -/
noncomputable def valueLaw (M : DensityModel) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (M.density x))

/-- `valueLaw` is a probability measure; this is why
`density_integral_one` is part of the model rather than an informal
normalization convention. -/
instance (M : DensityModel) : IsProbabilityMeasure M.valueLaw where
  measure_univ := by
    simpa [valueLaw] using M.density_integral_one

/-- Private values are nonnegative almost surely. -/
theorem ae_nonnegative (M : DensityModel) :
    ∀ᵐ x ∂M.valueLaw, 0 ≤ x := by
  rw [ae_iff]
  rw [show {x : ℝ | ¬ 0 ≤ x} = Iio 0 by ext x; simp]
  rw [valueLaw, withDensity_apply _ measurableSet_Iio]
  rw [lintegral_eq_zero_iff
    M.continuous_density.measurable.ennreal_ofReal]
  change ∀ᵐ x ∂volume.restrict (Iio 0),
    ENNReal.ofReal (M.density x) = 0
  rw [ae_restrict_iff' measurableSet_Iio]
  filter_upwards [] with x hx
  rw [M.density_of_neg hx]
  simp

/-- The type-contingent pure concession time displayed in item 2 of
[MFoGT, Example 7.4.1]. -/
noncomputable def candidateStrategy (M : DensityModel) (value : ℝ) : ℝ :=
  ∫ t in 0..value, t * M.density t / (1 - M.cdf t)

/-- The integrand in the candidate strategy is continuous on every compact
nonnegative interval. This records both measurability and local
integrability, and uses the explicit positive-survival hypothesis. -/
theorem continuousOn_candidateIntegrand (M : DensityModel) {b : ℝ} :
    ContinuousOn (fun t => t * M.density t / (1 - M.cdf t)) (Icc 0 b) := by
  have hcdf : Continuous M.cdf :=
    continuous_iff_continuousAt.mpr fun x => (M.hasDerivAt_cdf x).continuousAt
  refine
    (continuousOn_id.mul M.continuous_density.continuousOn).div
      (continuousOn_const.sub hcdf.continuousOn) ?_
  intro x hx
  exact (M.survival_pos x hx.1).ne'

/-- The candidate strategy is well-defined by an ordinary integrable
function on every finite nonnegative type interval. -/
theorem candidateIntegrand_intervalIntegrable (M : DensityModel)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t => t * M.density t / (1 - M.cdf t))
      volume a b := by
  rcases le_total a b with hab | hba
  · apply
      ((M.continuousOn_candidateIntegrand (b := b)).mono ?_).intervalIntegrable
    simpa [uIcc_of_le hab] using
      (Icc_subset_Icc_left ha : Icc a b ⊆ Icc 0 b)
  · apply
      ((M.continuousOn_candidateIntegrand (b := a)).mono ?_).intervalIntegrable
    simpa [uIcc_of_ge hba] using
      (Icc_subset_Icc_left hb : Icc b a ⊆ Icc 0 a)

/-- The displayed candidate has the derivative dictated by the type hazard
rate. This is an actual application of the fundamental theorem of calculus;
the denominator is discharged using `survival_pos`. -/
theorem candidateStrategy_hasDerivAt (M : DensityModel) {value : ℝ}
    (hvalue : 0 ≤ value) :
    HasDerivAt M.candidateStrategy
      (value * M.density value / (1 - M.cdf value)) value := by
  let integrand := fun t => t * M.density t / (1 - M.cdf t)
  have hcdf : Continuous M.cdf :=
    continuous_iff_continuousAt.mpr fun x =>
      (M.hasDerivAt_cdf x).continuousAt
  have hint :
      IntervalIntegrable integrand volume 0 value :=
    M.candidateIntegrand_intervalIntegrable le_rfl hvalue
  have hcont : ContinuousAt integrand value := by
    exact
      (continuousAt_id.mul M.continuous_density.continuousAt).div
        (continuousAt_const.sub hcdf.continuousAt)
        (M.survival_pos value hvalue).ne'
  have hmeas : Measurable integrand := by
    dsimp [integrand]
    exact
      (measurable_id.mul M.continuous_density.measurable).div
        (measurable_const.sub hcdf.measurable)
  simpa [candidateStrategy, integrand] using
    intervalIntegral.integral_hasDerivAt_right hint
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter hcont

/-- Candidate concession times are nonnegative at nonnegative values. -/
theorem candidateStrategy_nonnegative (M : DensityModel) {value : ℝ}
    (hvalue : 0 ≤ value) : 0 ≤ M.candidateStrategy value := by
  rw [candidateStrategy]
  apply intervalIntegral.integral_nonneg hvalue
  intro t ht
  exact div_nonneg
    (mul_nonneg ht.1 (M.density_nonnegative t))
    (M.survival_pos t ht.1).le

/-- Expected payoff after parameterizing one's concession time by an opponent
type cutoff. Under a strictly increasing strategy this is the exact pure
payoff: opponent types below `cutoff` concede first and the remaining mass is
`1-G(cutoff)`. -/
noncomputable def cutoffExpectedPayoff (M : DensityModel)
    (strategy : ℝ → ℝ) (value cutoff : ℝ) : ℝ :=
  (∫ t in 0..cutoff, (value - strategy t) * M.density t) -
    strategy cutoff * (1 - M.cdf cutoff)

/-- The candidate cutoff-payoff function is continuous on every compact
nonnegative interval. -/
theorem continuousOn_candidateCutoffExpectedPayoff (M : DensityModel)
    (value : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn
      (fun x => M.cutoffExpectedPayoff M.candidateStrategy value x)
      (Icc 0 b) := by
  let winIntegrand :=
    fun t => (value - M.candidateStrategy t) * M.density t
  have hstrategy :
      ContinuousOn M.candidateStrategy (Icc 0 b) := by
    intro x hx
    exact
      (M.candidateStrategy_hasDerivAt hx.1).continuousAt.continuousWithinAt
  have hwin :
      ContinuousOn winIntegrand (Icc 0 b) :=
    (continuousOn_const.sub hstrategy).mul
      M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume 0 b :=
    (by simpa [uIcc_of_le hb] using hwin : ContinuousOn winIntegrand (uIcc 0 b)).intervalIntegrable
  have hprimitive :
      ContinuousOn (fun x => ∫ t in 0..x, winIntegrand t) (Icc 0 b) := by
    simpa [uIcc_of_le hb] using
      intervalIntegral.continuousOn_primitive_interval' hwin_integrable
        left_mem_uIcc
  have hcdf : Continuous M.cdf :=
    continuous_iff_continuousAt.mpr fun x =>
      (M.hasDerivAt_cdf x).continuousAt
  unfold cutoffExpectedPayoff
  exact hprimitive.sub
    (hstrategy.mul (continuousOn_const.sub hcdf.continuousOn))

/-- Along the candidate strategy, the derivative of cutoff payoff is
`(value-cutoff)g(cutoff)`. The hazard-rate terms cancel; this is the
calculation omitted in the textbook example. -/
theorem candidateCutoffExpectedPayoff_hasDerivAt (M : DensityModel)
    {value cutoff : ℝ} (hcutoff : 0 < cutoff) :
    HasDerivAt
      (fun x => M.cutoffExpectedPayoff M.candidateStrategy value x)
      ((value - cutoff) * M.density cutoff) cutoff := by
  let winIntegrand :=
    fun t => (value - M.candidateStrategy t) * M.density t
  have hstrategy :
      HasDerivAt M.candidateStrategy
        (cutoff * M.density cutoff / (1 - M.cdf cutoff)) cutoff :=
    M.candidateStrategy_hasDerivAt hcutoff.le
  have hstrategy_continuousOn :
      ContinuousOn M.candidateStrategy (Icc 0 cutoff) := by
    intro x hx
    exact
      (M.candidateStrategy_hasDerivAt hx.1).continuousAt.continuousWithinAt
  have hwin_continuousOn :
      ContinuousOn winIntegrand (Icc 0 cutoff) :=
    (continuousOn_const.sub hstrategy_continuousOn).mul
      M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume 0 cutoff :=
    (by
      simpa [uIcc_of_le hcutoff.le] using hwin_continuousOn :
        ContinuousOn winIntegrand (uIcc 0 cutoff)).intervalIntegrable
  have hwin_continuousAt : ContinuousAt winIntegrand cutoff := by
    exact
      (continuousAt_const.sub hstrategy.continuousAt).mul
        M.continuous_density.continuousAt
  have hstrategy_continuousOn_pos :
      ContinuousOn M.candidateStrategy (Ioi 0) := by
    intro x hx
    exact
      (M.candidateStrategy_hasDerivAt hx.le).continuousAt.continuousWithinAt
  have hwin_continuousOn_pos :
      ContinuousOn winIntegrand (Ioi 0) :=
    (continuousOn_const.sub hstrategy_continuousOn_pos).mul
      M.continuous_density.continuousOn
  have hfirst :
      HasDerivAt (fun x => ∫ t in 0..x, winIntegrand t)
        (winIntegrand cutoff) cutoff :=
    intervalIntegral.integral_hasDerivAt_right hwin_integrable
      (hwin_continuousOn_pos.stronglyMeasurableAtFilter
        isOpen_Ioi cutoff hcutoff)
      hwin_continuousAt
  have hsurvival :
      HasDerivAt (fun x => 1 - M.cdf x) (-M.density cutoff) cutoff := by
    simpa only [zero_sub] using
      (hasDerivAt_const cutoff (1 : ℝ)).sub (M.hasDerivAt_cdf cutoff)
  have hsecond :
      HasDerivAt
        (fun x => M.candidateStrategy x * (1 - M.cdf x))
        ((cutoff * M.density cutoff / (1 - M.cdf cutoff)) *
            (1 - M.cdf cutoff) +
          M.candidateStrategy cutoff * (-M.density cutoff)) cutoff :=
    hstrategy.mul hsurvival
  unfold cutoffExpectedPayoff
  convert hfirst.sub hsecond using 1
  field_simp [(M.survival_pos cutoff hcutoff.le).ne']
  ring

/-- The candidate cutoff `value` maximizes the rigorous cutoff payoff over all
nonnegative cutoffs. This theorem proves the global inequality by integrating
the signed derivative on both sides of `value`; no first-order condition is
used as a substitute for global optimality. -/
theorem candidateCutoffExpectedPayoff_le (M : DensityModel)
    {value cutoff : ℝ} (hvalue : 0 ≤ value) (hcutoff : 0 ≤ cutoff) :
    M.cutoffExpectedPayoff M.candidateStrategy value cutoff ≤
      M.cutoffExpectedPayoff M.candidateStrategy value value := by
  let derivative := fun t => (value - t) * M.density t
  have hderivative_continuous : Continuous derivative :=
    (continuous_const.sub continuous_id).mul M.continuous_density
  rcases le_total cutoff value with hcv | hvc
  · have hFTC :
        (∫ t in cutoff..value, derivative t) =
          M.cutoffExpectedPayoff M.candidateStrategy value value -
            M.cutoffExpectedPayoff M.candidateStrategy value cutoff := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f := fun x =>
          M.cutoffExpectedPayoff M.candidateStrategy value x)
        (f' := derivative) hcv ?_ ?_ ?_
      · exact
          (M.continuousOn_candidateCutoffExpectedPayoff value hvalue).mono
            (Icc_subset_Icc_left hcutoff)
      · intro t ht
        exact M.candidateCutoffExpectedPayoff_hasDerivAt
          (hcutoff.trans_lt ht.1)
      · exact hderivative_continuous.intervalIntegrable _ _
    have hnonneg : 0 ≤ ∫ t in cutoff..value, derivative t := by
      apply intervalIntegral.integral_nonneg hcv
      intro t ht
      exact mul_nonneg (sub_nonneg.mpr ht.2) (M.density_nonnegative t)
    linarith
  · have hFTC :
        (∫ t in value..cutoff, derivative t) =
          M.cutoffExpectedPayoff M.candidateStrategy value cutoff -
            M.cutoffExpectedPayoff M.candidateStrategy value value := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f := fun x =>
          M.cutoffExpectedPayoff M.candidateStrategy value x)
        (f' := derivative) hvc ?_ ?_ ?_
      · exact
          (M.continuousOn_candidateCutoffExpectedPayoff value hcutoff).mono
            (Icc_subset_Icc_left hvalue)
      · intro t ht
        exact M.candidateCutoffExpectedPayoff_hasDerivAt
          (hvalue.trans_lt ht.1)
      · exact hderivative_continuous.intervalIntegrable _ _
    have hnonpos : (∫ t in value..cutoff, derivative t) ≤ 0 := by
      have hzero :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume value cutoff :=
        intervalIntegrable_const
      simpa using intervalIntegral.integral_mono_on hvc
        (hderivative_continuous.intervalIntegrable _ _) hzero
        (fun t ht =>
          mul_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr ht.1) (M.density_nonnegative t))
    linarith

/-- The private-value density is Bochner integrable. This is derived from the
model's `ℝ≥0∞` normalization rather than assumed a second time. -/
theorem density_integrable (M : DensityModel) : Integrable M.density := by
  refine ⟨M.continuous_density.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have h :
      (fun x => ENNReal.ofReal ‖M.density x‖) =
        (fun x => ENNReal.ofReal (M.density x)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (M.density_nonnegative x)]
  rw [h, M.density_integral_one]
  simp

/-- The ordinary Lebesgue integral of the private-value density is one. -/
theorem integral_density (M : DensityModel) :
    ∫ x, M.density x = 1 := by
  apply ENNReal.ofReal_eq_one.mp
  rw [ofReal_integral_eq_lintegral_ofReal M.density_integrable
    (ae_of_all _ M.density_nonnegative)]
  exact M.density_integral_one

/-- On a nonnegative cutoff, integrating the density over the lower tail
recovers the declared CDF. -/
theorem integral_density_Iic (M : DensityModel) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Iic x, M.density t = M.cdf x := by
  have hinterval :
      (∫ t in 0..x, M.density t) = M.cdf x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
      (continuous_iff_continuousAt.mpr fun t =>
        (M.hasDerivAt_cdf t).continuousAt).continuousOn
      (fun t _ => M.hasDerivAt_cdf t)
      (M.continuous_density.intervalIntegrable 0 x)]
    rw [M.cdf_zero, sub_zero]
  have hnegative :
      (∫ t in Iic 0, M.density t) = 0 := by
    calc
      (∫ t in Iic 0, M.density t) =
          ∫ (_t : ℝ) in Iic (0 : ℝ), (0 : ℝ) := by
        apply integral_congr_ae
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
        have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
          rw [ae_iff]
          simpa only [not_ne_iff, setOf_eq_eq_singleton] using
            (measure_singleton (μ := volume) 0)
        filter_upwards [hne] with t ht htle
        exact M.density_of_neg (lt_of_le_of_ne htle ht)
      _ = 0 := by simp
  calc
    (∫ t in Iic x, M.density t) =
        (∫ t in Iic 0, M.density t) +
          ∫ t in Ioc 0 x, M.density t := by
      rw [← Iic_union_Ioc_eq_Iic hx,
        setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          M.density_integrable.integrableOn
          M.density_integrable.integrableOn]
    _ = ∫ t in 0..x, M.density t := by
      rw [hnegative, zero_add, intervalIntegral.integral_of_le hx]
    _ = M.cdf x := hinterval

/-- The upper-tail density integral is the survival probability. -/
theorem integral_density_Ioi (M : DensityModel) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Ioi x, M.density t = 1 - M.cdf x := by
  have hsplit :=
    integral_add_compl (s := Iic x) measurableSet_Iic M.density_integrable
  rw [compl_Iic, M.integral_density_Iic hx, M.integral_density] at hsplit
  linarith

/-- Rewrite an expectation under the private-value law as a
Lebesgue-density integral. -/
theorem valueIntegral_eq_density (M : DensityModel) (f : ℝ → ℝ) :
    ∫ x, f x ∂M.valueLaw = ∫ x, M.density x * f x := by
  unfold valueLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    M.continuous_density.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [smul_eq_mul, M.density_nonnegative x]

/-- Exact integrability criterion after replacing the value law by its
Lebesgue density. -/
theorem valueIntegrable_iff_density (M : DensityModel) (f : ℝ → ℝ) :
    Integrable f M.valueLaw ↔
      Integrable (fun x => M.density x * f x) := by
  unfold valueLaw
  rw [integrable_withDensity_iff
    M.continuous_density.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [] with x
  simp [M.density_nonnegative x]
  ring

/-- Actual interim payoff against a pure type-contingent opponent strategy. -/
noncomputable def interimExpectedPayoff (M : DensityModel)
    (strategy : ℝ → ℝ) (value ownTime : ℝ) : ℝ :=
  ∫ opponentValue,
    payoff value ownTime (strategy opponentValue) ∂M.valueLaw

/-- Almost-everywhere decomposition of actual strategic payoff under a
strictly increasing opponent strategy. Negative types and the two boundary
points are handled as density-null sets. -/
theorem densityWeightedStrategyPayoff_ae (M : DensityModel)
    (strategy : ℝ → ℝ) (hstrict : StrictMonoOn strategy (Ici 0))
    (value cutoff : ℝ) (hcutoff : 0 ≤ cutoff) :
    (fun t =>
      M.density t * payoff value (strategy cutoff) (strategy t)) =ᵐ[volume]
      (fun t =>
        (Ioc 0 cutoff).indicator
            (fun t => (value - strategy t) * M.density t) t +
          (Ioi cutoff).indicator
            (fun t => -strategy cutoff * M.density t) t) := by
  have hne0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) 0)
  have hnecutoff : ∀ᵐ t : ℝ ∂volume, t ≠ cutoff := by
    rw [ae_iff]
    simpa only [not_ne_iff, setOf_eq_eq_singleton] using
      (measure_singleton (μ := volume) cutoff)
  filter_upwards [hne0, hnecutoff] with t ht0 htcutoff
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · have hwin : t ∉ Ioc 0 cutoff := by
      exact fun h => (not_lt_of_ge htneg.le) h.1
    have hlose : t ∉ Ioi cutoff := by
      exact fun h => (not_lt_of_ge (htneg.le.trans hcutoff)) h
    rw [Set.indicator_of_notMem hwin, Set.indicator_of_notMem hlose]
    rw [M.density_of_neg htneg]
    simp
  · rcases lt_or_gt_of_ne htcutoff with htl | htg
    · have hwin : t ∈ Ioc 0 cutoff := ⟨htpos, htl.le⟩
      have hlose : t ∉ Ioi cutoff := fun h => lt_asymm h htl
      rw [Set.indicator_of_mem hwin, Set.indicator_of_notMem hlose]
      rw [payoff, if_pos (hstrict htpos.le hcutoff htl)]
      ring
    · have hwin : t ∉ Ioc 0 cutoff :=
        fun h => (not_lt_of_ge h.2) htg
      have hlose : t ∈ Ioi cutoff := htg
      rw [Set.indicator_of_notMem hwin, Set.indicator_of_mem hlose]
      rw [payoff, if_neg
        (not_lt_of_ge (hstrict hcutoff htpos.le htg).le)]
      ring

/-- The density-weighted strategic payoff is integrable. -/
theorem densityWeightedStrategyPayoff_integrable (M : DensityModel)
    (strategy : ℝ → ℝ) (hcontinuous : ContinuousOn strategy (Ici 0))
    (hstrict : StrictMonoOn strategy (Ici 0))
    (value cutoff : ℝ) (hcutoff : 0 ≤ cutoff) :
    Integrable
      (fun t =>
        M.density t * payoff value (strategy cutoff) (strategy t)) := by
  let win := fun t : ℝ => (value - strategy t) * M.density t
  let lose := fun t : ℝ => -strategy cutoff * M.density t
  have hwin : IntegrableOn win (Ioc 0 cutoff) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hcutoff]
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hcutoff, win] using
      (continuousOn_const.sub
        (hcontinuous.mono Icc_subset_Ici_self)).mul
          M.continuous_density.continuousOn
  have hlose : IntegrableOn lose (Ioi cutoff) := by
    exact (M.density_integrable.const_mul (-strategy cutoff)).integrableOn
  have hsum :
      Integrable
        (fun t =>
          (Ioc 0 cutoff).indicator win t +
            (Ioi cutoff).indicator lose t) :=
    (hwin.integrable_indicator measurableSet_Ioc).add
      (hlose.integrable_indicator measurableSet_Ioi)
  apply hsum.congr
  simpa [win, lose] using
    (M.densityWeightedStrategyPayoff_ae strategy hstrict value cutoff
      hcutoff).symm

/-- Actual payoff integrability for every action represented by a
nonnegative type cutoff. -/
theorem payoff_integrable_of_strictMono (M : DensityModel)
    (strategy : ℝ → ℝ) (hcontinuous : ContinuousOn strategy (Ici 0))
    (hstrict : StrictMonoOn strategy (Ici 0))
    (value cutoff : ℝ) (hcutoff : 0 ≤ cutoff) :
    Integrable
      (fun opponentValue =>
        payoff value (strategy cutoff) (strategy opponentValue))
      M.valueLaw := by
  rw [M.valueIntegrable_iff_density]
  exact M.densityWeightedStrategyPayoff_integrable strategy hcontinuous
    hstrict value cutoff hcutoff

/-- The cutoff expression is exactly the actual expected payoff, not a
surrogate objective. -/
theorem interimExpectedPayoff_eq_cutoff (M : DensityModel)
    (strategy : ℝ → ℝ) (hcontinuous : ContinuousOn strategy (Ici 0))
    (hstrict : StrictMonoOn strategy (Ici 0))
    (value cutoff : ℝ) (hcutoff : 0 ≤ cutoff) :
    M.interimExpectedPayoff strategy value (strategy cutoff) =
      M.cutoffExpectedPayoff strategy value cutoff := by
  unfold interimExpectedPayoff
  rw [M.valueIntegral_eq_density]
  rw [integral_congr_ae
    (M.densityWeightedStrategyPayoff_ae strategy hstrict value cutoff
      hcutoff)]
  let win := fun t : ℝ => (value - strategy t) * M.density t
  let lose := fun t : ℝ => -strategy cutoff * M.density t
  change
    (∫ t, (Ioc 0 cutoff).indicator win t +
      (Ioi cutoff).indicator lose t) =
        M.cutoffExpectedPayoff strategy value cutoff
  have hwin : IntegrableOn win (Ioc 0 cutoff) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hcutoff]
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hcutoff, win] using
      (continuousOn_const.sub
        (hcontinuous.mono Icc_subset_Ici_self)).mul
          M.continuous_density.continuousOn
  have hlose : IntegrableOn lose (Ioi cutoff) :=
    (M.density_integrable.const_mul (-strategy cutoff)).integrableOn
  rw [integral_add
    (hwin.integrable_indicator measurableSet_Ioc)
    (hlose.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioi,
    ← intervalIntegral.integral_of_le hcutoff]
  have hlose_eq :
      (∫ t in Ioi cutoff, lose t) =
        -strategy cutoff * (1 - M.cdf cutoff) := by
    rw [show (∫ t in Ioi cutoff, lose t) =
        -strategy cutoff * ∫ t in Ioi cutoff, M.density t by
      rw [← integral_const_mul]]
    rw [M.integral_density_Ioi hcutoff]
  rw [hlose_eq]
  unfold cutoffExpectedPayoff
  dsimp [win]
  ring

/-- Regular density models used for the source's uniqueness assertion.
Strict positivity is what transports value-law almost-everywhere statements
back to Lebesgue almost-everywhere statements. Divergence of the candidate
strategy makes every nonnegative action representable by a cutoff. -/
structure Regular (M : DensityModel) : Prop where
  /-- Positive types have strictly positive density. -/
  density_pos : ∀ x, 0 < x → 0 < M.density x
  /-- Candidate concession times exhaust the nonnegative action line. -/
  candidate_tendsto :
    Tendsto M.candidateStrategy atTop atTop

/-- The candidate strategy is continuous on nonnegative values. -/
theorem continuousOn_candidateStrategy (M : DensityModel) :
    ContinuousOn M.candidateStrategy (Ici 0) := by
  intro x hx
  exact
    (M.candidateStrategy_hasDerivAt hx).continuousAt.continuousWithinAt

/-- Strict density positivity makes the candidate strategy strictly
increasing. -/
theorem strictMonoOn_candidateStrategy (M : DensityModel) (R : M.Regular) :
    StrictMonoOn M.candidateStrategy (Ici 0) := by
  apply strictMonoOn_of_deriv_pos
    (convex_Ici (𝕜 := ℝ) (0 : ℝ))
    M.continuousOn_candidateStrategy
  intro x hx
  rw [interior_Ici] at hx
  rw [(M.candidateStrategy_hasDerivAt hx.le).deriv]
  exact div_pos
    (mul_pos hx (R.density_pos x hx))
    (M.survival_pos x hx.le)

/-- Under the explicit tail condition in `Regular`, every nonnegative action
is the candidate action of a nonnegative cutoff. -/
theorem candidateStrategy_surjOn (M : DensityModel) (R : M.Regular) :
    SurjOn M.candidateStrategy (Ici 0) (Ici 0) := by
  intro ownTime hownTime
  have himage :
      Ici (M.candidateStrategy 0) ⊆
        M.candidateStrategy '' Ici 0 :=
    isPreconnected_Ici.intermediate_value_Ici self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop 0))
      M.continuousOn_candidateStrategy R.candidate_tendsto
  have hzero : M.candidateStrategy 0 = 0 := by
    simp [candidateStrategy]
  obtain ⟨cutoff, hcutoff, hcutoff_eq⟩ :=
    himage (by simpa [hzero] using hownTime)
  exact ⟨cutoff, hcutoff, hcutoff_eq⟩

end DensityModel

/-! ## Regular private-value uniqueness -/

/-- A regular symmetric equilibrium in the density model. The extra clauses
are the analytic hypotheses needed to justify the source's word "only":
strict monotonicity and differentiability of the pure strategy,
almost-everywhere interim optimality with pointwise deviation comparisons,
and genuine integrability of every payoff being compared. -/
structure IsRegularSymmetricEquilibrium (M : DensityModel)
    (strategy : ℝ → ℝ) : Prop where
  /-- The strategy starts at zero. -/
  map_zero : strategy 0 = 0
  /-- Concession times are nonnegative at nonnegative values. -/
  nonnegative : ∀ x, 0 ≤ x → 0 ≤ strategy x
  /-- Higher values wait strictly longer. -/
  strictMonoOn : StrictMonoOn strategy (Ici 0)
  /-- The strategy is differentiable on positive values. -/
  differentiableAt : ∀ x, 0 < x → DifferentiableAt ℝ strategy x
  /-- Interim payoff exists for every nonnegative type and deviation. -/
  payoff_integrable : ∀ value ownTime, 0 ≤ value → 0 ≤ ownTime →
    Integrable (payoff value ownTime ∘ strategy) M.valueLaw
  /-- Almost every positive-density type optimizes its concession time.
  The conclusion is deliberately almost everywhere rather than pointwise. -/
  optimal_ae :
    ∀ᵐ value ∂M.valueLaw, 0 ≤ value ∧
      ∀ ownTime, 0 ≤ ownTime →
        (∫ opponentValue,
            payoff value ownTime (strategy opponentValue) ∂M.valueLaw) ≤
          ∫ opponentValue,
            payoff value (strategy value) (strategy opponentValue)
              ∂M.valueLaw

namespace DensityModel

/-- The source's displayed private-value strategy is an actual regular
symmetric equilibrium. The proof compares the original payoff integrals,
represents every nonnegative deviation by a cutoff, and invokes the global
cutoff optimality theorem. -/
theorem candidate_isRegularSymmetricEquilibrium (M : DensityModel)
    (R : M.Regular) :
    IsRegularSymmetricEquilibrium M M.candidateStrategy := by
  have hcontinuous := M.continuousOn_candidateStrategy
  have hstrict := M.strictMonoOn_candidateStrategy R
  refine
    { map_zero := by simp [candidateStrategy]
      nonnegative := fun _ hvalue => M.candidateStrategy_nonnegative hvalue
      strictMonoOn := hstrict
      differentiableAt := fun x hx =>
        (M.candidateStrategy_hasDerivAt hx.le).differentiableAt
      payoff_integrable := ?_
      optimal_ae := ?_ }
  · intro value ownTime _ hownTime
    obtain ⟨cutoff, hcutoff, hcutoff_eq⟩ :=
      M.candidateStrategy_surjOn R hownTime
    rw [← hcutoff_eq]
    exact M.payoff_integrable_of_strictMono M.candidateStrategy
      hcontinuous hstrict value cutoff hcutoff
  · filter_upwards [M.ae_nonnegative] with value hvalue
    refine ⟨hvalue, ?_⟩
    intro ownTime hownTime
    obtain ⟨cutoff, hcutoff, hcutoff_eq⟩ :=
      M.candidateStrategy_surjOn R hownTime
    rw [← hcutoff_eq]
    rw [show
        (∫ opponentValue,
          payoff value (M.candidateStrategy cutoff)
            (M.candidateStrategy opponentValue) ∂M.valueLaw) =
            M.interimExpectedPayoff M.candidateStrategy value
              (M.candidateStrategy cutoff) by rfl]
    rw [M.interimExpectedPayoff_eq_cutoff M.candidateStrategy
      hcontinuous hstrict value cutoff hcutoff]
    rw [show
        (∫ opponentValue,
          payoff value (M.candidateStrategy value)
            (M.candidateStrategy opponentValue) ∂M.valueLaw) =
            M.interimExpectedPayoff M.candidateStrategy value
              (M.candidateStrategy value) by rfl]
    rw [M.interimExpectedPayoff_eq_cutoff M.candidateStrategy
      hcontinuous hstrict value value hvalue]
    exact M.candidateCutoffExpectedPayoff_le hvalue hcutoff

/-- Derivative of the exact cutoff payoff for an arbitrary regular strategy.
The cancellation gives `value * g - strategy' * (1-G)`. -/
theorem cutoffExpectedPayoff_hasDerivAt (M : DensityModel)
    (strategy : ℝ → ℝ) (hcontinuous : ContinuousOn strategy (Ici 0))
    {value cutoff d : ℝ} (hcutoff : 0 < cutoff)
    (hstrategy : HasDerivAt strategy d cutoff) :
    HasDerivAt
      (fun x => M.cutoffExpectedPayoff strategy value x)
      (value * M.density cutoff - d * (1 - M.cdf cutoff)) cutoff := by
  let winIntegrand :=
    fun t => (value - strategy t) * M.density t
  have hwin_continuousOn :
      ContinuousOn winIntegrand (Icc 0 cutoff) := by
    exact
      (continuousOn_const.sub
        (hcontinuous.mono Icc_subset_Ici_self)).mul
          M.continuous_density.continuousOn
  have hwin_integrable :
      IntervalIntegrable winIntegrand volume 0 cutoff := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hcutoff.le] using hwin_continuousOn
  have hwin_continuousAt : ContinuousAt winIntegrand cutoff := by
    exact
      (continuousAt_const.sub hstrategy.continuousAt).mul
        M.continuous_density.continuousAt
  have hwin_continuousOn_pos :
      ContinuousOn winIntegrand (Ioi 0) := by
    exact
      (continuousOn_const.sub
        (hcontinuous.mono Ioi_subset_Ici_self)).mul
          M.continuous_density.continuousOn
  have hfirst :
      HasDerivAt (fun x => ∫ t in 0..x, winIntegrand t)
        (winIntegrand cutoff) cutoff :=
    intervalIntegral.integral_hasDerivAt_right hwin_integrable
      (hwin_continuousOn_pos.stronglyMeasurableAtFilter
        isOpen_Ioi cutoff hcutoff)
      hwin_continuousAt
  have hsurvival :
      HasDerivAt (fun x => 1 - M.cdf x) (-M.density cutoff) cutoff := by
    simpa only [zero_sub] using
      (hasDerivAt_const cutoff (1 : ℝ)).sub (M.hasDerivAt_cdf cutoff)
  have hsecond :
      HasDerivAt
        (fun x => strategy x * (1 - M.cdf x))
        (d * (1 - M.cdf cutoff) +
          strategy cutoff * (-M.density cutoff)) cutoff :=
    hstrategy.mul hsurvival
  unfold cutoffExpectedPayoff
  convert hfirst.sub hsecond using 1
  dsimp [winIntegrand]
  ring

/-- Almost-everywhere first-order characterization of every regular
equilibrium. Strict density positivity transports the equilibrium condition
from the value law to Lebesgue measure. -/
theorem regularEquilibrium_deriv_eq_candidate_ae
    (M : DensityModel) (R : M.Regular) (strategy : ℝ → ℝ)
    (hE : IsRegularSymmetricEquilibrium M strategy)
    (hcontinuous : ContinuousOn strategy (Ici 0)) :
    ∀ᵐ value ∂volume, 0 < value →
      deriv strategy value =
        value * M.density value / (1 - M.cdf value) := by
  have hoptimal_volume :
      ∀ᵐ value ∂volume, 0 < value →
        ∀ ownTime, 0 ≤ ownTime →
          M.interimExpectedPayoff strategy value ownTime ≤
            M.interimExpectedPayoff strategy value (strategy value) := by
    have hoptimal := hE.optimal_ae
    unfold valueLaw at hoptimal
    have hweighted := (ae_withDensity_iff
      M.continuous_density.measurable.ennreal_ofReal).mp hoptimal
    filter_upwards [hweighted] with value hvalue hvalue_pos
    have hdensity_ne :
        ENNReal.ofReal (M.density value) ≠ 0 := by
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (R.density_pos value hvalue_pos)
    have hopt := hvalue hdensity_ne
    intro ownTime hownTime
    exact hopt.2 ownTime hownTime
  filter_upwards [hoptimal_volume] with value hopt hvalue
  have hstrategy :
      HasDerivAt strategy (deriv strategy value) value :=
    (hE.differentiableAt value hvalue).hasDerivAt
  have hcutoff_deriv :=
    M.cutoffExpectedPayoff_hasDerivAt strategy hcontinuous
      (value := value) (cutoff := value)
      (d := deriv strategy value) hvalue hstrategy
  have hlocalMax :
      IsLocalMax
        (fun cutoff => M.cutoffExpectedPayoff strategy value cutoff) value := by
    filter_upwards [Ioi_mem_nhds hvalue] with cutoff hcutoff
    have hcutoff_pos : 0 < cutoff := hcutoff
    have hcutoff_nonneg := hcutoff_pos.le
    have haction := hE.nonnegative cutoff hcutoff_nonneg
    have hactual := hopt hvalue (strategy cutoff) haction
    rw [M.interimExpectedPayoff_eq_cutoff strategy hcontinuous
      hE.strictMonoOn value cutoff hcutoff_nonneg] at hactual
    rw [M.interimExpectedPayoff_eq_cutoff strategy hcontinuous
      hE.strictMonoOn value value hvalue.le] at hactual
    exact hactual
  have hzero := hlocalMax.hasDerivAt_eq_zero hcutoff_deriv
  field_simp [(M.survival_pos value hvalue.le).ne']
  linarith

/-- Uniqueness of the private-value equilibrium in the explicit regularity
class. The conclusion is pointwise on nonnegative values, while the
equilibrium premise itself is only value-law almost everywhere. Absolute
continuity is the exact hypothesis that permits integrating the
almost-everywhere derivative identity. -/
theorem regularEquilibrium_eq_candidate
    (M : DensityModel) (R : M.Regular) (strategy : ℝ → ℝ)
    (hE : IsRegularSymmetricEquilibrium M strategy)
    (hcontinuous : ContinuousOn strategy (Ici 0))
    (habsolutelyContinuous :
      ∀ b, 0 ≤ b → AbsolutelyContinuousOnInterval strategy 0 b) :
    ∀ x, 0 ≤ x → strategy x = M.candidateStrategy x := by
  have hderiv :=
    M.regularEquilibrium_deriv_eq_candidate_ae R strategy hE hcontinuous
  intro x hx
  have hderiv_interval :
      ∀ᵐ t ∂volume, t ∈ uIoc 0 x →
        deriv strategy t =
          t * M.density t / (1 - M.cdf t) := by
    filter_upwards [hderiv] with t ht
    intro htmem
    have htpos : 0 < t := by
      rw [uIoc_of_le hx] at htmem
      exact htmem.1
    exact ht htpos
  calc
    strategy x = ∫ t in 0..x, deriv strategy t := by
      rw [(habsolutelyContinuous x hx).integral_deriv_eq_sub,
        hE.map_zero, sub_zero]
    _ = ∫ t in 0..x,
        t * M.density t / (1 - M.cdf t) :=
      intervalIntegral.integral_congr_ae hderiv_interval
    _ = M.candidateStrategy x := by rfl

end DensityModel

end StrategicGame.WarOfAttrition
