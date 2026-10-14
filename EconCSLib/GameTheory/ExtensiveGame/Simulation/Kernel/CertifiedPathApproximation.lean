/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.CertifiedPathApproximation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EffectivePathLaw

/-!
# Analytic certificates for effective state-path approximation

This semantic leaf gives the executable state-prefix approximation scheme a
genuine infinite-path meaning when the caller supplies mathematical evidence
for that meaning.  The evidence consists of:

* an analytic probability measure whose complete finite state-prefix
  marginals are the effective prefix laws;
* an external measurable and integrable real path utility;
* measurability of the lifted rational prefix observable; and
* a pointwise uniform error bound by the scheme's nonnegative rational
  radius at each relevant horizon.

The finite-marginal hypothesis is an equality of laws, not a claimed answer
for the target expectation.  Under these hypotheses the exact rational
`FiniteLaw.expectRat` center is the integral of the lifted prefix observable,
so the uniform pathwise estimate implies that the analytic expected utility
lies in the scheme interval.  A successful executable radius search therefore
has real error at most the requested tolerance.

The separate observable-measurability hypothesis is necessary at this level:
finite products of uncountable discrete measurable spaces need not make every
arbitrary prefix function measurable.  It is theorem-only evidence and is not
an input to the running search.  Likewise, the analytic path measure, utility,
and its integral occur only in the semantic statements; no target expectation
is passed to an executable definition.

## Main results

* `StateHistoryPolicy.pathMeasure_map_frestrictLe_eq_measure_effectivePathLaw_prefixLaw`
  supplies the required marginal certificate from an analytic realization;
* `StatePrefixApproximationScheme.expectedUtility_mem_interval_of_uniform`
  proves enclosure for an arbitrary certified analytic state-path law;
* `StatePrefixApproximationScheme.search_sound_expectedUtility_of_uniform`
  upgrades successful executable search to a true analytic error guarantee;
* the corresponding `StateHistoryPolicy` theorems apply those results directly
  to the library's existing analytic `pathMeasure`.
-/

open MeasureTheory ProbabilityTheory

namespace KernelArena

universe uS uA

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

@[reducible] private def piMeasurableSingletonClass
    {index : Type*} [Countable index]
    {coordinate : index → Type*}
    [(i : index) → MeasurableSpace (coordinate i)]
    [(i : index) → MeasurableSingletonClass (coordinate i)] :
    MeasurableSingletonClass ((i : index) → coordinate i) :=
  ⟨fun point => by
    have hsingleton :
        ({point} : Set ((i : index) → coordinate i)) =
          Set.univ.pi (fun i => {point i}) := by
      ext candidate
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
        true_implies]
      constructor
      · intro heq
        subst candidate
        intro i
        rfl
      · intro hcoordinate
        funext i
        exact hcoordinate i
    rw [hsingleton]
    exact MeasurableSet.pi Set.countable_univ fun i _ =>
      measurableSet_singleton (point i)⟩

namespace StateHistoryPolicy

variable {A : KernelArena}

/-- The complete prefix marginal of the original analytic state-path measure
is exactly the Dirac-measure interpretation of the effective prefix law.

This derives the semantic hypothesis used below from an analytic realization
of an effective history policy.  It identifies every requested finite
horizon; it does not make the infinite path measure executable. -/
theorem pathMeasure_map_frestrictLe_eq_measure_effectivePathLaw_prefixLaw
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (root : A.State) (horizon : ℕ) :
    (analytic.pathMeasure
        A.toMeasurable_measurableSet_terminalSet root).map
          (Preorder.frestrictLe (0 + horizon)) =
      μ[((policy.effectivePathLaw root).prefixLaw horizon |>.map
        fun history => history.toAnalytic).atoms] := by
  change
    analytic.prefixMeasure
        A.toMeasurable_measurableSet_terminalSet root (0 + horizon) = _
  rw [analytic.prefixMeasure_eq_partialTraj]
  exact (policy.measure_effectivePathLaw_prefixLaw_eq_partialTraj
    analytic realizes root horizon).symm

end StateHistoryPolicy

namespace StatePrefixApproximationScheme

variable {A : KernelArena} {start : ℕ}
variable {initialPrefix : A.StatePrefix start}

/-- Under an exact finite-marginal correspondence, the analytic integral of
one lifted rational prefix observable is the effective scheme's exact
rational center, coerced to `ℝ`.

The lift restricts a complete path through the absolute horizon
`start + horizon` and then reindexes that analytic prefix back to the
executable `StatePrefix` carrier. -/
theorem integral_liftedObservable_eq_center
    (scheme : StatePrefixApproximationScheme A start)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (pathMeasure : Measure (ℕ → A.toMeasurable.State))
    (horizon : ℕ)
    (finiteMarginal :
      pathMeasure.map (Preorder.frestrictLe (start + horizon)) =
        μ[((law.prefixLaw horizon).map
          fun history => history.toAnalytic).atoms])
    (hmeasurable : Measurable fun history :
        (index : Finset.Iic (start + horizon)) → A.toMeasurable.State =>
      (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ)) :
    (∫ path,
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (start + horizon) path)) : ℝ)
        ∂pathMeasure) =
      (scheme.center law horizon : ℝ) := by
  letI : MeasurableSingletonClass A.toMeasurable.State :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  letI : MeasurableSingletonClass
      ((index : Finset.Iic (start + horizon)) → A.toMeasurable.State) :=
    piMeasurableSingletonClass
  have hmap := integral_map
    (μ := pathMeasure)
    (φ := Preorder.frestrictLe (start + horizon))
    (Preorder.measurable_frestrictLe (start + horizon)).aemeasurable
    hmeasurable.aestronglyMeasurable
  calc
    (∫ path,
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (start + horizon) path)) : ℝ)
        ∂pathMeasure) =
        ∫ history,
          (scheme.observable horizon
            (StatePrefix.ofAnalytic history) : ℝ)
          ∂pathMeasure.map (Preorder.frestrictLe (start + horizon)) :=
      hmap.symm
    _ = ∫ history,
          (scheme.observable horizon
            (StatePrefix.ofAnalytic history) : ℝ)
          ∂μ[((law.prefixLaw horizon).map
            fun history => history.toAnalytic).atoms] := by
      rw [finiteMarginal]
    _ = (((law.prefixLaw horizon).map
          fun history => history.toAnalytic).expectRat
            (fun history =>
              scheme.observable horizon
                (StatePrefix.ofAnalytic history)) : ℝ) :=
      FiniteLaw.integral_measure_eq_expectRat _ _
    _ = ((law.prefixLaw horizon).expectRat
          (scheme.observable horizon) : ℝ) := by
      have hq := FiniteLaw.expectRat_map
        (fun history : A.StatePrefix (start + horizon) => history.toAnalytic)
        (law.prefixLaw horizon)
        (fun history =>
          scheme.observable horizon (StatePrefix.ofAnalytic history))
      exact congrArg (fun rational : ℚ => (rational : ℝ)) (by simpa using hq)
    _ = (scheme.center law horizon : ℝ) := rfl

/-- A genuine pointwise uniform approximation certificate bounds the error
between the external analytic expected utility and the executable rational
center by the scheme's nonnegative rational radius, both coerced to `ℝ`.

The proof first derives integrability of the lifted prefix observable from the
uniform difference bound, then applies the norm bound for the integral of the
difference.  It does not assume the desired expectation error as a premise. -/
theorem expectedUtility_error_le_radius_of_uniform
    (scheme : StatePrefixApproximationScheme A start)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (pathMeasure : Measure (ℕ → A.toMeasurable.State))
    [IsProbabilityMeasure pathMeasure]
    (utility : (ℕ → A.toMeasurable.State) → ℝ)
    (hutilityMeasurable : Measurable utility)
    (hutilityIntegrable : Integrable utility pathMeasure)
    (horizon : ℕ)
    (finiteMarginal :
      pathMeasure.map (Preorder.frestrictLe (start + horizon)) =
        μ[((law.prefixLaw horizon).map
          fun history => history.toAnalytic).atoms])
    (hobservable : Measurable fun history :
        (index : Finset.Iic (start + horizon)) → A.toMeasurable.State =>
      (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ))
    (huniform : ∀ path,
      |utility path -
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (start + horizon) path)) : ℝ)| ≤
        (scheme.radius horizon : ℝ)) :
    |(∫ path, utility path ∂pathMeasure) -
        (scheme.center law horizon : ℝ)| ≤
      (scheme.radius horizon : ℝ) := by
  let lifted : (ℕ → A.toMeasurable.State) → ℝ :=
    fun path =>
      (scheme.observable horizon
        (StatePrefix.ofAnalytic
          (Preorder.frestrictLe (start + horizon) path)) : ℝ)
  have hliftedMeasurable : Measurable lifted := by
    exact hobservable.comp
      (Preorder.measurable_frestrictLe (start + horizon))
  have hdiffIntegrable :
      Integrable (fun path => utility path - lifted path) pathMeasure := by
    apply Integrable.of_bound
      (hutilityMeasurable.sub hliftedMeasurable).aestronglyMeasurable
      (scheme.radius horizon : ℝ)
    exact Filter.Eventually.of_forall fun path => by
      simpa only [Real.norm_eq_abs, lifted] using huniform path
  have hliftedIntegrable : Integrable lifted pathMeasure := by
    apply (hutilityIntegrable.sub hdiffIntegrable).congr
    exact Filter.Eventually.of_forall fun path => by
      simp only [Pi.sub_apply]
      ring
  rw [← scheme.integral_liftedObservable_eq_center law pathMeasure
    horizon finiteMarginal hobservable]
  rw [← integral_sub hutilityIntegrable hliftedIntegrable]
  simpa only [Real.norm_eq_abs, lifted, probReal_univ,
    mul_one] using
      (norm_integral_le_of_norm_le_const
        (μ := pathMeasure)
        (f := fun path => utility path - lifted path)
        (C := (scheme.radius horizon : ℝ))
        (Filter.Eventually.of_forall fun path => by
          simpa only [Real.norm_eq_abs, lifted] using huniform path))

/-- The same uniform certificate places the analytic expected utility between
the scheme interval's rational endpoints after their exact coercion to
`ℝ`. -/
theorem expectedUtility_mem_interval_of_uniform
    (scheme : StatePrefixApproximationScheme A start)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (pathMeasure : Measure (ℕ → A.toMeasurable.State))
    [IsProbabilityMeasure pathMeasure]
    (utility : (ℕ → A.toMeasurable.State) → ℝ)
    (hutilityMeasurable : Measurable utility)
    (hutilityIntegrable : Integrable utility pathMeasure)
    (horizon : ℕ)
    (finiteMarginal :
      pathMeasure.map (Preorder.frestrictLe (start + horizon)) =
        μ[((law.prefixLaw horizon).map
          fun history => history.toAnalytic).atoms])
    (hobservable : Measurable fun history :
        (index : Finset.Iic (start + horizon)) → A.toMeasurable.State =>
      (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ))
    (huniform : ∀ path,
      |utility path -
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (start + horizon) path)) : ℝ)| ≤
        (scheme.radius horizon : ℝ)) :
    ((scheme.interval law horizon).1 : ℝ) ≤
        ∫ path, utility path ∂pathMeasure ∧
      (∫ path, utility path ∂pathMeasure) ≤
        ((scheme.interval law horizon).2 : ℝ) := by
  have herror := scheme.expectedUtility_error_le_radius_of_uniform
    law pathMeasure utility hutilityMeasurable hutilityIntegrable horizon
    finiteMarginal hobservable huniform
  have hbounds := abs_le.mp herror
  change
    (((scheme.center law horizon -
      (scheme.radius horizon : ℚ) : ℚ)) : ℝ) ≤
        ∫ path, utility path ∂pathMeasure ∧
      (∫ path, utility path ∂pathMeasure) ≤
        (((scheme.center law horizon +
          (scheme.radius horizon : ℚ) : ℚ)) : ℝ)
  push_cast
  constructor <;> linarith

/-- If executable radius search succeeds under horizonwise finite-marginal and
uniform approximation certificates, the returned interval contains the
analytic expected utility and its returned center has real error at most the
requested rational tolerance.

The running search still reads only the effective law, radius schedule,
tolerance, and budget.  The analytic measure, utility, and certificate occur
only in this theorem. -/
theorem search_sound_expectedUtility_of_uniform
    (scheme : StatePrefixApproximationScheme A start)
    (law : StateEffectivePathLawFrom A start initialPrefix)
    (pathMeasure : Measure (ℕ → A.toMeasurable.State))
    [IsProbabilityMeasure pathMeasure]
    (utility : (ℕ → A.toMeasurable.State) → ℝ)
    (hutilityMeasurable : Measurable utility)
    (hutilityIntegrable : Integrable utility pathMeasure)
    (finiteMarginal : ∀ horizon,
      pathMeasure.map (Preorder.frestrictLe (start + horizon)) =
        μ[((law.prefixLaw horizon).map
          fun history => history.toAnalytic).atoms])
    (hobservable : ∀ horizon,
      Measurable fun history :
          (index : Finset.Iic (start + horizon)) → A.toMeasurable.State =>
        (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ))
    (huniform : ∀ horizon path,
      |utility path -
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (start + horizon) path)) : ℝ)| ≤
        (scheme.radius horizon : ℝ))
    (tolerance : ℚ≥0) (budget horizon : ℕ)
    (result : RationalSchemeEstimate)
    (hsearch : scheme.search law tolerance budget = some (horizon, result)) :
    horizon < budget ∧
      scheme.estimate law horizon = result ∧
      (((result.interval.1 : ℚ) : ℝ) ≤
          ∫ path, utility path ∂pathMeasure ∧
        (∫ path, utility path ∂pathMeasure) ≤
          ((result.interval.2 : ℚ) : ℝ)) ∧
      |(∫ path, utility path ∂pathMeasure) - (result.center : ℝ)| ≤
        (tolerance : ℝ) := by
  obtain ⟨hbudget, hresult, hradius⟩ :=
    scheme.search_sound law tolerance budget horizon result hsearch
  have herror := scheme.expectedUtility_error_le_radius_of_uniform
    law pathMeasure utility hutilityMeasurable hutilityIntegrable horizon
    (finiteMarginal horizon) (hobservable horizon) (huniform horizon)
  have hinterval := scheme.expectedUtility_mem_interval_of_uniform
    law pathMeasure utility hutilityMeasurable hutilityIntegrable horizon
    (finiteMarginal horizon) (hobservable horizon) (huniform horizon)
  have hcenter : scheme.center law horizon = result.center := by
    simpa only [estimate] using
      congrArg RationalSchemeEstimate.center hresult
  have hradiusEq : scheme.radius horizon = result.radius := by
    simpa only [estimate] using
      congrArg RationalSchemeEstimate.radius hresult
  have hintervalEq : scheme.interval law horizon = result.interval := by
    exact congrArg RationalSchemeEstimate.interval hresult
  rw [hintervalEq] at hinterval
  refine ⟨hbudget, hresult, hinterval, ?_⟩
  calc
    |(∫ path, utility path ∂pathMeasure) - (result.center : ℝ)| =
        |(∫ path, utility path ∂pathMeasure) -
          (scheme.center law horizon : ℝ)| := by rw [hcenter]
    _ ≤ (scheme.radius horizon : ℝ) := herror
    _ = (result.radius : ℝ) := by rw [hradiusEq]
    _ ≤ (tolerance : ℝ) := by exact_mod_cast hradius

end StatePrefixApproximationScheme

namespace StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- For an effective state policy and its analytic realization, a pointwise
uniform prefix approximation places the existing analytic state-path expected
utility in the executable scheme interval at the selected horizon. -/
theorem expectedPathUtility_mem_schemeInterval_of_uniform
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (root : A.State)
    (scheme : StatePrefixApproximationScheme A 0)
    (utility : (ℕ → A.toMeasurable.State) → ℝ)
    (hutilityMeasurable : Measurable utility)
    (hutilityIntegrable : Integrable utility
      (analytic.pathMeasure
        A.toMeasurable_measurableSet_terminalSet root))
    (horizon : ℕ)
    (hobservable : Measurable fun history :
        (index : Finset.Iic (0 + horizon)) → A.toMeasurable.State =>
      (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ))
    (huniform : ∀ path,
      |utility path -
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (0 + horizon) path)) : ℝ)| ≤
        (scheme.radius horizon : ℝ)) :
    ((scheme.interval (policy.effectivePathLaw root) horizon).1 : ℝ) ≤
        ∫ path, utility path
          ∂analytic.pathMeasure
            A.toMeasurable_measurableSet_terminalSet root ∧
      (∫ path, utility path
          ∂analytic.pathMeasure
            A.toMeasurable_measurableSet_terminalSet root) ≤
        ((scheme.interval
          (policy.effectivePathLaw root) horizon).2 : ℝ) := by
  exact scheme.expectedUtility_mem_interval_of_uniform
    (policy.effectivePathLaw root)
    (analytic.pathMeasure
      A.toMeasurable_measurableSet_terminalSet root)
    utility hutilityMeasurable hutilityIntegrable horizon
    (policy.pathMeasure_map_frestrictLe_eq_measure_effectivePathLaw_prefixLaw
      analytic realizes root horizon)
    hobservable huniform

/-- For an effective state policy and its analytic realization, successful
state-scheme search returns an interval containing the actual analytic
expected path utility and a center whose real error is no larger than the
searched tolerance. -/
theorem search_sound_expectedPathUtility_of_uniform
    (policy : A.StateHistoryPolicy)
    (analytic : A.toMeasurable.HistoryActionPolicy)
    (realizes : policy.AnalyticallyRealizedBy analytic)
    (root : A.State)
    (scheme : StatePrefixApproximationScheme A 0)
    (utility : (ℕ → A.toMeasurable.State) → ℝ)
    (hutilityMeasurable : Measurable utility)
    (hutilityIntegrable : Integrable utility
      (analytic.pathMeasure
        A.toMeasurable_measurableSet_terminalSet root))
    (hobservable : ∀ horizon,
      Measurable fun history :
          (index : Finset.Iic (0 + horizon)) → A.toMeasurable.State =>
        (scheme.observable horizon (StatePrefix.ofAnalytic history) : ℝ))
    (huniform : ∀ horizon path,
      |utility path -
        (scheme.observable horizon
          (StatePrefix.ofAnalytic
            (Preorder.frestrictLe (0 + horizon) path)) : ℝ)| ≤
        (scheme.radius horizon : ℝ))
    (tolerance : ℚ≥0) (budget horizon : ℕ)
    (result : RationalSchemeEstimate)
    (hsearch :
      scheme.search (policy.effectivePathLaw root) tolerance budget =
        some (horizon, result)) :
    horizon < budget ∧
      scheme.estimate (policy.effectivePathLaw root) horizon = result ∧
      (((result.interval.1 : ℚ) : ℝ) ≤
          ∫ path, utility path
            ∂analytic.pathMeasure
              A.toMeasurable_measurableSet_terminalSet root ∧
        (∫ path, utility path
            ∂analytic.pathMeasure
              A.toMeasurable_measurableSet_terminalSet root) ≤
          ((result.interval.2 : ℚ) : ℝ)) ∧
      |(∫ path, utility path
          ∂analytic.pathMeasure
            A.toMeasurable_measurableSet_terminalSet root) -
          (result.center : ℝ)| ≤
        (tolerance : ℝ) := by
  exact scheme.search_sound_expectedUtility_of_uniform
    (policy.effectivePathLaw root)
    (analytic.pathMeasure
      A.toMeasurable_measurableSet_terminalSet root)
    utility hutilityMeasurable hutilityIntegrable
    (fun selected =>
      policy.pathMeasure_map_frestrictLe_eq_measure_effectivePathLaw_prefixLaw
        analytic realizes root selected)
    hobservable huniform tolerance budget horizon result hsearch

end StateHistoryPolicy

end KernelArena
