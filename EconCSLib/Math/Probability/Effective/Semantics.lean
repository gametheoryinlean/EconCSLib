/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.Effective.Core
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Measure semantics of effective probability queries

This analytic leaf interprets the measure-free interfaces in
`Effective.Core`.  An `EventSemantics` assigns a measurable set to each event
code.  `RatOracle.Represents` says that every rational interval returned by an
oracle contains one fixed real value, and `EffectiveLaw.Represents` says that
the represented values are the probabilities of the coded events under one
probability measure.

The main correctness theorem proves, by structural induction, that the
executable oracle for a finite rational simple observable encloses its
Bochner integral.  The proof-only `SimpleObservable.Denotes` relation keeps
the analytic function out of executable data.  Pushforward, law bind, and
kernel composition correctness follow from explicit map and kernel
representation certificates.  Shrinking oracle widths also make the
represented real value unique, yielding exact-integral theorems for
`ExactLaw` backends.

All generic uses of sets, real integrals, and measures are confined to this
analytic leaf.  Concrete analytic instances may import it, but none of these
semantic witnesses is inspected by the executable query operations.
-/

open MeasureTheory

namespace EffectiveProbability

universe uEvent vEvent wEvent uα uβ uγ

/-- Set-theoretic interpretation of a selected event-code language. -/
structure EventSemantics (EventCode : Type uEvent) (α : Type uα)
    [MeasurableSpace α] where
  /-- Measurable event denoted by a code. -/
  denote : EventCode → Set α
  /-- Every event in the selected language is measurable. -/
  measurable_denote : ∀ event, MeasurableSet (denote event)

namespace RatEnclosure

/-- A real value lies in a rational enclosure after exact coercion of both
endpoints to `ℝ`. -/
def ContainsReal (interval : RatEnclosure) (value : ℝ) : Prop :=
  (interval.lower : ℝ) ≤ value ∧ value ≤ (interval.upper : ℝ)

/-- Rational membership implies membership after exact coercion to `ℝ`. -/
theorem Contains.containsReal {interval : RatEnclosure} {value : ℚ}
    (h : interval.Contains value) : interval.ContainsReal (value : ℝ) := by
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

@[simp]
theorem containsReal_exact (value : ℚ) :
    (exact value).ContainsReal (value : ℝ) := by
  simp [ContainsReal]

/-- Real interval membership is preserved by Minkowski addition. -/
theorem ContainsReal.add {left right : RatEnclosure} {x y : ℝ}
    (hx : left.ContainsReal x) (hy : right.ContainsReal y) :
    (left.add right).ContainsReal (x + y) := by
  exact ⟨by exact_mod_cast add_le_add hx.1 hy.1,
    by exact_mod_cast add_le_add hx.2 hy.2⟩

/-- Real interval membership is preserved by rational scaling. -/
theorem ContainsReal.scale {interval : RatEnclosure} {value : ℝ}
    (hvalue : interval.ContainsReal value) (factor : ℚ) :
    (interval.scale factor).ContainsReal ((factor : ℝ) * value) := by
  by_cases hfactor : 0 ≤ factor
  · rw [ContainsReal, scale_lower_of_nonneg interval hfactor,
      scale_upper_of_nonneg interval hfactor]
    have hfactorReal : (0 : ℝ) ≤ (factor : ℝ) := by
      exact_mod_cast hfactor
    constructor
    · simpa using mul_le_mul_of_nonneg_left hvalue.1 hfactorReal
    · simpa using mul_le_mul_of_nonneg_left hvalue.2 hfactorReal
  · have hnegative : factor < 0 := lt_of_not_ge hfactor
    rw [ContainsReal, scale_lower_of_neg interval hnegative,
      scale_upper_of_neg interval hnegative]
    have hfactorReal : (factor : ℝ) ≤ 0 := by
      exact_mod_cast hnegative.le
    constructor
    · simpa using mul_le_mul_of_nonpos_left hvalue.2 hfactorReal
    · simpa using mul_le_mul_of_nonpos_left hvalue.1 hfactorReal

end RatEnclosure

namespace RatOracle

/-- An oracle represents a real value when every positive-tolerance query
returns a rational interval containing that same value. -/
def Represents (oracle : RatOracle) (value : ℝ) : Prop :=
  ∀ tolerance hpositive,
    (oracle.query tolerance hpositive).ContainsReal value

/-- A purely rational enclosure certificate also represents the coerced real
value. -/
theorem Encloses.represents {oracle : RatOracle} {value : ℚ}
    (h : oracle.Encloses value) : oracle.Represents (value : ℝ) := by
  intro tolerance hpositive
  exact (h tolerance hpositive).containsReal

/-- Representation respects equality of the represented real value. -/
theorem Represents.congr {oracle : RatOracle} {x y : ℝ}
    (hx : oracle.Represents x) (hxy : x = y) :
    oracle.Represents y := by
  subst y
  exact hx

/-- An exact rational oracle represents the corresponding real number. -/
theorem exact_represents (value : ℚ) :
    (exact value).Represents (value : ℝ) :=
  (exact_encloses value).represents

/-- Representation is preserved by oracle addition. -/
theorem Represents.add {left right : RatOracle} {x y : ℝ}
    (hx : left.Represents x) (hy : right.Represents y) :
    (left.add right).Represents (x + y) := by
  intro tolerance hpositive
  rw [add_query left right tolerance hpositive]
  exact (hx (tolerance / 2) (half_pos hpositive)).add
    (hy (tolerance / 2) (half_pos hpositive))

/-- Representation is preserved by rational oracle scaling. -/
theorem Represents.scale {oracle : RatOracle} {value : ℝ}
    (hvalue : oracle.Represents value) (factor : ℚ) :
    (oracle.scale factor).Represents ((factor : ℝ) * value) := by
  intro tolerance hpositive
  by_cases hfactor : factor = 0
  · subst factor
    simpa using RatEnclosure.containsReal_exact 0
  · have hquery : 0 < tolerance / |factor| :=
      div_pos hpositive (abs_pos.mpr hfactor)
    rw [scale_query_of_ne oracle hfactor hpositive]
    exact (hvalue (tolerance / |factor|) hquery).scale factor

private theorem le_of_represents {oracle : RatOracle} {x y : ℝ}
    (hx : oracle.Represents x) (hy : oracle.Represents y) : x ≤ y := by
  by_contra hxy
  have hyx : y < x := lt_of_not_ge hxy
  obtain ⟨tolerance, hpositive, htolerance⟩ :=
    exists_pos_rat_lt (sub_pos.mpr hyx)
  let interval := oracle.query tolerance hpositive
  have hxmem : interval.ContainsReal x := hx tolerance hpositive
  have hymem : interval.ContainsReal y := hy tolerance hpositive
  have hspan : x - y ≤
      (interval.upper : ℝ) - (interval.lower : ℝ) := by
    linarith [hxmem.2, hymem.1]
  have hwidthRat := oracle.query_width_le tolerance hpositive
  have hwidth :
      ((interval.upper : ℝ) - (interval.lower : ℝ)) ≤
        (tolerance : ℝ) := by
    have hcast : (interval.width : ℝ) ≤ (tolerance : ℝ) := by
      exact_mod_cast hwidthRat
    simpa [RatEnclosure.width] using hcast
  linarith

/-- Two real values represented by the same shrinking-width oracle are equal.

If one value were strictly larger, density of the rationals would provide a
positive rational tolerance smaller than their gap.  Both values lie in the
same queried interval, while the oracle contract makes that interval no wider
than the chosen tolerance, a contradiction. -/
theorem Represents.unique {oracle : RatOracle} {x y : ℝ}
    (hx : oracle.Represents x) (hy : oracle.Represents y) : x = y :=
  le_antisymm (le_of_represents hx hy) (le_of_represents hy hx)

end RatOracle

namespace SimpleObservable

variable {EventCode : Type uEvent} {α : Type uα} [MeasurableSpace α]

/-- Proof-only denotation relation for a finite rational simple observable.

The real function is supplied explicitly and certified by the constructors;
the semantic layer does not manufacture function-valued data by classical
choice. -/
inductive Denotes (semantics : EventSemantics EventCode α) :
    SimpleObservable EventCode → (α → ℝ) → Prop where
  | const (value : ℚ) :
      Denotes semantics (.const value) (fun _ => (value : ℝ))
  | indicator (event : EventCode) :
      Denotes semantics (.indicator event)
        ((semantics.denote event).indicator fun _ => (1 : ℝ))
  | add {left right : SimpleObservable EventCode} {f g : α → ℝ} :
      Denotes semantics left f → Denotes semantics right g →
        Denotes semantics (.add left right) (fun x => f x + g x)
  | scale (coefficient : ℚ) {observable : SimpleObservable EventCode}
      {f : α → ℝ} :
      Denotes semantics observable f →
        Denotes semantics (.scale coefficient observable)
          (fun x => (coefficient : ℝ) * f x)

/-- A denotation certificate can be transported across equality of the
represented real function. -/
theorem Denotes.congr {semantics : EventSemantics EventCode α}
    {observable : SimpleObservable EventCode} {f g : α → ℝ}
    (h : Denotes semantics observable f) (hfg : f = g) :
    Denotes semantics observable g := by
  subst g
  exact h

/-- Every function certified by the denotation relation is measurable. -/
theorem Denotes.measurable {semantics : EventSemantics EventCode α}
    {observable : SimpleObservable EventCode} {f : α → ℝ}
    (h : Denotes semantics observable f) : Measurable f := by
  induction h with
  | const value => exact measurable_const
  | indicator event =>
      exact measurable_const.indicator (semantics.measurable_denote event)
  | add hleft hright ihLeft ihRight => exact ihLeft.add ihRight
  | scale coefficient h ih => exact ih.const_mul _

/-- Every certified denotation is integrable under a finite measure. -/
theorem Denotes.integrable {semantics : EventSemantics EventCode α}
    {observable : SimpleObservable EventCode} {f : α → ℝ}
    (h : Denotes semantics observable f) (μ : Measure α)
    [IsFiniteMeasure μ] : Integrable f μ := by
  induction h with
  | const value => exact integrable_const _
  | indicator event =>
      exact (integrable_const (μ := μ) (1 : ℝ)).indicator
        (semantics.measurable_denote event)
  | add hleft hright ihLeft ihRight => exact ihLeft.add ihRight
  | scale coefficient h ih => exact ih.const_mul _

end SimpleObservable

namespace EffectiveLaw

variable {EventCode : Type uEvent} {α : Type uα} [MeasurableSpace α]

/-- Correctness of an effective law with respect to a coded-event
interpretation and an analytic probability measure. -/
structure Represents (law : EffectiveLaw EventCode)
    (semantics : EventSemantics EventCode α) (μ : Measure α) : Prop where
  /-- The semantic law is normalized. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- Each executable event oracle encloses the corresponding event mass. -/
  mass : ∀ event,
    (law.mass event).Represents (μ.real (semantics.denote event))

/-- The executable expectation oracle for every finite rational simple
observable represents its true integral. -/
theorem Represents.expect_integral {law : EffectiveLaw EventCode}
    {semantics : EventSemantics EventCode α} {μ : Measure α}
    (represents : law.Represents semantics μ)
    {observable : SimpleObservable EventCode} {f : α → ℝ}
    (hdenotes : observable.Denotes semantics f) :
    (law.expect observable).Represents
      (∫ x, f x ∂μ) := by
  letI : IsProbabilityMeasure μ := represents.isProbabilityMeasure
  induction hdenotes with
  | const value =>
      refine (RatOracle.exact_represents value).congr ?_
      simp [probReal_univ]
  | indicator event =>
      refine (represents.mass event).congr ?_
      exact (integral_indicator_one (μ := μ)
        (semantics.measurable_denote event)).symm
  | add hleft hright ihLeft ihRight =>
      refine (ihLeft.add ihRight).congr ?_
      symm
      exact integral_add (hleft.integrable μ) (hright.integrable μ)
  | scale coefficient h ih =>
      refine (ih.scale coefficient).congr ?_
      symm
      exact integral_const_mul (μ := μ) (coefficient : ℝ) _

end EffectiveLaw

namespace ExactLaw

variable {EventCode : Type uEvent} {α : Type uα} [MeasurableSpace α]

variable (law : ExactLaw EventCode)
variable (semantics : EventSemantics EventCode α) (μ : Measure α)
variable (hprobability : IsProbabilityMeasure μ)
variable (hmass : ∀ event,
  (law.mass event : ℝ) = μ.real (semantics.denote event))

include hprobability hmass

/-- An exact rational backend represents an analytic probability law whenever
its selected event masses agree after coercion to `ℝ`.  This is the reusable
bridge for symbolic non-atomic instances with closed-form rational answers. -/
theorem toEffective_represents :
    law.toEffective.Represents semantics μ := by
  refine
    { isProbabilityMeasure := hprobability
      mass := ?_ }
  intro event
  exact (RatOracle.exact_represents (law.mass event)).congr (hmass event)

/-- Exact rational simple-observable expectation agrees with the genuine
integral under any represented analytic probability law. -/
theorem expectRat_eq_integral
    {observable : SimpleObservable EventCode} {f : α → ℝ}
    (hdenotes : observable.Denotes semantics f) :
    (law.expectRat observable : ℝ) = ∫ x, f x ∂μ := by
  apply RatOracle.Represents.unique
  · exact (law.toEffective_expect_encloses observable).represents
  · exact
      (law.toEffective_represents semantics μ hprobability hmass).expect_integral
        hdenotes

end ExactLaw

/-- Correctness of an effective preimage compiler with respect to a concrete
measurable function. -/
structure EffectiveMap.Represents
    {SourceCode : Type uEvent} {TargetCode : Type vEvent}
    {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    (mapping : EffectiveMap SourceCode TargetCode)
    (sourceSemantics : EventSemantics SourceCode α)
    (targetSemantics : EventSemantics TargetCode β)
    (f : α → β) : Prop where
  /-- Concrete map used by the semantic pushforward. -/
  measurable : Measurable f
  /-- Compiled source code denotes the concrete preimage. -/
  preimage : ∀ event,
    sourceSemantics.denote (mapping.preimage event) =
      f ⁻¹' targetSemantics.denote event

namespace EffectiveLaw.Represents

variable {SourceCode : Type uEvent} {TargetCode : Type vEvent}
variable {α : Type uα} {β : Type uβ}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Effective pushforward preserves representation when the event compiler
denotes measurable preimages. -/
theorem map {law : EffectiveLaw SourceCode}
    {mapping : EffectiveMap SourceCode TargetCode}
    {sourceSemantics : EventSemantics SourceCode α}
    {targetSemantics : EventSemantics TargetCode β}
    {μ : Measure α} {f : α → β}
    (hlaw : law.Represents sourceSemantics μ)
    (hmapping : mapping.Represents sourceSemantics targetSemantics f) :
    (law.map mapping).Represents targetSemantics (μ.map f) := by
  letI : IsProbabilityMeasure μ := hlaw.isProbabilityMeasure
  refine
    { isProbabilityMeasure :=
        Measure.isProbabilityMeasure_map hmapping.measurable.aemeasurable
      mass := ?_ }
  intro event
  refine (hlaw.mass (mapping.preimage event)).congr ?_
  have hmeasure :
      (μ.map f).real (targetSemantics.denote event) =
        μ.real (f ⁻¹' targetSemantics.denote event) := by
    simp only [Measure.real]
    rw [Measure.map_apply hmapping.measurable
      (targetSemantics.measurable_denote event)]
  rw [hmapping.preimage event]
  exact hmeasure.symm

end EffectiveLaw.Represents

/-- Correctness of an effective expectation transformer with respect to a
concrete Markov kernel.  Event pullback denotes the kernel probability of the
target event at each source point. -/
structure EffectiveKernel.Represents
    {SourceCode : Type uEvent} {TargetCode : Type vEvent}
    {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    (effective : EffectiveKernel SourceCode TargetCode)
    (sourceSemantics : EventSemantics SourceCode α)
    (targetSemantics : EventSemantics TargetCode β)
    (κ : ProbabilityTheory.Kernel α β) : Prop where
  /-- The analytic kernel is probability-valued at every source point. -/
  isMarkovKernel : ProbabilityTheory.IsMarkovKernel κ
  /-- Effective event pullback denotes the analytic event-probability
  function. -/
  pullEvent : ∀ event,
    (effective.pullEvent event).Denotes sourceSemantics
      (fun x => (κ x).real (targetSemantics.denote event))

namespace EffectiveKernel.Represents

open ProbabilityTheory

variable {SourceCode : Type uEvent} {TargetCode : Type vEvent}
variable {α : Type uα} {β : Type uβ}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Pullback correctness extends from event indicators to every finite
rational simple observable. -/
theorem pullObservable_integral
    {effective : EffectiveKernel SourceCode TargetCode}
    {sourceSemantics : EventSemantics SourceCode α}
    {targetSemantics : EventSemantics TargetCode β}
    {κ : Kernel α β}
    (represents : effective.Represents sourceSemantics targetSemantics κ)
    {observable : SimpleObservable TargetCode} {f : β → ℝ}
    (hdenotes : observable.Denotes targetSemantics f) :
    (effective.pullObservable observable).Denotes sourceSemantics
      (fun x => ∫ y, f y ∂κ x) := by
  letI : IsMarkovKernel κ := represents.isMarkovKernel
  induction hdenotes with
  | const value =>
      refine (SimpleObservable.Denotes.const value).congr ?_
      funext x
      simp [probReal_univ]
  | indicator event =>
      refine (represents.pullEvent event).congr ?_
      funext x
      exact (integral_indicator_one (μ := κ x)
        (targetSemantics.measurable_denote event)).symm
  | add hleft hright ihLeft ihRight =>
      refine (ihLeft.add ihRight).congr ?_
      funext x
      exact (integral_add
        (hleft.integrable (κ x)) (hright.integrable (κ x))).symm
  | scale coefficient h ih =>
      refine (ih.scale coefficient).congr ?_
      funext x
      exact (integral_const_mul (μ := κ x) (coefficient : ℝ)
        _).symm

/-- The real event mass of a measure–kernel composition is the integral of
the kernel's real event-probability function. -/
private theorem real_comp_apply
    {μ : Measure α} {κ : Kernel α β}
    [IsFiniteMeasure μ] [IsMarkovKernel κ]
    (event : Set β) (hevent : MeasurableSet event) :
    (κ ∘ₘ μ).real event = ∫ x, (κ x).real event ∂μ := by
  rw [Measure.real, Measure.bind_apply hevent κ.aemeasurable]
  symm
  apply integral_toReal
  · exact (κ.measurable_coe hevent).aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      (measure_lt_top (κ x) event)

/-- Effective law bind represents analytic composition of the source
probability measure with the represented Markov kernel. -/
theorem bind
    {law : EffectiveLaw SourceCode}
    {effective : EffectiveKernel SourceCode TargetCode}
    {sourceSemantics : EventSemantics SourceCode α}
    {targetSemantics : EventSemantics TargetCode β}
    {μ : Measure α} {κ : Kernel α β}
    (hlaw : law.Represents sourceSemantics μ)
    (hkernel : effective.Represents sourceSemantics targetSemantics κ) :
    (law.bind effective).Represents targetSemantics (κ ∘ₘ μ) := by
  letI : IsProbabilityMeasure μ := hlaw.isProbabilityMeasure
  letI : IsMarkovKernel κ := hkernel.isMarkovKernel
  refine
    { isProbabilityMeasure := by infer_instance
      mass := ?_ }
  intro event
  refine (hlaw.expect_integral (hkernel.pullEvent event)).congr ?_
  exact (real_comp_apply (μ := μ) (κ := κ)
    (targetSemantics.denote event)
    (targetSemantics.measurable_denote event)).symm

/-- Composition of represented effective transformers represents composition
of the corresponding analytic Markov kernels. -/
theorem comp
    {MiddleCode : Type vEvent} {FinalCode : Type wEvent}
    {γ : Type uγ} [MeasurableSpace γ]
    {outer : EffectiveKernel SourceCode MiddleCode}
    {inner : EffectiveKernel MiddleCode FinalCode}
    {sourceSemantics : EventSemantics SourceCode α}
    {middleSemantics : EventSemantics MiddleCode β}
    {finalSemantics : EventSemantics FinalCode γ}
    {κ : Kernel α β} {η : Kernel β γ}
    (houter : outer.Represents sourceSemantics middleSemantics κ)
    (hinner : inner.Represents middleSemantics finalSemantics η) :
    (outer.comp inner).Represents sourceSemantics finalSemantics (η ∘ₖ κ) := by
  letI : IsMarkovKernel κ := houter.isMarkovKernel
  letI : IsMarkovKernel η := hinner.isMarkovKernel
  refine
    { isMarkovKernel := by infer_instance
      pullEvent := ?_ }
  intro event
  refine
    (houter.pullObservable_integral (hinner.pullEvent event)).congr ?_
  funext x
  rw [Kernel.comp_apply]
  exact (real_comp_apply (μ := κ x) (κ := η)
    (finalSemantics.denote event)
    (finalSemantics.measurable_denote event)).symm

end EffectiveKernel.Represents

end EffectiveProbability
