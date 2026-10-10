/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.Effective.Semantics
import EconCSLib.Math.Probability.Effective.Uniform
import EconCSLib.Math.Probability.RationalIntervalUnion.Volume

/-!
# Volume semantics for effective uniform-unit-interval queries

This analytic leaf proves that the executable event oracle in
`EffectiveProbability.UniformUnitInterval` represents the genuine non-atomic
uniform probability measure on the real unit interval.  It also proves the
corresponding statement for the constant effective kernel and identifies the
exact rational expectation of every certified simple observable with its
volume integral.

The executable definitions remain in `Effective.Uniform`; this module only
supplies their set, measure, kernel, and integral interpretation.
-/

open MeasureTheory
open ProbabilityTheory

namespace EffectiveProbability
namespace UniformUnitInterval

/-- A rational interval-union code denotes the corresponding measurable
subset of the real unit interval. -/
def eventSemantics : EventSemantics EventCode (Set.Icc (0 : ℝ) 1) where
  denote := RationalIntervalUnion.event
  measurable_denote := RationalIntervalUnion.event_measurable

/-- The exact executable unit-interval law represents genuine volume. -/
theorem law_represents_volume :
    law.Represents eventSemantics
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  apply exactLaw.toEffective_represents
  · infer_instance
  · intro event
    exact RationalIntervalUnion.probability_eq_volume event |>.symm

/-- Every certified simple-observable expectation encloses its genuine
uniform-volume integral. -/
theorem expect_represents_integral
    {observable : SimpleObservable EventCode}
    {f : Set.Icc (0 : ℝ) 1 → ℝ}
    (hdenotes : observable.Denotes eventSemantics f) :
    (law.expect observable).Represents
      (∫ x, f x
        ∂(volume : Measure (Set.Icc (0 : ℝ) 1))) :=
  law_represents_volume.expect_integral hdenotes

/-- The exact rational expectation for a certified simple observable is the
genuine integral under non-atomic unit-interval volume. -/
theorem expectRat_eq_integral
    {observable : SimpleObservable EventCode}
    {f : Set.Icc (0 : ℝ) 1 → ℝ}
    (hdenotes : observable.Denotes eventSemantics f) :
    (expectRat observable : ℝ) =
      ∫ x, f x ∂(volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  change (exactLaw.expectRat observable : ℝ) = _
  apply exactLaw.expectRat_eq_integral eventSemantics
    (volume : Measure (Set.Icc (0 : ℝ) 1))
  · infer_instance
  · intro event
    exact RationalIntervalUnion.probability_eq_volume event |>.symm
  · exact hdenotes

/-- The constant effective uniform kernel represents the constant analytic
kernel whose value is unit-interval volume. -/
theorem kernel_represents_volume
    {SourceCode : Type*} {α : Type*} [MeasurableSpace α]
    (sourceSemantics : EventSemantics SourceCode α) :
    (kernel SourceCode).Represents sourceSemantics eventSemantics
      (Kernel.const α (volume : Measure (Set.Icc (0 : ℝ) 1))) := by
  refine
    { isMarkovKernel := by infer_instance
      pullEvent := ?_ }
  intro event
  refine (show
    ((kernel SourceCode).pullEvent event).Denotes sourceSemantics
      (fun _ => (exactLaw.mass event : ℝ)) by
        simpa only [kernel_pullEvent] using
          (SimpleObservable.Denotes.const (semantics := sourceSemantics)
            (exactLaw.mass event))).congr ?_
  funext _
  simp only [Kernel.const_apply]
  exact RationalIntervalUnion.probability_eq_volume event |>.symm

end UniformUnitInterval
end EffectiveProbability
