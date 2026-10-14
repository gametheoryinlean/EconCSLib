/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.Effective.Core
import EconCSLib.Math.Probability.RationalIntervalUnion

/-!
# Exact effective queries for the uniform unit interval

This module is the first concrete non-atomic backend for the effective
probability interfaces.  Events are finite lists of closed rational interval
bounds.  `RationalIntervalUnion.probability` computes their exact mass, so the
effective law answers every requested precision with a singleton rational
enclosure.

The constant kernel is a genuine non-atomic transition model at its semantic
interpretation: every source code receives the same uniform unit-interval
law.  Its expectation transformer returns the exact rational mass as a source
constant.  Measure-theoretic volume and kernel correctness live in
`Effective.UniformSemantics`.
-/

namespace EffectiveProbability
namespace UniformUnitInterval

/-- Coded events are finite unions of rational closed intervals, with the
clipping and empty-interval conventions of `RationalIntervalUnion`. -/
abbrev EventCode := List RationalIntervalUnion.Bounds

/-- Exact symbolic unit-interval law on the selected event language. -/
def exactLaw : ExactLaw EventCode where
  mass := RationalIntervalUnion.probability

/-- Arbitrary-precision effective view of the exact symbolic law. -/
def law : EffectiveLaw EventCode :=
  exactLaw.toEffective

/-- Exact rational expectation of a finite linear combination of coded event
indicators. -/
def expectRat (observable : SimpleObservable EventCode) : ℚ :=
  exactLaw.expectRat observable

/-- Constant uniform-unit-interval kernel from any source event language. -/
def kernel (SourceCode : Type*) : EffectiveKernel SourceCode EventCode where
  pullEvent event :=
    .const (RationalIntervalUnion.probability event)

@[simp]
theorem exactLaw_mass (event : EventCode) :
    exactLaw.mass event = RationalIntervalUnion.probability event :=
  rfl

@[simp]
theorem law_mass (event : EventCode) :
    law.mass event =
      RatOracle.exact (RationalIntervalUnion.probability event) :=
  rfl

@[simp]
theorem expectRat_const (value : ℚ) :
    expectRat (.const value) = value :=
  rfl

@[simp]
theorem expectRat_indicator (event : EventCode) :
    expectRat (.indicator event) =
      RationalIntervalUnion.probability event :=
  rfl

@[simp]
theorem kernel_pullEvent (SourceCode : Type*) (event : EventCode) :
    (kernel SourceCode).pullEvent event =
      .const (RationalIntervalUnion.probability event) :=
  rfl

end UniformUnitInterval
end EffectiveProbability
