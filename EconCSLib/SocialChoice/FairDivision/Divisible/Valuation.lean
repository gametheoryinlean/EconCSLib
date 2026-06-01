/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.Allocation
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.Valuation

Valuation-side infrastructure for divisible goods (cake cutting).

This file contains the abstract cake-valuation interface, the standard
measure-based specialization, and normalization vocabulary.
-/

namespace SocialChoice
namespace FairDivision
namespace Divisible

open MeasureTheory Set

/-- An abstract cake valuation assigns a value in `V` to each agent-piece pair. -/
structure CakeValuation (N Ω V : Type*) where
  /-- The valuation function: agent × cake-piece → value. -/
  val : N → Set Ω → V

/-- A measure-based cake valuation: each agent's value for a piece is given by their personal
    measure `μ i` on the cake `Ω`. -/
def MeasureValuation {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → MeasureTheory.Measure Ω) : CakeValuation N Ω ENNReal :=
  ⟨fun i S => μ i S⟩

namespace MeasureValuation

variable {N Ω : Type*} [MeasurableSpace Ω] (μ : N → MeasureTheory.Measure Ω)

/-- The value of the empty piece is zero. -/
@[simp]
lemma val_empty (i : N) : (MeasureValuation μ).val i ∅ = 0 :=
  MeasureTheory.measure_empty

/-- For disjoint measurable sets, `MeasureValuation` is additive. -/
lemma val_union (i : N) (S T : Set Ω)
    (hdisj : Disjoint S T) (ht : MeasurableSet T) :
    (MeasureValuation μ).val i (S ∪ T) =
      (MeasureValuation μ).val i S + (MeasureValuation μ).val i T :=
  MeasureTheory.measure_union hdisj ht

/-- For a countably-indexed pairwise-disjoint family of measurable sets, `MeasureValuation`
    is countably additive (tsum). -/
lemma val_iUnion [Countable N] (i : N) (A : Allocation N Ω)
    (hdisj : ∀ j k : N, j ≠ k → Disjoint (A j) (A k))
    (hmeas : ∀ j, MeasurableSet (A j)) :
    (MeasureValuation μ).val i (⋃ j, A j) = ∑' j, (MeasureValuation μ).val i (A j) :=
  MeasureTheory.measure_iUnion (fun ⦃j k⦄ hjk => hdisj j k hjk) hmeas

end MeasureValuation

/-- A normalized cake valuation: each agent values the whole cake at exactly `1`. -/
def IsNormalized {N Ω V : Type*} [One V] (cv : CakeValuation N Ω V) : Prop :=
  ∀ i : N, cv.val i Set.univ = 1

namespace IsNormalized

/-- For `MeasureValuation`, normalization is equivalent to every agent's measure being
    a probability measure. -/
lemma iff_isProbabilityMeasure {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → MeasureTheory.Measure Ω) :
    IsNormalized (MeasureValuation μ) ↔ ∀ i, MeasureTheory.IsProbabilityMeasure (μ i) := by
  simp only [IsNormalized, MeasureValuation]
  exact ⟨fun h i => ⟨h i⟩, fun h i => (h i).measure_univ⟩

end IsNormalized

end Divisible
end FairDivision
end SocialChoice
