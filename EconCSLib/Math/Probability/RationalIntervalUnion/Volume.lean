/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.RationalIntervalUnion
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Volume semantics of finite rational interval unions

This analytic leaf interprets `RationalIntervalUnion.Bounds` as closed subsets
of the real unit interval. It proves that the executable inclusion-exclusion
algorithm computes their original unit-interval volume, including overlapping,
duplicate, clipped, reversed, singleton, and endpoint-touching descriptions.
Consequently the computed rational lies in `[0, 1]`.

The non-atomic measure remains the denotation. This module supplies an exact
evaluator only for the finite event-description language defined by the pure
module; it does not decide membership in an arbitrary real set.
-/

open MeasureTheory
open scoped unitInterval

namespace RationalIntervalUnion

/-- A closed rational interval, intersected with the real unit interval. -/
def intervalEvent (bounds : Bounds) : Set (Set.Icc (0 : ℝ) 1) :=
  {x | (bounds.1 : ℝ) ≤ x.val ∧ x.val ≤ (bounds.2 : ℝ)}

/-- Event represented by a finite union of closed rational intervals. -/
def event : List Bounds → Set (Set.Icc (0 : ℝ) 1)
  | [] => ∅
  | head :: tail => intervalEvent head ∪ event tail

/-- Every represented rational interval is measurable. -/
theorem intervalEvent_measurable (bounds : Bounds) :
    MeasurableSet (intervalEvent bounds) :=
  (measurableSet_Ici.preimage measurable_subtype_coe).inter
    (measurableSet_Iic.preimage measurable_subtype_coe)

/-- Every finite represented union is measurable. -/
theorem event_measurable (intervals : List Bounds) : MeasurableSet (event intervals) := by
  induction intervals with
  | nil => exact MeasurableSet.empty
  | cons head tail ih => exact (intervalEvent_measurable head).union ih

/-- Computing endpoint intersections preserves the represented event. -/
theorem intervalEvent_intersect (left right : Bounds) :
    intervalEvent (intersect left right) = intervalEvent left ∩ intervalEvent right := by
  ext x
  simp only [intervalEvent, intersect, Set.mem_setOf_eq, Rat.cast_max, Rat.cast_min,
    max_le_iff, le_min_iff, Set.mem_inter_iff]
  tauto

/-- Intersecting a descriptor with a finite union maps over its bounds. -/
theorem event_map_intersect (head : Bounds) (tail : List Bounds) :
    event (tail.map (intersect head)) = intervalEvent head ∩ event tail := by
  induction tail with
  | nil => simp [event]
  | cons other tail ih =>
    simp only [List.map_cons, event, intervalEvent_intersect, ih,
      Set.inter_union_distrib_left]

/-- The clipped rational length equals the original unit-interval volume. -/
theorem intervalMass_eq_volume (bounds : Bounds) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).real (intervalEvent bounds) =
      (intervalMass bounds : ℝ) := by
  have himage : Subtype.val '' intervalEvent bounds =
      Set.Icc (max 0 (bounds.1 : ℝ)) (min 1 (bounds.2 : ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨max_le y.property.1 hy.1, le_min y.property.2 hy.2⟩
    · rintro ⟨hl, hu⟩
      exact ⟨⟨x, (le_max_left _ _).trans hl, hu.trans (min_le_left _ _)⟩,
        ⟨(le_max_right _ _).trans hl, hu.trans (min_le_right _ _)⟩, rfl⟩
  rw [Measure.real, unitInterval.volume_apply, himage, Real.volume_Icc,
    ENNReal.toReal_ofReal']
  simp [intervalMass, Rat.cast_max, Rat.cast_min, max_comm]

/-- The executable inclusion-exclusion value is the original non-atomic
probability. No disjointness or endpoint-order certificate is required. -/
theorem probability_eq_volume (intervals : List Bounds) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).real (event intervals) =
      (probability intervals : ℝ) := by
  induction intervals using probability.induct with
  | case1 => simp [event, probability]
  | case2 head tail ihTail ihInter =>
    simp only [List.attach_map_val] at ihInter
    have h := measureReal_union_add_inter
      (μ := (volume : Measure (Set.Icc (0 : ℝ) 1)))
      (s := intervalEvent head) (event_measurable tail)
    rw [← event_map_intersect, ihInter, intervalMass_eq_volume, ihTail] at h
    simp only [event, probability, Rat.cast_sub, Rat.cast_add]
    linarith

/-- The extended-real volume is the nonnegative embedding of the exact result. -/
theorem volume_event (intervals : List Bounds) :
    (volume : Measure (Set.Icc (0 : ℝ) 1)) (event intervals) =
      ENNReal.ofReal (probability intervals : ℝ) := by
  rw [← probability_eq_volume, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The exact inclusion-exclusion result is nonnegative. -/
theorem probability_nonneg (intervals : List Bounds) : 0 ≤ probability intervals := by
  have h : (0 : ℝ) ≤ (probability intervals : ℝ) := by
    rw [← probability_eq_volume]
    exact measureReal_nonneg
  exact_mod_cast h

/-- The exact inclusion-exclusion result is at most one. -/
theorem probability_le_one (intervals : List Bounds) : probability intervals ≤ 1 := by
  have h : (probability intervals : ℝ) ≤ 1 := by
    rw [← probability_eq_volume]
    exact measureReal_le_one
  exact_mod_cast h

end RationalIntervalUnion
