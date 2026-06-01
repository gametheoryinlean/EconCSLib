/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.OrdContinuous

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.Allocation

Allocation-side infrastructure for divisible goods (cake cutting).

This file contains only the share/allocation representation and measurable
partition predicates. Valuation-side material lives in `Divisible.Valuation`.
-/

namespace SocialChoice
namespace FairDivision
namespace Divisible

open MeasureTheory Set

/-- A divisible allocation assigns each agent `i : N` a piece (a measurable subset) of the
    cake `Ω`. -/
abbrev Allocation (N Ω : Type*) := SocialChoice.FairDivision.Allocation N (Set Ω)

/-- A complete divisible allocation is a measurable partition of the cake. -/
structure IsAllocation {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (A : Allocation N Ω) : Prop where
  /-- Each piece is a measurable set. -/
  measurable : ∀ i : N, MeasurableSet (A i)
  /-- Distinct agents receive disjoint pieces. -/
  disjoint   : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- Every point of the cake belongs to some agent's piece. -/
  cover      : ⋃ i : N, A i = Set.univ

namespace IsAllocation

variable {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
variable {A : Allocation N Ω}

/-- Every point of the cake belongs to the piece of some agent. -/
lemma mem_iUnion (ha : IsAllocation A) (x : Ω) : ∃ i : N, x ∈ A i := by
  have : x ∈ ⋃ i, A i := ha.cover ▸ Set.mem_univ x
  exact Set.mem_iUnion.mp this

end IsAllocation

/-- A **contiguous allocation** on `ℝ`: each agent's piece is an interval
    (an order-connected subset of `ℝ`). -/
def IsContiguousAllocation {N : Type*} (A : Allocation N ℝ) : Prop :=
  ∀ i : N, (A i).OrdConnected

end Divisible
end FairDivision
end SocialChoice
