/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Valuation

Cardinal valuations for indivisible goods allocation.

## Main definitions

* `SocialChoice.FairDivision.Indivisible.Valuation N G` — abstract valuation: assigns a real value to each
  agent-bundle pair
* `SocialChoice.FairDivision.Indivisible.AdditiveValuation N G` — additive valuation: determined by per-item weights
* `SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation` — lifts an additive valuation to a `Valuation`

## Namespace

All types are scoped under `SocialChoice.FairDivision.Indivisible` to avoid
clashing with `Mathlib.RingTheory.Valuation.Basic` and to keep the public API
under the canonical social-choice hierarchy.

## Design

`Valuation` is real-valued. This keeps the public fair-division API aligned with the
bundled cardinal interfaces and avoids carrying avoidable ordered-algebra typeclass
parameters through every theorem statement.

`AdditiveValuation` specializes to the important case `v_i(S) = Σ_{g ∈ S} w_i(g)`.

Note: `Indivisible.Valuation N G` maps bundles of *goods* — do not conflate with
`CoalitionalGame`'s characteristic function (coalitions of *agents*) or Mathlib's
ring-theoretic `Valuation` (ring → ordered monoid).

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
-/

open BigOperators Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

/-! ### Abstract valuation -/

/-- An abstract valuation assigns a real value to each agent-bundle pair.

    `val i S` is the value agent `i` assigns to bundle `S`.

    Lives in `namespace SocialChoice.FairDivision.Indivisible` to avoid clash
    with Mathlib's ring-theoretic `Valuation`. -/
structure Valuation (N G : Type*) where
  /-- The valuation function: agent × bundle → value. -/
  val : N → Finset G → ℝ

/-! ### Additive valuation -/

/-- An additive valuation is determined by per-item weights.

    `weight i g` is the value agent `i` assigns to good `g` individually.
    The bundle value is `v_i(S) = Σ_{g ∈ S} weight i g`. -/
structure AdditiveValuation (N G : Type*) where
  /-- Per-item weight: agent × good → value. -/
  weight : N → G → ℝ

namespace AdditiveValuation

variable {N G : Type*}

/-- Lift an additive valuation to an abstract `Valuation`.

    `(w.toValuation).val i S = Σ_{g ∈ S} w.weight i g`. -/
def toValuation (w : AdditiveValuation N G) : Valuation N G :=
  ⟨fun i S => ∑ g ∈ S, w.weight i g⟩

/-- The value of the empty bundle is zero for additive valuations. -/
@[simp]
lemma toValuation_empty (w : AdditiveValuation N G) (i : N) :
    w.toValuation.val i ∅ = 0 := by
  simp [toValuation]

/-- Additive valuation of a union of disjoint bundles splits as a sum. -/
lemma toValuation_union [DecidableEq G]
    (w : AdditiveValuation N G) (i : N) (S T : Finset G) (h : Disjoint S T) :
    w.toValuation.val i (S ∪ T) = w.toValuation.val i S + w.toValuation.val i T := by
  simp [toValuation, Finset.sum_union h]

/-- Additive valuations with nonnegative weights are monotone: sub-bundles have no
    greater value than their supersets. -/
lemma toValuation_mono [DecidableEq G]
    (w : AdditiveValuation N G)
    (hnn : ∀ (i : N) (g : G), 0 ≤ w.weight i g)
    (i : N) {S T : Finset G} (h : T ⊆ S) :
    w.toValuation.val i T ≤ w.toValuation.val i S := by
  simp only [toValuation]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hnn i x)

end AdditiveValuation

end Indivisible
end FairDivision
end SocialChoice
