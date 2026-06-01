/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Efficiency

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.Checker

Noncomputable `Bool`-valued reflection helpers for indivisible-goods fairness predicates.

For finite instances (finite agents and finite goods), these definitions package each
fairness predicate as a Boolean together with a correctness theorem (`iff`). They are
noncomputable because valuations are real-valued; they are not intended for `#eval` or
`native_decide`.

## Main definitions

* `isEnvyFree` — Boolean reflection helper for `IsEnvyFree`
* `isEF1` — Boolean reflection helper for `IsEF1`
* `isEFX` — Boolean reflection helper for `IsEFX`
* `isProportional` — Boolean reflection helper for `IsProportional`

## Main results

* `isEnvyFree_iff`, `isEF1_iff`, `isEFX_iff`, `isProportional_iff` — soundness and
  completeness of each checker.

## Typeclass requirements

* `[Fintype N]` and `[DecidableEq N]` — iterate over agents
* `[DecidableEq G]` — Finset operations on bundles (sdiff, membership)
The value codomain is fixed to `ℝ`, so no valuation-ordering typeclasses are needed.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
-/

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### Envy-freeness reflection -/

/-- Noncomputable envy-free Boolean reflection helper.
    Returns `true` iff `A` is envy-free under valuation `v`. -/
noncomputable def isEnvyFree [Fintype N]
    (v : Valuation N G) (A : Allocation N G) : Bool :=
  decide (∀ i j : N, v.val i (A j) ≤ v.val i (A i))

/-- The envy-free checker is sound and complete. -/
theorem isEnvyFree_iff [Fintype N]
    (v : Valuation N G) (A : Allocation N G) :
    isEnvyFree v A = true ↔ IsEnvyFree v A := by
  simp [isEnvyFree, IsEnvyFree, SocialChoice.FairDivision.IsEnvyFree]

/-! ### EF1 reflection -/

/-- Noncomputable EF1 Boolean reflection helper.
    Returns `true` iff `A` is envy-free up to one good under valuation `v`. -/
noncomputable def isEF1 [Fintype N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) : Bool :=
  decide (∀ i j : N, i ≠ j → (A j).Nonempty →
    ∃ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i))

/-- The EF1 checker is sound and complete. -/
theorem isEF1_iff [Fintype N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) :
    isEF1 v A = true ↔ IsEF1 v A := by
  simp [isEF1, IsEF1]

/-! ### EFX reflection -/

/-- Noncomputable EFX Boolean reflection helper.
    Returns `true` iff `A` is envy-free up to any good under valuation `v`. -/
noncomputable def isEFX [Fintype N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) : Bool :=
  decide (∀ i j : N, i ≠ j →
    ∀ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i))

/-- The EFX checker is sound and complete. -/
theorem isEFX_iff [Fintype N] [DecidableEq N] [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) :
    isEFX v A = true ↔ IsEFX v A := by
  simp [isEFX, IsEFX]

/-! ### Proportionality reflection -/

/-- Noncomputable proportionality Boolean reflection helper for `n` agents.
    Returns `true` iff every agent's bundle value is ≥ 1/n of the total.

    The value codomain is fixed to `ℝ`, so this is noncomputable. -/
noncomputable def isProportional [Fintype N] (n : ℕ)
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Bool :=
  decide (∀ i : N, v.val i allGoods ≤ (n : ℝ) * v.val i (A i))

/-- The proportionality checker is sound and complete. -/
theorem isProportional_iff [Fintype N] (n : ℕ)
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) :
    isProportional n v allGoods A = true ↔ IsProportional n v allGoods A := by
  simp [isProportional, IsProportional, SocialChoice.FairDivision.IsProportional]

end Indivisible
end FairDivision
end SocialChoice
