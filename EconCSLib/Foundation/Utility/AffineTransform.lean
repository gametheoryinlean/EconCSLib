/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# EconCSLib.Foundation.Utility.AffineTransform

Positive affine transformations of utility functions and their properties.

## Main definitions

* `IsPositiveAffineOf` — `v` is a positive affine transform of `u`

## Main results

* `IsPositiveAffineOf.preserves_le` — positive affine transform preserves ≤
* `IsPositiveAffineOf.preserves_representation` — if `u` represents ≤, so does `a·u + b`
* `IsPositiveAffineOf.symm` — positive affine transform is invertible [MSZ Ex 2.19]

## References

* [MSZ] Chapter 2, Theorem 2.22
-/

section AffineTransform

variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `v` is a positive affine transformation of `u`: `v(x) = a · u(x) + b` with `a > 0`.
    Two utility functions related by a positive affine transform represent the same
    preference. [MSZ 2.22] -/
def IsPositiveAffineOf (u v : X → 𝕜) : Prop :=
  ∃ (a b : 𝕜), 0 < a ∧ ∀ x, v x = a * u x + b

/-- Positive affine transformation is reflexive (identity: a=1, b=0). -/
theorem IsPositiveAffineOf.refl (u : X → 𝕜) : IsPositiveAffineOf u u :=
  ⟨1, 0, one_pos, fun x => by ring⟩

/-- Positive affine transformation is transitive. -/
theorem IsPositiveAffineOf.trans {u v w : X → 𝕜}
    (h₁ : IsPositiveAffineOf u v) (h₂ : IsPositiveAffineOf v w) :
    IsPositiveAffineOf u w := by
  obtain ⟨a₁, b₁, ha₁, hv⟩ := h₁
  obtain ⟨a₂, b₂, ha₂, hw⟩ := h₂
  exact ⟨a₂ * a₁, a₂ * b₁ + b₂, mul_pos ha₂ ha₁, fun x => by rw [hw, hv]; ring⟩

/-- A positive affine transform preserves the order: `u x ≤ u y ↔ v x ≤ v y`. -/
theorem IsPositiveAffineOf.preserves_le {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) (x y : X) :
    u x ≤ u y ↔ v x ≤ v y := by
  obtain ⟨a, b, ha, hv⟩ := h
  simp only [hv]
  constructor
  · intro hle
    have := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
    linarith
  · intro hle
    have : a * u x + b ≤ a * u y + b := hle
    have : a * u x ≤ a * u y := by linarith
    exact le_of_mul_le_mul_left this ha

/-- If `u` represents a preference, so does any positive affine transform. [MSZ 2.22] -/
theorem IsPositiveAffineOf.preserves_representation [Preorder X] {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) (hrep : RepresentsPreference u) :
    RepresentsPreference v where
  le_iff a b := by
    rw [← h.preserves_le]
    exact hrep.le_iff a b

/-- Positive affine transformation is symmetric (invertible). [MSZ Ex 2.19]
    If `v(x) = a·u(x) + b` with `a > 0`, then `u(x) = (1/a)·v(x) + (-b/a)`. -/
theorem IsPositiveAffineOf.symm {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) : IsPositiveAffineOf v u := by
  obtain ⟨a, b, ha, hv⟩ := h
  exact ⟨1/a, -b/a, div_pos one_pos ha, fun x => by
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp [ha']; linarith [hv x]⟩

end AffineTransform
