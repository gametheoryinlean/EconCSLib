/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.AffineTransform
import EconCSLib.Foundation.Preference
import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.Math.Simplex
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# EconCSLib.Foundation.Utility.Basic

Risk attitudes and their characterizations.

## Main definitions

* `IsAffineUtility` — utility function of the form `u(x) = a·x + b`
* `IsRiskNeutral` — utility preserves expected values
* `IsLinearUtility` — utility linear over lottery mixtures

## Main results

* `IsAffineUtility.isRiskNeutral` — affine utility → risk neutral [MSZ 2.27]
* `IsRiskNeutral.isAffine` — risk neutral → affine utility [MSZ 2.27]

## References

* [MSZ] Chapter 2, Definitions 2.24–2.27
-/

/-! ### Risk attitudes -/

section RiskAttitude

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
set_option linter.unusedSectionVars false

/-- A utility function is affine (linear + constant): `u(x) = a·x + b`.
    An agent with an affine utility function is risk neutral. [MSZ 2.24] -/
def IsAffineUtility (u : 𝕜 → 𝕜) : Prop :=
  ∃ (a b : 𝕜), ∀ x, u x = a * x + b

/-- Risk neutrality for lotteries over a finite index set `I`:
    `u(∑ pᵢ·xᵢ) = ∑ pᵢ·u(xᵢ)`.
    Equivalent to `u` being affine. [MSZ 2.27] -/
def IsRiskNeutral {I : Type*} [Fintype I] (u : 𝕜 → 𝕜) : Prop :=
  ∀ (p : stdSimplex 𝕜 I) (x : I → 𝕜),
    u (wsum p x) = wsum p (u ∘ x)

/-- An affine utility function is risk neutral. [MSZ 2.27, easy direction] -/
theorem IsAffineUtility.isRiskNeutral {I : Type*} [Fintype I] {u : 𝕜 → 𝕜}
    (h : IsAffineUtility u) : IsRiskNeutral (I := I) u := by
  obtain ⟨a, b, hu⟩ := h
  intro p x
  -- Write u ∘ x as a • x + const b, then use wsum linearity lemmas.
  have hcomp : u ∘ x = a • x + (fun _ => b) := by
    funext i; simp [Function.comp, hu, Pi.smul_apply, smul_eq_mul]
  rw [hcomp, wsum_add, wsum_smul, wsum_const, hu]

/-- Risk neutrality implies affine utility. [MSZ 2.27, hard direction]
    Requires `|I| ≥ 2` so that non-trivial distributions exist. -/
theorem IsRiskNeutral.isAffine {I : Type*} [Fintype I] [Nontrivial I] {u : 𝕜 → 𝕜}
    (h : IsRiskNeutral (I := I) u) : IsAffineUtility u := by
  classical
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne I
  -- Step 1: derive convex combination property from risk neutrality
  -- u(t·a + (1-t)·b) = t·u(a) + (1-t)·u(b) for t ∈ [0,1]
  have conv : ∀ (t : 𝕜) (_ : 0 ≤ t) (_ : t ≤ 1) (a b : 𝕜),
      u (t * a + (1 - t) * b) = t * u a + (1 - t) * u b := by
    intro t ht₀ ht₁ a b
    let p := Lottery.mix t ht₀ ht₁ (Lottery.pure (𝕜 := 𝕜) i₀) (Lottery.pure i₁)
    let f : I → 𝕜 := fun i => if i = i₀ then a else b
    have hL : wsum p f = t * a + (1 - t) * b := by
      change Lottery.expectedValue p f = _
      rw [Lottery.expectedValue_mix]
      simp [Lottery.expectedValue_pure, f, hne.symm]
    have hR : wsum p (u ∘ f) = t * u a + (1 - t) * u b := by
      change Lottery.expectedValue p (u ∘ f) = _
      rw [Lottery.expectedValue_mix]
      simp [Lottery.expectedValue_pure, Function.comp, f, hne.symm]
    rw [← hL, h p f, hR]
  -- Step 2: u(x) = (u 1 - u 0) · x + u 0 for all x
  refine ⟨u 1 - u 0, u 0, fun x => ?_⟩
  -- Case x ∈ [0,1]: u(x·1 + (1-x)·0) = x·u(1) + (1-x)·u(0)
  -- Case x > 1: u((1/x)·x + (1-1/x)·0) = (1/x)·u(x) + (1-1/x)·u(0), solve for u(x)
  -- Case x < 0: u(0) = (1/2)·u(x) + (1/2)·u(-x), with u(-x) known since -x > 0
  suffices ∀ y : 𝕜, 0 ≤ y → u y = (u 1 - u 0) * y + u 0 by
    by_cases hx : 0 ≤ x
    · exact this x hx
    · push_neg at hx
      have hmx := this (-x) (le_of_lt (neg_pos.mpr hx))
      have h_mid := conv (1 / 2) (by norm_num) (by norm_num) x (-x)
      have : (1 : 𝕜) / 2 * x + (1 - 1 / 2) * -x = 0 := by ring
      rw [this] at h_mid
      linarith
  intro y hy
  rcases eq_or_lt_of_le hy with rfl | hy_pos
  · simp
  rcases le_or_gt y 1 with hy1 | hy1
  · -- y ∈ (0, 1]
    have := conv y hy hy1 1 0
    simp at this; linarith
  · -- y > 1
    have h_inv := conv (1 / y) (le_of_lt (div_pos one_pos hy_pos))
      ((div_le_one hy_pos).mpr (le_of_lt hy1)) y 0
    simp at h_inv
    have hyne : y ≠ 0 := ne_of_gt hy_pos
    field_simp at h_inv ⊢; linarith

end RiskAttitude
