/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# EconCSLib.Math.Simplex

Generic utilities for working with the standard simplex `stdSimplex 𝕜 I`.

This module is neutral shared infrastructure: it provides simplex-indexed
affine combinations and weighted sums, without any game-specific
interpretation. Strategic games, lotteries, and utility theory all build on
these lemmas.

## Main definitions

* `stdSimplex.affineCombination` — affine combination using simplex weights
* `wsum` — weighted sum/dot product: `∑ᵢ xᵢ · f(i)` for `x : stdSimplex 𝕜 I`

## Main results

* `wsum_const` — weighted sum of a constant equals the constant
* `wsum_le_wsum` — monotonicity: pointwise `≤` implies weighted-sum `≤`
* `wsum_nonneg` — non-negativity: non-negative summands give non-negative total
* `wsum_add` — weighted sums distribute over addition
* `wsum_smul` — weighted sums distribute over scalar multiplication
* `wsum_wsum_comm` — exchange order of iterated weighted sums
* `wsum_pure` — a point mass evaluates the selected coordinate

## Attribution

Adapted from `GameTheory/Simplex.lean` and helper lemmas in
`GameTheory/Zerosum.lean` from
[math-xmum/gametheory](https://github.com/math-xmum/gametheory).
-/

open Finset BigOperators Matrix

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {I : Type*} [Fintype I]

set_option linter.unusedSectionVars false

namespace stdSimplex

/-- Affine combination of a finite family of points using simplex weights.

This is a thin wrapper around Mathlib's `Finset.affineCombination`, specialized
to weights coming from `stdSimplex`. -/
noncomputable def affineCombination {k V P I : Type*}
    [Ring k] [PartialOrder k] [Fintype I]
    [AddCommGroup V] [Module k V] [AddTorsor V P]
    (x : stdSimplex k I) (p : I → P) : P :=
  Finset.univ.affineCombination k p x

/-- In a module, simplex affine combinations are Mathlib finite linear combinations. -/
@[simp]
theorem affineCombination_eq_linearCombination {k V I : Type*}
    [Ring k] [PartialOrder k] [Fintype I]
    [AddCommGroup V] [Module k V]
    (x : stdSimplex k I) (p : I → V) :
    affineCombination x p = Fintype.linearCombination k p x := by
  simp [affineCombination, Fintype.linearCombination_apply,
    Finset.affineCombination_eq_linear_combination, stdSimplex.sum_eq_one x]

end stdSimplex

/-- Weighted sum of `f` with weights from a simplex element `x`.
    Thin `abbrev` over Mathlib's finite dot product `⬝ᵥ`: definitionally equal,
    so `simp [wsum]` (or no unfold at all) switches between the two forms.
    Kept as a named concept because the simplex-specific lemmas below
    (`wsum_const`, `wsum_le_wsum`, `wsum_nonneg`, `wsum_pure`) depend on
    `∑ x = 1` or `x ≥ 0` and have no generic `dotProduct` analogue. -/
abbrev wsum (x : stdSimplex 𝕜 I) (f : I → 𝕜) : 𝕜 :=
  x ⬝ᵥ f

/-- Weighted sum of a constant equals the constant. -/
theorem wsum_const (x : stdSimplex 𝕜 I) (c : 𝕜) :
    wsum x (fun _ => c) = c := by
  simp [wsum, dotProduct, ← Finset.sum_mul]

/-- Weighted sum is monotone: pointwise `≤` implies `wsum ≤`. -/
theorem wsum_le_wsum (x : stdSimplex 𝕜 I) {f g : I → 𝕜}
    (h : ∀ i, f i ≤ g i) : wsum x f ≤ wsum x g := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (h i) (x.property.1 i)

/-- Weighted sum of non-negative values is non-negative. -/
theorem wsum_nonneg (x : stdSimplex 𝕜 I) {f : I → 𝕜}
    (h : ∀ i, 0 ≤ f i) : 0 ≤ wsum x f := by
  calc 0 = wsum x (fun _ => (0 : 𝕜)) := (wsum_const x 0).symm
    _ ≤ wsum x f := wsum_le_wsum x (fun i => by linarith [h i])

/-- Weighted sum of strictly-positive values is strictly positive.

    Some coordinate `a` of any simplex point is strictly positive (since
    `∑ x = 1`), and the corresponding `x_a · f a` summand is strictly
    positive while every other summand is non-negative. -/
theorem wsum_pos (x : stdSimplex 𝕜 I) {f : I → 𝕜}
    (hf : ∀ i, 0 < f i) : 0 < wsum x f := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, 0 < x.val a := by
    by_contra hAll
    push_neg at hAll
    have hzero : ∀ i, x.val i = 0 :=
      fun i => le_antisymm (hAll i) (x.property.1 i)
    have hsum_zero : (∑ i, x.val i) = 0 := by simp_rw [hzero]; simp
    exact zero_ne_one (hsum_zero.symm.trans x.property.2)
  change 0 < ∑ b, x.val b * f b
  have hle : ∀ b ∈ (Finset.univ : Finset I), (0 : 𝕜) ≤ x.val b * f b :=
    fun b _ => mul_nonneg (x.property.1 b) (hf b).le
  have hpos : ∃ b ∈ (Finset.univ : Finset I), (0 : 𝕜) < x.val b * f b :=
    ⟨a, Finset.mem_univ _, mul_pos ha (hf a)⟩
  calc (0 : 𝕜)
      = ∑ _ : I, (0 : 𝕜) := by simp
    _ < ∑ b, x.val b * f b := Finset.sum_lt_sum hle hpos

/-- Weighted sum respects `≥`. -/
theorem wsum_ge_wsum (x : stdSimplex 𝕜 I) {f g : I → 𝕜}
    (h : ∀ i, f i ≥ g i) : wsum x f ≥ wsum x g :=
  wsum_le_wsum x h

/-- Weighted sum is linear over addition. -/
theorem wsum_add (x : stdSimplex 𝕜 I) (f g : I → 𝕜) :
    wsum x (f + g) = wsum x f + wsum x g := by
  simp [wsum, dotProduct, mul_add, Finset.sum_add_distrib]

/-- Weighted sum commutes with scalar multiplication. -/
theorem wsum_smul (x : stdSimplex 𝕜 I) (c : 𝕜) (f : I → 𝕜) :
    wsum x (c • f) = c * wsum x f := by
  simp [wsum, dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum]

/-! ### Convex combination of two simplex points (`mix`) -/

/-- Convex combination of two simplex points: `mix α hα₀ hα₁ x y = α·x + (1-α)·y`.

This is the basic vocabulary for compound lotteries and for any inductive
argument that interpolates between two mixed strategies (Loomis, Sion,
fictitious play). The hypotheses are passed as plain `(α : 𝕜) (hα₀ : 0 ≤ α)
(hα₁ : α ≤ 1)` rather than via a unit-interval subtype to match Mathlib
idioms and to keep call sites lightweight. -/
def stdSimplex.mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) : stdSimplex 𝕜 I where
  val i := α * x.val i + (1 - α) * y.val i
  property := by
    refine ⟨fun i => ?_, ?_⟩
    · have hx := x.property.1 i
      have hy := y.property.1 i
      have hα' : 0 ≤ 1 - α := by linarith
      have h₁ : 0 ≤ α * x.val i := mul_nonneg hα₀ hx
      have h₂ : 0 ≤ (1 - α) * y.val i := mul_nonneg hα' hy
      linarith
    · have hxsum := x.property.2
      have hysum := y.property.2
      have : (∑ i, (α * x.val i + (1 - α) * y.val i))
          = α * (∑ i, x.val i) + (1 - α) * (∑ i, y.val i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [this, hxsum, hysum]; ring

@[simp]
theorem stdSimplex.mix_apply (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) (i : I) :
    (stdSimplex.mix α hα₀ hα₁ x y).val i = α * x.val i + (1 - α) * y.val i := rfl

/-- Bilinearity of `wsum` over `stdSimplex.mix`:
`wsum (mix α x y) f = α · wsum x f + (1-α) · wsum y f`. -/
theorem wsum_mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) (f : I → 𝕜) :
    wsum (stdSimplex.mix α hα₀ hα₁ x y) f =
      α * wsum x f + (1 - α) * wsum y f := by
  change (∑ i, (α * x.val i + (1 - α) * y.val i) * f i)
       = α * (∑ i, x.val i * f i) + (1 - α) * (∑ i, y.val i * f i)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

/-! ### Ordered-field arithmetic helpers about convex combinations

These work directly on the scalar expression `α · x + (1-α) · y` without
reference to `stdSimplex`. They are the algebraic ingredients used to derive
strict-monotonicity facts about `wsum_mix` below. -/

/-- If `x < y` and `α < 1`, then `α·x + (1-α)·y > x`. -/
theorem linear_comb_gt_left {x y : 𝕜} (H : x < y) {α : 𝕜} (Hα : α < 1) :
    x < α * x + (1 - α) * y := by
  have hpos : 0 < 1 - α := by linarith
  have : 0 < (1 - α) * (y - x) := mul_pos hpos (by linarith)
  nlinarith

/-- If `y < x` and `0 < α`, then `α·x + (1-α)·y > y`. -/
theorem linear_comb_gt_right {x y : 𝕜} (H : y < x) {α : 𝕜} (Hα : 0 < α) :
    y < α * x + (1 - α) * y := by
  have : 0 < α * (x - y) := mul_pos Hα (by linarith)
  nlinarith

/-- Convex combination of "≥ c" and "> c" stays "> c" (provided `α ≥ 0` and `α < 1`). -/
theorem linear_comb_gt_of_ge_gt (x y c : 𝕜) (H1 : c ≤ x) (H2 : c < y)
    {α : 𝕜} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    c < α * x + (1 - α) * y := by
  have hpos : 0 < 1 - α := by linarith
  have hxc : 0 ≤ α * (x - c) := mul_nonneg hα₀ (by linarith)
  have hyc : 0 < (1 - α) * (y - c) := mul_pos hpos (by linarith)
  nlinarith

/-- Convex combination of "≤ c" and "< c" stays "< c" (provided `α ≥ 0` and `α < 1`). -/
theorem linear_comb_lt_of_le_lt (x y c : 𝕜) (H1 : x ≤ c) (H2 : y < c)
    {α : 𝕜} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    α * x + (1 - α) * y < c := by
  have hpos : 0 < 1 - α := by linarith
  have hxc : 0 ≤ α * (c - x) := mul_nonneg hα₀ (by linarith)
  have hyc : 0 < (1 - α) * (c - y) := mul_pos hpos (by linarith)
  nlinarith

/-! ### Strict monotonicity of `wsum_mix` -/

/-- `wsum` version of `linear_comb_gt_of_ge_gt`. -/
theorem wsum_mix_gt_of_ge_gt {I : Type*} [Fintype I]
    (f : I → 𝕜) (x y : stdSimplex 𝕜 I) (c : 𝕜)
    (H1 : c ≤ wsum x f) (H2 : c < wsum y f)
    {t : 𝕜} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (Ht : t < 1) :
    c < wsum (stdSimplex.mix t ht₀ ht₁ x y) f := by
  rw [wsum_mix]
  exact linear_comb_gt_of_ge_gt _ _ c H1 H2 ht₀ Ht

/-- `wsum` version of `linear_comb_lt_of_le_lt`. -/
theorem wsum_mix_lt_of_le_lt {I : Type*} [Fintype I]
    (f : I → 𝕜) (x y : stdSimplex 𝕜 I) (c : 𝕜)
    (H1 : wsum x f ≤ c) (H2 : wsum y f < c)
    {t : 𝕜} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (Ht : t < 1) :
    wsum (stdSimplex.mix t ht₀ ht₁ x y) f < c := by
  rw [wsum_mix]
  exact linear_comb_lt_of_le_lt _ _ c H1 H2 ht₀ Ht

/-! ### Neighborhood existential for convex combinations

If `c < x`, then there is an interior `t ∈ (0,1)` with `c < t·x + (1-t)·y`.
Over a general ordered field this is the elementary fact that the segment
`s ↦ s·x + (1-s)·y` from `y` to `x` stays above `c` near `s = 1`; we pick `t`
explicitly (no continuity), so it holds for any
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`. This is the key
ingredient for the Loomis-style inductive step (perturbing the optimiser a
little in the `y`-direction). -/

/-- Existence of a strictly interior `t` keeping `t·x + (1-t)·y > c`, given
`c < x`. Constructive over any ordered field: pick `t` just above the crossing
threshold `(c-y)/(x-y)` (clamped to `0`) when `y < x`, or any interior `t`
when `x ≤ y`. -/
theorem mix_gt_of_gt_nbh (x y c : 𝕜) (H : c < x) :
    ∃ t : 𝕜, 0 < t ∧ t < 1 ∧ c < t * x + (1 - t) * y := by
  rcases (lt_or_ge y x).symm with hxy | hyx
  · -- `x ≤ y`: the whole segment stays above `x > c`; any interior `t` works.
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    have hexp : (1 / 2) * x + (1 - 1 / 2) * y = x + (1 / 2) * (y - x) := by ring
    rw [hexp]
    have : 0 ≤ (1 / 2 : 𝕜) * (y - x) := mul_nonneg (by norm_num) (by linarith)
    linarith
  · -- `y < x`: pick `t` above the crossing threshold but below `1`.
    have hd : 0 < x - y := by linarith
    have hthr_lt_one : (c - y) / (x - y) < 1 := (div_lt_one hd).mpr (by linarith)
    set a : 𝕜 := max ((c - y) / (x - y)) 0 with ha
    have ha_lt_one : a < 1 := max_lt hthr_lt_one one_pos
    have ha_nonneg : 0 ≤ a := le_max_right _ _
    have hthr_le_a : (c - y) / (x - y) ≤ a := le_max_left _ _
    refine ⟨(a + 1) / 2, by linarith, by linarith, ?_⟩
    have hthr_lt_t : (c - y) / (x - y) < (a + 1) / 2 := by linarith
    have hcy : c - y < ((a + 1) / 2) * (x - y) := (div_lt_iff₀ hd).mp hthr_lt_t
    have hexp : ((a + 1) / 2) * x + (1 - (a + 1) / 2) * y
        = y + ((a + 1) / 2) * (x - y) := by ring
    rw [hexp]; linarith

/-- Dual: strictly interior `t` keeping `t·x + (1-t)·y < c`, given `x < c`.
Obtained from `mix_gt_of_gt_nbh` by negating `x, y, c`. -/
theorem mix_lt_of_lt_nbh (x y c : 𝕜) (H : x < c) :
    ∃ t : 𝕜, 0 < t ∧ t < 1 ∧ t * x + (1 - t) * y < c := by
  obtain ⟨t, ht0, ht1, hgt⟩ := mix_gt_of_gt_nbh (-x) (-y) (-c) (by linarith)
  refine ⟨t, ht0, ht1, ?_⟩
  have hneg : t * (-x) + (1 - t) * (-y) = -(t * x + (1 - t) * y) := by ring
  rw [hneg] at hgt
  linarith

/-- Exchange order of double weighted sums. -/
theorem wsum_wsum_comm {J : Type*} [Fintype J]
    (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J)
    (A : I → J → 𝕜) :
    wsum x (fun i => wsum y (A i)) = wsum y (fun j => wsum x (fun i => A i j)) := by
  simp only [wsum, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext i
  ring

/-- Point-mass simplex element at `i₀`. -/
def stdSimplex.pure [DecidableEq I] (i₀ : I) : stdSimplex 𝕜 I where
  val i := if i = i₀ then 1 else 0
  property := ⟨fun i => by simp only; split_ifs <;> norm_num,
               by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩

@[simp]
theorem stdSimplex.pure_apply [DecidableEq I] (i₀ i : I) :
    (stdSimplex.pure (𝕜 := 𝕜) i₀).val i = if i = i₀ then 1 else 0 := rfl

/-- Weighted sum at a point mass evaluates the chosen coordinate. -/
@[simp]
theorem wsum_pure_apply [DecidableEq I] (i₀ : I) (f : I → 𝕜) :
    wsum (stdSimplex.pure (𝕜 := 𝕜) i₀) f = f i₀ := by
  change (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * f i) = f i₀
  simp

/-- Weighted sum with point mass at `i₀` equals `f i₀`. Legacy form using
the inline anonymous-structure point mass. New code should prefer
`stdSimplex.pure` together with `wsum_pure_apply`. -/
theorem wsum_pure [DecidableEq I] (i₀ : I) (f : I → 𝕜) :
    wsum ⟨fun i => if i = i₀ then 1 else 0,
          fun i => by simp only; split_ifs <;> norm_num,
          by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩ f = f i₀ :=
  wsum_pure_apply (𝕜 := 𝕜) i₀ f

/-! ### Order characterization of `wsum` ranges

These lemmas turn pointwise bounds on `f : I → 𝕜` into bounds on the weighted
sum `wsum x f` over all simplex points `x`. They are the bridge that lets
Loomis-style arguments reduce a quantification over mixed strategies to a
quantification over pure responses. -/

/-- `f ≥ v` pointwise iff every simplex weighted sum is `≥ v`. -/
theorem ge_iff_simplex_ge {f : I → 𝕜} {v : 𝕜} :
    (∀ i, v ≤ f i) ↔ ∀ x : stdSimplex 𝕜 I, v ≤ wsum x f := by
  classical
  refine ⟨fun hi x => ?_, fun H i => ?_⟩
  · calc v = wsum x (fun _ => v) := (wsum_const x v).symm
      _ ≤ wsum x f := wsum_le_wsum x hi
  · simpa using H (stdSimplex.pure i)

/-- `f ≤ v` pointwise iff every simplex weighted sum is `≤ v`. -/
theorem le_iff_simplex_le {f : I → 𝕜} {v : 𝕜} :
    (∀ i, f i ≤ v) ↔ ∀ x : stdSimplex 𝕜 I, wsum x f ≤ v := by
  classical
  refine ⟨fun hi x => ?_, fun H i => ?_⟩
  · calc wsum x f ≤ wsum x (fun _ => v) := wsum_le_wsum x hi
      _ = v := wsum_const x v
  · simpa using H (stdSimplex.pure i)

/-! ### Continuity (over ℝ)

For the simplified Loomis route we need that `x ↦ wsum x f` is continuous on
`stdSimplex ℝ I`. The Mathlib instance `stdSimplex.instCompactSpace_coe` then
hands us compactness "for free", which is the workhorse for existence of
optimal mixed strategies. -/

section Topology
variable {I : Type*} [Fintype I]

/-- The `i`-th coordinate projection on `stdSimplex ℝ I` is continuous. -/
theorem stdSimplex.continuous_coord (i : I) :
    Continuous fun x : stdSimplex ℝ I => x.val i :=
  (continuous_apply i).comp continuous_subtype_val

/-- `wsum (·) f` is continuous on the standard simplex over ℝ. -/
theorem wsum_continuous (f : I → ℝ) :
    Continuous fun x : stdSimplex ℝ I => wsum x f :=
  continuous_finset_sum _ fun i _ =>
    (stdSimplex.continuous_coord i).mul continuous_const

end Topology

/-! ### Matrix-game expected payoff

`expectedPayoffMatrix` was previously in `StrategicGame.Simplex`. It is placed
here because it is a purely arithmetic definition (bilinear evaluation on the
simplex) with no strategic-game vocabulary. -/

variable {J : Type*}

open Matrix

/-- Expected payoff in a matrix game `A : I → J → 𝕜` under mixed strategies. -/
def expectedPayoffMatrix (A : I → J → 𝕜) [Fintype J]
    (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  x ⬝ᵥ fun i => y ⬝ᵥ A i

/-- Expected payoff is commutative in the summation order. -/
theorem expectedPayoffMatrix_comm {J : Type*} [Fintype J]
    (A : I → J → 𝕜) (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) :
    expectedPayoffMatrix A x y =
    y ⬝ᵥ fun j => x ⬝ᵥ fun i => A i j := by
  simpa [expectedPayoffMatrix, wsum] using wsum_wsum_comm x y A
