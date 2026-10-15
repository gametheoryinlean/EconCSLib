/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite-dimensional bounded polyhedra

This module proves the finite-dimensional bounded case of the
Minkowski-Weyl theorem needed by EconCSLib: a bounded solution set of finitely
many weak linear inequalities over `ℝ` is the convex hull of finitely many
points.

The proof is organized around extreme points. At an extreme point, the active
constraint functionals span the full dual space; otherwise a nonzero common
kernel direction gives two distinct nearby feasible points whose midpoint is
the alleged extreme point. Since a finite constraint family has only finitely
many active sets, the extreme-point set is finite. Krein-Milman and closedness
of the convex hull of a finite set then give the exact finite convex-hull
representation.

## Main declarations

* `finiteDotLinear` - a finite coefficient vector as a linear functional.
* `FiniteLinearInequalitySet` - a finite system `b k ≤ L k x`.
* `finiteLinearInequalitySet_extremePoints_finite` - finiteness of its extreme
  points.
* `finiteLinearInequalitySet_eq_convexHull_finset` - a bounded finite
  H-polyhedron is the convex hull of a finite set.

## References

* [Rockafellar, *Convex Analysis*, Theorem 19.1]
* [Ziegler, *Lectures on Polytopes*, Section 1.1]
-/

open Finset Set

namespace EconCSLib.Convex

variable {E K : Type*}

/-- The finite dot product with coefficient vector `a`, bundled as a linear
functional on the coordinate space `I → ℝ`. -/
def finiteDotLinear {I : Type*} [Fintype I]
    (a : I → ℝ) : Module.Dual ℝ (I → ℝ) where
  toFun x := ∑ i, a i * x i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_left_comm]

@[simp]
theorem finiteDotLinear_apply {I : Type*} [Fintype I]
    (a x : I → ℝ) :
    finiteDotLinear a x = ∑ i, a i * x i :=
  rfl

/-- The solution set of the weak linear inequalities `b k ≤ L k x`. -/
def FiniteLinearInequalitySet [AddCommGroup E] [Module ℝ E] [Fintype K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) : Set E :=
  {x | ∀ k, b k ≤ L k x}

/-- The constraints active at `x`. -/
noncomputable def activeConstraints
    [AddCommGroup E] [Module ℝ E] [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) (x : E) : Finset K :=
  Finset.univ.filter fun k => L k x = b k

@[simp]
theorem mem_activeConstraints
    [AddCommGroup E] [Module ℝ E] [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) (x : E) (k : K) :
    k ∈ activeConstraints L b x ↔ L k x = b k := by
  simp [activeConstraints]

/-- A finite linear inequality set is convex. -/
theorem finiteLinearInequalitySet_convex
    [AddCommGroup E] [Module ℝ E] [Fintype K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) :
    Convex ℝ (FiniteLinearInequalitySet L b) := by
  intro x hx y hy a c ha hc hac k
  rw [map_add, map_smul, map_smul]
  calc
    b k = (a + c) * b k := by rw [hac, one_mul]
    _ = a * b k + c * b k := by ring
    _ ≤ a * L k x + c * L k y :=
      add_le_add (mul_le_mul_of_nonneg_left (hx k) ha)
        (mul_le_mul_of_nonneg_left (hy k) hc)

/-- A finite linear inequality set is closed in a finite-dimensional real
normed vector space. -/
theorem finiteLinearInequalitySet_isClosed
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) :
    IsClosed (FiniteLinearInequalitySet L b) := by
  rw [FiniteLinearInequalitySet]
  rw [show {x : E | ∀ k : K, b k ≤ L k x} =
      ⋂ k : K, {x : E | b k ≤ L k x} by ext; simp]
  apply isClosed_iInter
  intro k
  exact IsClosed.preimage (L k).continuous_of_finiteDimensional isClosed_Ici

private theorem exists_common_kernel_direction_of_activeSpan_ne_top
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) (x : E)
    (hspan : Submodule.span ℝ (L '' (activeConstraints L b x : Set K)) ≠ ⊤) :
    ∃ d : E, d ≠ 0 ∧
      ∀ k ∈ activeConstraints L b x, L k d = 0 := by
  have hnotsep :
      ¬ ∀ d : E, d ≠ 0 →
        ∃ f ∈ L '' (activeConstraints L b x : Set K), f d ≠ 0 := by
    intro hsep
    exact hspan (Submodule.span_eq_top_of_ne_zero hsep)
  push Not at hnotsep
  obtain ⟨d, hd, hzero⟩ := hnotsep
  refine ⟨d, hd, ?_⟩
  intro k hk
  exact hzero (L k) ⟨k, hk, rfl⟩

private theorem exists_two_sided_feasible_perturbation
    [AddCommGroup E] [Module ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ)
    {x d : E}
    (hx : x ∈ FiniteLinearInequalitySet L b)
    (hdactive : ∀ k ∈ activeConstraints L b x, L k d = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      x + ε • d ∈ FiniteLinearInequalitySet L b ∧
      x - ε • d ∈ FiniteLinearInequalitySet L b := by
  classical
  let inactive : Finset K :=
    Finset.univ.filter fun k => L k x ≠ b k
  by_cases hinactive : inactive.Nonempty
  · let radius : K → ℝ :=
      fun k => (L k x - b k) / (|L k d| + 1)
    have hradius_pos : ∀ k ∈ inactive, 0 < radius k := by
      intro k hk
      have hkne : L k x ≠ b k := (Finset.mem_filter.mp hk).2
      have hstrict : b k < L k x := lt_of_le_of_ne (hx k) (Ne.symm hkne)
      dsimp [radius]
      positivity
    let m : ℝ := inactive.inf' hinactive radius
    have hm_pos : 0 < m := by
      rw [show m = inactive.inf' hinactive radius from rfl]
      exact (Finset.lt_inf'_iff hinactive).2 hradius_pos
    let ε : ℝ := m / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, hε, ?_, ?_⟩
    · intro k
      by_cases hkactive : k ∈ activeConstraints L b x
      · have hkx : L k x = b k := (mem_activeConstraints L b x k).1 hkactive
        rw [map_add, map_smul, hdactive k hkactive, smul_eq_mul, mul_zero, add_zero, hkx]
      · have hkne : L k x ≠ b k := by
          simpa [mem_activeConstraints] using hkactive
        have hkinactive : k ∈ inactive := by simp [inactive, hkne]
        have hm_le : m ≤ radius k :=
          Finset.inf'_le radius hkinactive
        have hεradius : ε < radius k := by
          dsimp [ε]
          linarith [hm_pos]
        have habs : ε * |L k d| < L k x - b k := by
          have hdenom : 0 < |L k d| + 1 := by positivity
          have hmul : ε * (|L k d| + 1) < L k x - b k := by
            apply (lt_div_iff₀ hdenom).mp
            simpa [radius] using hεradius
          have hεnonneg : 0 ≤ ε := hε.le
          nlinarith [abs_nonneg (L k d)]
        have hlower : -|L k d| ≤ L k d := neg_abs_le (L k d)
        rw [map_add, map_smul, smul_eq_mul]
        nlinarith
    · intro k
      by_cases hkactive : k ∈ activeConstraints L b x
      · have hkx : L k x = b k := (mem_activeConstraints L b x k).1 hkactive
        rw [map_sub, map_smul, hdactive k hkactive, smul_eq_mul, mul_zero, sub_zero, hkx]
      · have hkne : L k x ≠ b k := by
          simpa [mem_activeConstraints] using hkactive
        have hkinactive : k ∈ inactive := by simp [inactive, hkne]
        have hm_le : m ≤ radius k :=
          Finset.inf'_le radius hkinactive
        have hεradius : ε < radius k := by
          dsimp [ε]
          linarith [hm_pos]
        have habs : ε * |L k d| < L k x - b k := by
          have hdenom : 0 < |L k d| + 1 := by positivity
          have hmul : ε * (|L k d| + 1) < L k x - b k := by
            apply (lt_div_iff₀ hdenom).mp
            simpa [radius] using hεradius
          have hεnonneg : 0 ≤ ε := hε.le
          nlinarith [abs_nonneg (L k d)]
        have hupper : L k d ≤ |L k d| := le_abs_self (L k d)
        rw [map_sub, map_smul, smul_eq_mul]
        nlinarith
  · have hallactive : ∀ k : K, k ∈ activeConstraints L b x := by
      intro k
      by_contra hk
      have hkne : L k x ≠ b k := by
        simpa [mem_activeConstraints] using hk
      exact hinactive ⟨k, by simp [inactive, hkne]⟩
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · intro k
      have hkx : L k x = b k := (mem_activeConstraints L b x k).1 (hallactive k)
      rw [map_add, map_smul, hdactive k (hallactive k), smul_eq_mul,
        mul_zero, add_zero, hkx]
    · intro k
      have hkx : L k x = b k := (mem_activeConstraints L b x k).1 (hallactive k)
      rw [map_sub, map_smul, hdactive k (hallactive k), smul_eq_mul,
        mul_zero, sub_zero, hkx]

/-- At an extreme point of a finite linear inequality set, the active
constraint functionals span the entire dual space. -/
theorem activeConstraints_span_eq_top_of_mem_extremePoints
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) {x : E}
    (hx : x ∈ (FiniteLinearInequalitySet L b).extremePoints ℝ) :
    Submodule.span ℝ (L '' (activeConstraints L b x : Set K)) = ⊤ := by
  by_contra hspan
  obtain ⟨d, hdne, hdactive⟩ :=
    exists_common_kernel_direction_of_activeSpan_ne_top L b x hspan
  obtain ⟨ε, hε, hplus, hminus⟩ :=
    exists_two_sided_feasible_perturbation L b hx.1 hdactive
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hopen :
      x ∈ openSegment ℝ (x + ε • d) (x - ε • d) :=
    mem_openSegment_add_sub x (ε • d)
  have heq := (mem_extremePoints.mp hx).2
    (x + ε • d) hplus (x - ε • d) hminus hopen
  have hsmul : ε • d = 0 := by
    have := congrArg (fun y => y - x) heq.1
    simpa using this
  exact hdne ((smul_eq_zero.mp hsmul).resolve_left hε.ne')

private theorem eq_of_activeConstraints_eq_of_mem_extremePoints
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ)
    {x y : E}
    (hx : x ∈ (FiniteLinearInequalitySet L b).extremePoints ℝ)
    (hactive : activeConstraints L b x = activeConstraints L b y) :
    x = y := by
  let evaluation : Module.Dual ℝ E →ₗ[ℝ] ℝ := Module.Dual.eval ℝ E (x - y)
  have hgenerators :
      L '' (activeConstraints L b x : Set K) ⊆ LinearMap.ker evaluation := by
    rintro f ⟨k, hk, rfl⟩
    have hkx : L k x = b k := (mem_activeConstraints L b x k).1 hk
    have hky_mem : k ∈ activeConstraints L b y := by rw [← hactive]; exact hk
    have hky : L k y = b k := (mem_activeConstraints L b y k).1 hky_mem
    change L k (x - y) = 0
    rw [map_sub, hkx, hky, sub_self]
  have hspan_le :
      Submodule.span ℝ (L '' (activeConstraints L b x : Set K)) ≤
        LinearMap.ker evaluation :=
    Submodule.span_le.2 hgenerators
  have hspan := activeConstraints_span_eq_top_of_mem_extremePoints L b hx
  have hker : LinearMap.ker evaluation = ⊤ := by
    apply top_unique
    simpa [hspan] using hspan_le
  have hevaluation : evaluation = 0 := LinearMap.ker_eq_top.mp hker
  have heval : Module.evalEquiv ℝ E (x - y) = 0 := by
    simpa [evaluation] using hevaluation
  have hsub : x - y = 0 :=
    (Module.evalEquiv ℝ E).injective (by simpa only [map_zero] using heval)
  exact sub_eq_zero.mp hsub

/-- The extreme-point set of a finite linear inequality system is finite. -/
theorem finiteLinearInequalitySet_extremePoints_finite
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ) :
    ((FiniteLinearInequalitySet L b).extremePoints ℝ).Finite := by
  classical
  let activeMap :
      (FiniteLinearInequalitySet L b).extremePoints ℝ → Finset K :=
    fun x => activeConstraints L b x.1
  have hinjective : Function.Injective activeMap := by
    intro x y hxy
    apply Subtype.ext
    exact eq_of_activeConstraints_eq_of_mem_extremePoints L b x.2 hxy
  letI : Finite ((FiniteLinearInequalitySet L b).extremePoints ℝ) :=
    Finite.of_injective activeMap hinjective
  exact Set.finite_coe_iff.mp inferInstance

/-- A bounded solution set of finitely many weak linear inequalities in a
finite-dimensional real normed vector space is the convex hull of finitely
many points. This is the bounded H-to-V direction of Minkowski-Weyl. -/
theorem finiteLinearInequalitySet_eq_convexHull_finset
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype K] [DecidableEq K]
    (L : K → Module.Dual ℝ E) (b : K → ℝ)
    (hbounded : Bornology.IsBounded (FiniteLinearInequalitySet L b)) :
    ∃ V : Finset E,
      FiniteLinearInequalitySet L b = convexHull ℝ (V : Set E) := by
  classical
  let P := FiniteLinearInequalitySet L b
  have hclosed : IsClosed P := finiteLinearInequalitySet_isClosed L b
  have hcompact : IsCompact P :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hconvex : Convex ℝ P := finiteLinearInequalitySet_convex L b
  have hextreme : (P.extremePoints ℝ).Finite :=
    finiteLinearInequalitySet_extremePoints_finite L b
  let V : Finset E := hextreme.toFinset
  refine ⟨V, ?_⟩
  have hclosedHull : IsClosed (convexHull ℝ (P.extremePoints ℝ)) :=
    hextreme.isClosed_convexHull ℝ
  have hkrein : closure (convexHull ℝ (P.extremePoints ℝ)) = P :=
    closure_convexHull_extremePoints hcompact hconvex
  calc
    P = closure (convexHull ℝ (P.extremePoints ℝ)) := hkrein.symm
    _ = convexHull ℝ (P.extremePoints ℝ) := hclosedHull.closure_eq
    _ = convexHull ℝ (V : Set E) := by simp [V]

end EconCSLib.Convex
