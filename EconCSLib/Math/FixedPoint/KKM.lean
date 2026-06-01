/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Basic
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import EconCSLib.Math.FixedPoint.Brouwer

/-!
# EconCSLib.Math.FixedPoint.KKM

The Knaster–Kuratowski–Mazurkiewicz (KKM) fixed-point lemma and its variants.

The KKM lemma is a fundamental result in combinatorial topology with broad applications
in game theory, economics, and fair division.  The **open-cover variant** stated here
is the topological engine of Stromquist's proof of envy-free existence
(Stromquist, "How to Cut a Cake Fairly", *Amer. Math. Monthly* 87, 1980, pp. 640–644).

## Setup

We work with the **standard (n-1)-simplex**
```
  stdSimplex ℝ (Fin n) = { x : Fin n → ℝ | 0 ≤ xᵢ for all i, ∑ xᵢ = 1 }
```
inside `Fin n → ℝ` with the subspace topology.  The **face opposite vertex i** is
```
  simplexFaceOpp i = { x ∈ stdSimplex ℝ (Fin n) | xᵢ = 0 }
```
the sub-face where coordinate `i` is zero.  In Stromquist's notation, `simplexFaceOpp i`
is the face `Sᵢ` where the i-th piece of cake is empty.

## Main results

* `kkm_closed_cover` — classical KKM: if the simplex is covered by `n` **closed** sets
  satisfying the KKM combinatorial condition, their common intersection is nonempty.

* `kkm_open_cover` — open-cover variant (Stromquist 1980, p.642): if the simplex is
  covered by `n` **open** sets `U₀, …, Uₙ₋₁` with `Uᵢ ∩ simplexFaceOpp i = ∅`,
  then `⋂ᵢ Uᵢ` is nonempty.

## Proof strategy

`kkm_closed_cover` is proved via Brouwer's fixed-point theorem
(`EconCSLib.Math.FixedPoint.Brouwer`): assuming no common intersection point exists,
construct a continuous self-map of the simplex that pushes each point away from
the closed sets it misses (using `Metric.infDist`), apply Brouwer to get a fixed
point, and derive a contradiction via the KKM combinatorial condition.

`kkm_open_cover` reduces to `kkm_closed_cover` via a partition of unity argument:
obtain continuous functions `φ i : C(Fin n → ℝ, ℝ)` subordinate to `U i` (via
`exists_continuous_sum_one_of_isOpen_isCompact`) with `tsupport (φ i) ⊆ U i` and
`∑ i, φ i = 1` on the simplex.  Define `F j = stdSimplex ∩ {x | ∀ k, φ k x ≤ φ j x}`.
Each `F j` is closed; the KKM condition holds because for `x ∈ face(σ)` the face-
avoidance hypothesis forces `φ k x = 0` for `k ∉ σ`, so some `j ∈ σ` attains the max.
Applying `kkm_closed_cover` yields `x` with `φ j x = 1/n > 0` for every `j`, hence
`x ∈ tsupport (φ j) ⊆ U j`.

## References

* Knaster, Kuratowski, Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe",
  *Fund. Math.* 14 (1929), pp. 132–137.
* Stromquist, "How to Cut a Cake Fairly", *Amer. Math. Monthly* 87 (1980), pp. 640–644.
* Su, "Rental Harmony: Sperner's Lemma in Fair Division", *Amer. Math. Monthly* 106 (1999).
-/

open Set Finset

variable {n : ℕ}

/-! ### Faces of the standard simplex -/

/-- The **face of the standard simplex opposite vertex `i`**: the set of simplex points
    whose `i`-th coordinate is zero.

    In cake-cutting language (Stromquist 1980): `simplexFaceOpp i` is the face `Sᵢ`
    consisting of all divisions where the `i`-th piece has measure zero (is "empty").
    The KKM open-cover condition requires `Uᵢ ∩ simplexFaceOpp i = ∅` — no division
    in `Uᵢ` has an empty `i`-th piece. -/
def simplexFaceOpp (i : Fin n) : Set (Fin n → ℝ) :=
  {x | x i = 0} ∩ stdSimplex ℝ (Fin n)

/-! ### KKM combinatorial condition -/

/-- The **KKM condition** for a cover `F : Fin n → Set _` of the standard simplex:
    for each subset `σ ⊆ Fin n`, the face of the simplex supported on `σ`
    (points with zero weight outside `σ`) is covered by `⋃_{i ∈ σ} F i`.

    This is the combinatorial heart of the KKM lemma: each face is covered by the
    subfamily indexed by that face's vertices. -/
def IsKKMCover (F : Fin n → Set (Fin n → ℝ)) : Prop :=
  ∀ (σ : Finset (Fin n)),
    (stdSimplex ℝ (Fin n) ∩ {x | ∀ i ∉ σ, x i = 0}) ⊆ ⋃ i ∈ σ, F i

/-! ### Classical KKM lemma -/

/-- **Knaster–Kuratowski–Mazurkiewicz lemma** (closed-cover version).

    If the standard `(n-1)`-simplex `stdSimplex ℝ (Fin n)` is covered by `n` **closed** sets
    `F 0, …, F (n-1)` satisfying the KKM combinatorial condition (`IsKKMCover F`), then
    their common intersection with the simplex is nonempty.

    **Proof**: By contradiction using Brouwer's fixed-point theorem.  Assuming no common
    intersection, define `g(x)(j) = (x j + infDist x (F j)) / (1 + D(x))` where
    `D(x) = ∑ j, infDist x (F j) > 0`.  Then `g` is a continuous self-map of the simplex
    with no fixed point (the fixed-point equation forces `D(x₀) = 0` via the KKM condition),
    contradicting Brouwer. -/
theorem kkm_closed_cover (hn : 0 < n)
    (F : Fin n → Set (Fin n → ℝ))
    (hclosed : ∀ i, IsClosed (F i))
    (hkkm : IsKKMCover F) :
    ∃ x ∈ stdSimplex ℝ (Fin n), ∀ i, x ∈ F i := by
  -- Each F i is nonempty: the i-th vertex e_i lies in F i by the KKM condition
  -- applied to σ = {i}.
  have hF_nonempty : ∀ i, (F i).Nonempty := by
    intro i
    let e : Fin n → ℝ := fun j => if j = i then 1 else 0
    have he_simp : e ∈ stdSimplex ℝ (Fin n) := by
      constructor
      · intro j; simp [e]; split <;> norm_num
      · simp [e, Finset.sum_ite_eq', Finset.mem_univ]
    have he_face : ∀ j ∉ ({i} : Finset (Fin n)), e j = 0 := by
      intro j hj; simp only [e]; rw [if_neg]; simp only [Finset.mem_singleton] at hj; exact hj
    have he_mem : e ∈ ⋃ j ∈ ({i} : Finset (Fin n)), F j := hkkm {i} ⟨he_simp, he_face⟩
    rw [Set.mem_iUnion₂] at he_mem
    obtain ⟨j, hj_mem, hj_F⟩ := he_mem
    simp only [Finset.mem_singleton] at hj_mem
    exact ⟨e, hj_mem ▸ hj_F⟩
  -- By contradiction: assume no point of the simplex lies in all F i.
  by_contra h_not
  push_neg at h_not
  -- h_not : ∀ x ∈ stdSimplex, ∃ i, x ∉ F i
  -- Define D(x) = ∑ i, infDist x (F i).
  let D : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Metric.infDist x (F i)
  -- D(x) > 0 for all x in the simplex.
  have hD_pos : ∀ x ∈ stdSimplex ℝ (Fin n), 0 < D x := by
    intro x hx
    obtain ⟨i, hi⟩ := h_not x hx
    have hpos : 0 < Metric.infDist x (F i) := by
      rcases lt_or_eq_of_le (Metric.infDist_nonneg (s := F i) (x := x)) with h | h
      · exact h
      · exfalso; exact hi (((hclosed i).mem_iff_infDist_zero (hF_nonempty i)).mpr h.symm)
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun j _ => Metric.infDist_nonneg) (Finset.mem_univ i))
  -- Define g : simplex → simplex by g(x)(j) = (x j + infDist x (F j)) / (1 + D(x)).
  let g : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n) := fun x =>
    ⟨fun j => (x.1 j + Metric.infDist x.1 (F j)) / (1 + D x.1), by
      constructor
      · intro j
        apply div_nonneg
        · exact add_nonneg (x.2.1 j) Metric.infDist_nonneg
        · linarith [hD_pos x.1 x.2]
      · rw [← Finset.sum_div]
        rw [div_eq_one_iff_eq (by linarith [hD_pos x.1 x.2] : (1 + D x.1) ≠ 0)]
        simp only [Finset.sum_add_distrib]
        linarith [x.2.2]⟩
  -- g is continuous.
  have hg_cont : Continuous g := by
    apply Continuous.subtype_mk
    apply continuous_pi; intro j
    apply Continuous.div
    · exact ((continuous_apply j).comp continuous_subtype_val).add
        ((Metric.continuous_infDist_pt (F j)).comp continuous_subtype_val)
    · exact continuous_const.add
        (continuous_finset_sum _ fun i _ =>
          (Metric.continuous_infDist_pt (F i)).comp continuous_subtype_val)
    · intro x; linarith [hD_pos x.1 x.2]
  -- Apply Brouwer's fixed-point theorem.
  obtain ⟨x₀, hfp⟩ := Brouwer (n := ⟨n, hn⟩) g hg_cont
  -- Extract the coordinate equation from the fixed point.
  have hfp_coord : ∀ j : Fin n,
      (x₀.1 j + Metric.infDist x₀.1 (F j)) / (1 + D x₀.1) = x₀.1 j := by
    intro j; exact congr_fun (congr_arg Subtype.val hfp) j
  -- Rearrange: x₀.val j * D(x₀) = infDist x₀.val (F j).
  have hD_ne_zero : 1 + D x₀.1 ≠ 0 := by linarith [hD_pos x₀.1 x₀.2]
  have hrearrange : ∀ j : Fin n, x₀.1 j * D x₀.1 = Metric.infDist x₀.1 (F j) := by
    intro j; have h := hfp_coord j; rw [div_eq_iff hD_ne_zero] at h; linarith
  -- Let σ = {j | x₀.val j > 0}. Since ∑ x₀.val = 1, σ is nonempty.
  let σ : Finset (Fin n) := Finset.filter (fun j => 0 < x₀.1 j) Finset.univ
  have hσ_nonempty : σ.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have hall_zero : ∀ j : Fin n, x₀.1 j = 0 := by
      intro j
      have h1 := x₀.2.1 j
      have h2 : ¬ (0 < x₀.1 j) := by
        intro hpos
        have : j ∈ σ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
        rw [h_empty] at this; simp at this
      linarith
    have hsum_zero : ∑ j : Fin n, x₀.1 j = 0 := Finset.sum_eq_zero fun j _ => hall_zero j
    have hsum_one : ∑ j : Fin n, x₀.1 j = 1 := x₀.2.2
    linarith
  -- x₀ is in the face corresponding to σ: for i ∉ σ, x₀.val i = 0.
  have hx₀_face : x₀.1 ∈ stdSimplex ℝ (Fin n) ∩ {x | ∀ i ∉ σ, x i = 0} := by
    exact ⟨x₀.2, fun i hi => by
      simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      linarith [x₀.2.1 i]⟩
  -- By the KKM condition, x₀.val ∈ ⋃ j ∈ σ, F j.
  have hx₀_union : x₀.1 ∈ ⋃ j ∈ σ, F j := hkkm σ hx₀_face
  obtain ⟨j₀, hx₀_union_j₀⟩ := Set.mem_iUnion.mp hx₀_union
  obtain ⟨hj₀_mem, hj₀_F⟩ := Set.mem_iUnion.mp hx₀_union_j₀
  -- j₀ ∈ σ means x₀.val j₀ > 0.
  have hj₀_pos : 0 < x₀.1 j₀ := by
    simp only [σ, Finset.mem_filter, Finset.mem_univ, true_and] at hj₀_mem; exact hj₀_mem
  -- Since x₀.val ∈ F j₀ and F j₀ is closed, infDist x₀.val (F j₀) = 0.
  have hinfDist_zero : Metric.infDist x₀.1 (F j₀) = 0 :=
    ((hclosed j₀).mem_iff_infDist_zero (hF_nonempty j₀)).mp hj₀_F
  -- x₀.val j₀ * D(x₀) = 0, but x₀.val j₀ > 0, so D(x₀) = 0. Contradiction.
  have hmul_zero : x₀.1 j₀ * D x₀.1 = 0 := by rw [hrearrange j₀, hinfDist_zero]
  have hD_zero : D x₀.1 = 0 := by
    rcases mul_eq_zero.mp hmul_zero with h | h
    · linarith
    · exact h
  linarith [hD_pos x₀.1 x₀.2]

/-! ### Open-cover variant (Stromquist's lemma) -/

/-- **KKM lemma — open-cover variant** (Stromquist 1980, p.642).

    If the standard `(n-1)`-simplex is covered by `n` open sets `U 0, …, U (n-1)` such that
    no `U i` intersects the face `simplexFaceOpp i` (where coordinate `i` is zero), then
    some point of the simplex lies in every `U i`.

    This is the topological engine of Stromquist's EF existence proof:
    the `U i` are the "unique preference" unions (sets of divisions where some player
    uniquely prefers piece `i`), and the point in `⋂ᵢ Uᵢ` is the fair division.

    **Proof**: Reduce to `kkm_closed_cover` via a partition of unity.
    Obtain `φ i : C(Fin n → ℝ, ℝ)` with `tsupport (φ i) ⊆ U i` and `∑ i, φ i = 1`
    on the simplex (using `exists_continuous_sum_one_of_isOpen_isCompact`).
    Set `F j = stdSimplex ∩ {x | ∀ k, φ k x ≤ φ j x}` (closed).
    For `x ∈ face(σ)`: `φ k x = 0` for `k ∉ σ` (by face-avoidance), so the max is
    attained by some `j ∈ σ`, giving `x ∈ F j`.  Hence `IsKKMCover F` holds.
    The fixed point `x` from `kkm_closed_cover` satisfies `φ j x = 1/n > 0` for all `j`,
    so `x ∈ support (φ j) ⊆ tsupport (φ j) ⊆ U j`. -/
theorem kkm_open_cover (hn : 0 < n)
    (U : Fin n → Set (Fin n → ℝ))
    (hopen : ∀ i, IsOpen (U i))
    (hface : ∀ i, simplexFaceOpp i ⊆ (U i)ᶜ)
    (hcover : stdSimplex ℝ (Fin n) ⊆ ⋃ i, U i) :
    ∃ x ∈ stdSimplex ℝ (Fin n), ∀ i, x ∈ U i := by
  -- Obtain a finite partition of unity φ i : C(Fin n → ℝ, ℝ) with:
  --   (a) tsupport (φ i) ⊆ U i
  --   (b) ∑ i, φ i = 1 on stdSimplex
  --   (c) 0 ≤ φ i x ≤ 1 for all x
  obtain ⟨φ, htsup, hsum, hnn, _⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact hopen (isCompact_stdSimplex ℝ (Fin n)) hcover
  -- Define: F j = simplex points where φ j attains the maximum among all φ k
  let F : Fin n → Set (Fin n → ℝ) :=
    fun j => stdSimplex ℝ (Fin n) ∩ {x | ∀ k : Fin n, φ k x ≤ φ j x}
  -- F j is closed: intersection of the closed simplex with a finite intersection of
  -- closed half-spaces {φ k ≤ φ j}
  have hF_closed : ∀ j, IsClosed (F j) := fun j => by
    apply IsClosed.inter (isCompact_stdSimplex ℝ (Fin n)).isClosed
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun k =>
      isClosed_le (φ k).continuous (φ j).continuous
  -- F satisfies the KKM condition
  have hF_kkm : IsKKMCover F := by
    intro σ x ⟨hx_simp, hx_zero⟩
    -- Key: for k ∉ σ, x_k = 0 forces x ∈ simplexFaceOpp k, so x ∉ U k,
    -- so x ∉ tsupport (φ k), so φ k x = 0
    have hzero : ∀ k ∉ σ, φ k x = 0 := fun k hk => by
      have hxk : x ∈ simplexFaceOpp k := ⟨hx_zero k hk, hx_simp⟩
      have hnotU : x ∉ U k := hface k hxk
      have hnotsup : x ∉ tsupport (⇑(φ k)) := fun h => hnotU (htsup k h)
      have hnotsupp : x ∉ Function.support (⇑(φ k)) :=
        fun h => hnotsup (subset_closure h)
      simpa [Function.mem_support] using hnotsupp
    -- Case σ = ∅: face(∅) ∩ simplex is empty (all coordinates = 0 but sum = 1)
    by_cases hσ : σ.Nonempty
    · -- Pick j ∈ σ that maximizes φ j x
      obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_max_image σ (fun k => φ k x) hσ
      refine mem_iUnion₂.mpr ⟨j, hj_mem, hx_simp, fun k => ?_⟩
      by_cases hk : k ∈ σ
      · exact hj_max k hk
      · rw [hzero k hk]; exact (hnn j x).1
    · -- σ = ∅ implies ∀ i, x i = 0, contradicting ∑ x i = 1
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hσ
      have h_all_zero : ∀ i : Fin n, x i = 0 :=
        fun i => hx_zero i (by simp [hσ])
      have hzero_sum : ∑ i : Fin n, x i = 0 :=
        Finset.sum_eq_zero fun i _ => h_all_zero i
      linarith [hx_simp.2]
  -- Apply the classical KKM lemma to get x ∈ ⋂ j, F j
  obtain ⟨x, hx_simp, hx_F⟩ := kkm_closed_cover hn F hF_closed hF_kkm
  refine ⟨x, hx_simp, fun i => ?_⟩
  -- x ∈ F j for all j means: ∀ j k, φ k x ≤ φ j x and ∀ j k, φ j x ≤ φ k x
  -- So all φ j x are equal to the same constant c
  have heq : ∀ j : Fin n, φ j x = φ i x :=
    fun j => le_antisymm ((hx_F i).2 j) ((hx_F j).2 i)
  -- c = φ i x satisfies n * c = 1, hence c = 1/n > 0
  have hsum_eval : ∑ j : Fin n, φ j x = 1 := by
    have h := hsum hx_simp
    simp only [Finset.sum_apply, Pi.one_apply] at h
    exact h
  have hc_pos : 0 < φ i x := by
    have hcard : (n : ℝ) * φ i x = 1 := by
      have : ∑ j : Fin n, φ j x = ∑ _ : Fin n, φ i x :=
        Finset.sum_congr rfl (fun j _ => heq j)
      rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at hsum_eval
      linarith
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    nlinarith [(hnn i x).1]
  -- x ∈ support (φ i) ⊆ tsupport (φ i) ⊆ U i
  exact htsup i (subset_closure (Function.mem_support.mpr (ne_of_gt hc_pos)))
