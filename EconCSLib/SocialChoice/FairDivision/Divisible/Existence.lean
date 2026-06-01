/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
import EconCSLib.Math.FixedPoint.KKM
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.Existence

Existence theorems for envy-free complete divisible allocations.

## Main results

* `proportional_exists` — for any `n` agents with non-atomic finite measures on `[0,1]`, a
  complete proportional allocation exists (each agent values their piece at ≥ 1/n of the cake)
* `ef_exists` — for any `n` agents with non-atomic finite measures on `[0,1]`, a complete
  envy-free allocation exists

## Proof strategy for `ef_exists` (Stromquist 1980)

We follow the proof of Stromquist, "How to Cut a Cake Fairly", *Amer. Math. Monthly* 87 (1980).

### Setup

The **division simplex** `S = stdSimplex ℝ (Fin n)` is the standard `(n-1)`-simplex.  A
point `x ∈ S` represents a way to divide the cake into `n` consecutive pieces: coordinate
`xᵢ ≥ 0` encodes the "fractional length" of the `i`-th piece, and `∑ xᵢ = 1`.  The actual
cut points in `ℝ` are recovered via a fixed homeomorphism `φ : (0,1) ≃ₜ ℝ`; the `i`-th
piece is `φ((∑_{j<i} xⱼ, ∑_{j≤i} xⱼ])`.

The **face opposite vertex `i`** is `simplexFaceOpp i = {x ∈ S | xᵢ = 0}`, the set of
divisions where piece `i` is empty.

### Key definitions

For each agent `j : Fin n` and piece index `i : Fin n`:
- `strom_A i j` — the **preference set** of agent `j` for piece `i`: the set of
  divisions `x ∈ S` where piece `i` achieves maximum value for agent `j`.
  This set is **closed** (by continuity of the value function, `strom_value_continuous`).

- `strom_B i j` — the **unique preference set**: divisions where piece `i` is agent `j`'s
  *unique* maximizer.  This set is **open** (relative to `S`).

- `strom_U i` — the **agent preference union**: `⋃ⱼ strom_B i j`, the set of divisions
  where *some* agent uniquely prefers piece `i`.  Each `strom_U i` is open and does not
  intersect `simplexFaceOpp i`.

### Proof by KKM

The proof splits into two cases:

**Usual case** (`strom_U` covers `S`): Apply `kkm_open_cover` to obtain a point
`x* ∈ ⋂ᵢ strom_U i`.  At `x*`, each piece `i` has a unique claimant among the agents,
and the claimants are all distinct (since `strom_B i j` and `strom_B i j'` are disjoint for
`j ≠ j'`).  Assigning each agent their uniquely preferred piece yields an EF allocation.

**Unusual case** (`strom_U` does not cover `S`): Any uncovered division `x` has every agent
indifferent between two or more pieces.  We eliminate this by approximating the `strom_A i j`
sets: choose irrationals `α₀, …, αₙ₋₁` linearly independent over `ℚ`, and for a large `M`
define modified preference sets `strom_A' i j` by intersecting `strom_A i j` with the
half-open cells `{x | xₖ ∈ [L/M + αⱼ, (L+1)/M + αⱼ)}`.  The resulting `strom_U'` sets DO
cover `S` (the irrationality prevents coincidences), so the usual case applies.  As `M → ∞`,
the approximate fair divisions converge (by compactness of `S`) to a fair division for the
original preferences.

## References

* Stromquist, "How to Cut a Cake Fairly", *Amer. Math. Monthly* 87 (1980), pp. 640–644
* Dubins–Spanier, "How to Cut a Cake Fairly", *Amer. Math. Monthly* 68 (1961), pp. 1–17
* Su, "Rental Harmony: Sperner's Lemma in Fair Division", *Amer. Math. Monthly* (1999)
* Nisan et al., *Algorithmic Game Theory*, Chapter 13
-/

open MeasureTheory Set Topology
open scoped unitInterval

namespace SocialChoice
namespace FairDivision
namespace Divisible

/-! ### Proportional existence -/

/-- **Proportional allocations always exist** for `n` agents with non-atomic finite measures on `[0,1]`.

    A proportional allocation assigns each agent a piece they value at ≥ 1/n of the total cake.

    **Proof sketch** (moving knife, proportional variant):

    By induction on `n = Fintype.card N`.

    *Base case* (`n = 1`): The single agent receives the entire cake.

    *Inductive step*: Given `n` agents, find a cut point `t* ∈ [0,1]` such that
    `μ₀([0, t*]) = μ₀([0,1])/n`. Assign agent 0 the piece `[0, t*]`, which they value at
    exactly `1/n`. Apply the inductive hypothesis to the remaining `n-1` agents on `(t*, 1]`,
    scaled to `1/(n-1)` of the remainder.

    Each agent's piece has value ≥ `1/n` of their total measure on `[0,1]`:
    - Agent 0's piece: exactly `μ₀([0,1])/n` by construction.
    - Agent `i > 0` (inductive hypothesis on restricted measures): value ≥ `1/(n-1)` of
      remainder. Since the remainder has value ≥ `(n-1)/n * μᵢ([0,1])` for agent `i` (they
      didn't cut, so the cut was possibly suboptimal for them), we get value
      ≥ `1/(n-1) * (n-1)/n * μᵢ([0,1]) = 1/n * μᵢ([0,1])`.

    **Key Lean ingredients**:
    - `cut_exists` (in `DubinsSpanier.lean`) — IVT lemma for placing a knife at any fraction
    - `dubinsSpanierProportional` — the inductive algorithm for `Fin n` agents
    - `Fintype.equivFin N` — bijection `N ≃ Fin (Fintype.card N)` to convert types

    **Proof**: apply `dubinsSpanierProportional` with the measure family reindexed along
    the bijection `e := Fintype.equivFin N`, then transport the allocation back along `e`. -/
theorem proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NoAtoms (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  -- Reindex agents via the canonical bijection e : N ≃ Fin (Fintype.card N)
  set n := Fintype.card N
  set e := Fintype.equivFin N
  have hn : 0 < n := Fintype.card_pos
  -- Reindexed measure family: μ' j = μ (e.symm j)
  let μ' : Fin n → Measure I := μ ∘ e.symm
  haveI hfin' : ∀ j : Fin n, IsFiniteMeasure (μ' j) := fun j =>
    show IsFiniteMeasure (μ (e.symm j)) from inferInstance
  haveI hnoatoms' : ∀ j : Fin n, NoAtoms (μ' j) := fun j =>
    show NoAtoms (μ (e.symm j)) from inferInstance
  -- Apply the Dubins–Spanier algorithm
  obtain ⟨A', hA', hprop'⟩ := dubinsSpanierProportional n hn μ'
  -- Transport back: A i = A' (e i)
  refine ⟨fun i => A' (e i), ?_, ?_⟩
  · -- IsAllocation (fun i => A' (e i))
    refine ⟨fun i => hA'.measurable (e i), fun i j hij => hA'.disjoint (e i) (e j)
              (fun h => hij (e.injective h)), ?_⟩
    -- Cover: ⋃ i : N, A' (e i) = Set.univ
    -- Use bijectivity of e: each j : Fin n equals e (e.symm j)
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hA'.cover ▸ Set.mem_univ x)
    exact ⟨e.symm j, by rwa [e.apply_symm_apply]⟩
  · -- IsProportional n (MeasureValuation μ) (fun i => A' (e i))
    intro i
    -- μ' (e i) = μ (e.symm (e i)) = μ i
    have hμ_eq : μ' (e i) = μ i := show μ (e.symm (e i)) = μ i by
      rw [e.symm_apply_apply]
    calc μ i Set.univ = μ' (e i) Set.univ := by rw [hμ_eq]
      _ ≤ ↑n * μ' (e i) (A' (e i)) := hprop' (e i)
      _ = ↑n * μ i (A' (e i)) := by rw [hμ_eq]

/-! ### EF existence: Stromquist scaffolding -/

section StromquistProof

/-!
This section develops the scaffolding for the Stromquist proof of `ef_exists`, following
Stromquist (1980).  The main components are:

1. The **piece function** `strom_piece`: maps a simplex point and a piece index to a subset of ℝ.
2. The **value function** `strom_value`: evaluates a measure on a piece.
3. The **preference sets** `strom_A`, `strom_B`, `strom_U`: closed/open subsets of the simplex
   encoding agent preferences.
4. The **KKM application** and the **assignment** of pieces to agents.

**Design note**: `strom_A i j` is defined on all of `Fin n → ℝ` (not restricted to the simplex).
This ensures `strom_B i j` is genuinely open in the ambient space, which is required for the KKM
open-cover theorem.  The simplex constraint appears explicitly only in `strom_A_covers` and the
KKM application.
-/

variable (n : ℕ) (hn : 0 < n) (μ : Fin n → Measure ℝ)
variable [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)]

/-- For a non-atomic finite measure ν and any reals l, r:
    `(ν (Ico l r)).toReal = max ((ν (Iic r)).toReal - (ν (Iic l)).toReal) 0`. -/
private lemma measure_Ico_toReal (ν : Measure ℝ) [IsFiniteMeasure ν] [NoAtoms ν] (l r : ℝ) :
    (ν (Set.Ico l r)).toReal =
      max ((ν (Set.Iic r)).toReal - (ν (Set.Iic l)).toReal) 0 := by
  by_cases hlr : l ≤ r
  · -- l ≤ r: Ico =ᵐ[ν] Ioc; and Iic l ∪ Ioc l r = Iic r (disjoint)
    have h_Ico_eq_Ioc : ν (Set.Ico l r) = ν (Set.Ioc l r) := by
      have h : ν.restrict (Set.Ico l r) = ν.restrict (Set.Ioc l r) :=
        restrict_Ico_eq_restrict_Ioc
      calc ν (Set.Ico l r)
          = ν.restrict (Set.Ico l r) Set.univ := by
              rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        _ = ν.restrict (Set.Ioc l r) Set.univ := by rw [h]
        _ = ν (Set.Ioc l r) := by
              rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    -- Iic l and Ioc l r are disjoint with union Iic r
    have hd : Disjoint (Set.Iic l) (Set.Ioc l r) :=
      Set.disjoint_left.mpr (fun x hxl hxr => absurd hxl (not_le.mpr hxr.1))
    have hu : Set.Iic l ∪ Set.Ioc l r = Set.Iic r := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro (h | ⟨-, h⟩) <;> [exact le_trans h hlr; exact h]
      · intro h
        by_cases h' : x ≤ l
        · exact Or.inl h'
        · exact Or.inr ⟨not_le.mp h', h⟩
    have h_sum : ν (Set.Iic r) = ν (Set.Iic l) + ν (Set.Ioc l r) := by
      rw [← hu]; exact measure_union hd measurableSet_Ioc
    -- Convert to real arithmetic
    have h_sum_real : (ν (Set.Iic r)).toReal =
        (ν (Set.Iic l)).toReal + (ν (Set.Ioc l r)).toReal := by
      rw [h_sum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have hnn : 0 ≤ (ν (Set.Ioc l r)).toReal := ENNReal.toReal_nonneg
    rw [h_Ico_eq_Ioc, max_eq_left (by linarith)]
    linarith
  · -- l > r: empty interval
    push_neg at hlr
    have hempty : Set.Ico l r = ∅ := Set.Ico_eq_empty (not_lt.mpr (le_of_lt hlr))
    have hle : (ν (Set.Iic r)).toReal ≤ (ν (Set.Iic l)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        (measure_mono (Set.Iic_subset_Iic.mpr (le_of_lt hlr)))
    simp only [hempty, measure_empty, ENNReal.toReal_zero]
    exact (max_eq_right (by linarith)).symm

/-! #### Piece function and partition -/

/-- The **i-th piece at division `x`**: the subset of `ℝ` assigned to piece `i` when the
    cake is divided according to `x ∈ stdSimplex ℝ (Fin n)`.

    **Construction**: Fix a homeomorphism `φ : (0,1) ≃ₜ ℝ` (e.g., `φ(t) = tan(π(t - 1/2))`).
    At division `x`, the i-th piece is `φ((∑_{j<i} xⱼ, ∑_{j≤i} xⱼ])`.

    Equivalently for measures supported on `[0,1]`: piece `i` is the interval
    `(∑_{j<i} xⱼ, ∑_{j≤i} xⱼ]` in `[0,1]`.

    The key properties (stated as separate lemmas below) are:
    - The pieces partition `ℝ` (`strom_piece_partition`).
    - Each piece is measurable (`strom_piece_measurable`).
    - Piece `i` is empty iff `xᵢ = 0` (`strom_piece_empty_iff`). -/
noncomputable def strom_piece (x : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  Set.Ico (∑ j ∈ Finset.univ.filter (· < i), x j) (∑ j ∈ Finset.univ.filter (· ≤ i), x j)

/-- The pieces at any division `x ∈ stdSimplex ℝ (Fin n)` form a measurable partition of
    `Set.Ico 0 1 ⊆ ℝ`.  (They do **not** cover all of ℝ; see `strom_usual_case` for how the
    complement is handled when constructing a `IsAllocation`.) -/
lemma strom_piece_partition (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    (∀ i, MeasurableSet (strom_piece n x i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (strom_piece n x i) (strom_piece n x j)) ∧
    (⋃ i, strom_piece n x i = Set.Ico 0 1) := by
  have hnn : ∀ i, 0 ≤ x i := hx.1
  have hsum : ∑ i, x i = 1 := hx.2
  -- derive n > 0 from the sum condition
  have hn' : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hsum
    · exact h
  -- cumulative lower/upper sums
  let L : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.filter (· < i), x j
  let U : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.filter (· ≤ i), x j
  have hdef : ∀ i, strom_piece n x i = Set.Ico (L i) (U i) := fun _ => rfl
  -- L on the first element = 0
  have hL0 : L ⟨0, hn'⟩ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _)
  -- U on the last element = 1
  have hUlast : U ⟨n - 1, by omega⟩ = 1 := by
    simp only [U]
    have heq : Finset.univ.filter (· ≤ (⟨n - 1, by omega⟩ : Fin n)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro j _
      rw [Fin.le_iff_val_le_val]
      show j.val ≤ n - 1
      have := j.isLt; omega
    rw [heq]; exact hsum
  -- i < j → U i ≤ L j  (upper bound of piece i ≤ lower bound of piece j)
  have hU_le_L : ∀ i j : Fin n, i < j → U i ≤ L j := fun i j hij =>
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun k => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hk => hk.trans_lt hij)
      (fun k _ _ => hnn k)
  have hL_nonneg : ∀ i, 0 ≤ L i := fun i => Finset.sum_nonneg (fun j _ => hnn j)
  have hU_le_one : ∀ i, U i ≤ 1 := fun i => by
    calc U i ≤ ∑ j : Fin n, x j :=
              Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun k _ _ => hnn k)
      _ = 1 := hsum
  refine ⟨fun i => hdef i ▸ measurableSet_Ico, ?_, ?_⟩
  · -- Pairwise disjointness
    intro i j hij
    rw [hdef i, hdef j, Set.Ico_disjoint_Ico]
    rcases lt_or_gt_of_ne hij with h | h
    · exact (min_le_left _ _).trans ((hU_le_L i j h).trans (le_max_right _ _))
    · exact (min_le_right _ _).trans ((hU_le_L j i h).trans (le_max_left _ _))
  · -- ⋃ i, Ico (L i) (U i) = Ico 0 1
    simp_rw [hdef]
    ext t; simp only [Set.mem_iUnion, Set.mem_Ico]
    constructor
    · rintro ⟨i, hlo, hhi⟩
      exact ⟨(hL_nonneg i).trans hlo, hhi.trans_le (hU_le_one i)⟩
    · intro ⟨ht0, ht1⟩
      -- find the minimum piece i₀ with t < U i₀
      have hS_ne : (Finset.univ.filter (fun i : Fin n => t < U i)).Nonempty :=
        ⟨⟨n - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUlast ▸ ht1⟩⟩
      set i₀ := (Finset.univ.filter (fun i : Fin n => t < U i)).min' hS_ne
      refine ⟨i₀, ?_, (Finset.mem_filter.mp (Finset.min'_mem _ hS_ne)).2⟩
      -- show L i₀ ≤ t
      rcases Nat.eq_zero_or_pos i₀.val with h0 | hpos
      · -- i₀ = 0: L i₀ = 0 ≤ t
        have hempty : Finset.univ.filter (fun j : Fin n => j < i₀) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro j _
          simp only [not_lt, Fin.le_iff_val_le_val, h0]
          exact Nat.zero_le _
        simp [L, hempty, ht0]
      · -- i₀.val > 0: predecessor pred satisfies t ≥ U pred = L i₀
        have hpred_lt : i₀.val - 1 < n := by omega
        set pred : Fin n := ⟨i₀.val - 1, hpred_lt⟩
        have hconsec : U pred = L i₀ := by
          simp only [U, L, pred]
          congr 1; ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.le_iff_val_le_val, Fin.lt_def]
          omega
        have hpred_not_mem : pred ∉ Finset.univ.filter (fun i : Fin n => t < U i) := by
          intro hmem
          have hpred_lt' : pred < i₀ := Fin.lt_def.mpr (by simp [pred]; omega)
          exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr hpred_lt')
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hpred_not_mem
        linarith [hconsec]

/-- Piece `i` is empty (measure zero for all agents) if and only if `xᵢ = 0`.

    This is the measure-theoretic content of "face `i` corresponds to piece `i` being empty":
    at a point `x` in `simplexFaceOpp i`, the piece `strom_piece n x i` contains no mass. -/
lemma strom_piece_empty_iff (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (i : Fin n) :
    strom_piece n x i = ∅ ↔ x i = 0 := by
  simp only [strom_piece, Set.Ico_eq_empty_iff, not_lt]
  have key : ∑ j ∈ Finset.univ.filter (· ≤ i), x j =
      ∑ j ∈ Finset.univ.filter (· < i), x j + x i := by
    have hsplit : Finset.univ.filter (fun j : Fin n => j ≤ i) =
        (Finset.univ.filter (fun j : Fin n => j < i)) ∪ {i} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_singleton]; exact le_iff_lt_or_eq
    have hdisj : Disjoint (Finset.univ.filter (fun j : Fin n => j < i)) {i} := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_irrefl i
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton]
  constructor
  · intro h; linarith [hx.1 i]
  · intro h; rw [key]; linarith

/-! #### Value function and its continuity -/

/-- The **value** agent `j` assigns to piece `i` at division `x`:
    `strom_value μ x j i = μ j (strom_piece n x i)`. -/
noncomputable def strom_value (x : Fin n → ℝ) (j i : Fin n) : ℝ :=
  (μ j (strom_piece n x i)).toReal

/-- The value function `x ↦ strom_value μ x j i` is **continuous** on all of `Fin n → ℝ`.

    **Proof**: The piece endpoints `l(x) = ∑_{k<i} xk` and `r(x) = ∑_{k≤i} xk` are linear
    (hence continuous) in `x`.  The measure of the piece equals
    `max (CDF_j(r(x)) - CDF_j(l(x))) 0` where `CDF_j` is the continuous CDF of `μ j`
    (continuous by `cdfRealContinuous`).  The composition is continuous. -/
lemma strom_value_continuous (j i : Fin n) :
    Continuous (fun x : Fin n → ℝ => strom_value n μ x j i) := by
  have hcdf : Continuous (fun t : ℝ => (μ j (Set.Iic t)).toReal) :=
    cdfRealContinuous (μ j)
  have hl_cont : Continuous (fun x : Fin n → ℝ =>
      ∑ k ∈ Finset.univ.filter (· < i), x k) :=
    continuous_finset_sum _ fun k _ => continuous_apply k
  have hr_cont : Continuous (fun x : Fin n → ℝ =>
      ∑ k ∈ Finset.univ.filter (· ≤ i), x k) :=
    continuous_finset_sum _ fun k _ => continuous_apply k
  have hval_eq : ∀ x : Fin n → ℝ, strom_value n μ x j i =
      max ((μ j (Set.Iic (∑ k ∈ Finset.univ.filter (· ≤ i), x k))).toReal -
           (μ j (Set.Iic (∑ k ∈ Finset.univ.filter (· < i), x k))).toReal) 0 := fun x => by
    simp only [strom_value, strom_piece]
    exact measure_Ico_toReal (μ j) _ _
  simp_rw [hval_eq]
  exact (hcdf.comp hr_cont |>.sub (hcdf.comp hl_cont)).max continuous_const

/-! #### Preference sets -/

/-- **Preference set** `strom_A i j`: the set of points in `Fin n → ℝ` where
    piece `i` is a (weak) maximizer for agent `j`.

    `strom_A n μ i j = {x | ∀ k, strom_value μ x j k ≤ strom_value μ x j i}`.

    **Design note**: defined on all of `Fin n → ℝ` (not restricted to the simplex) so that
    `strom_B i j` (defined as `strom_A i j \ ⋃_{k≠i} strom_A k j`) is genuinely open in the
    ambient space, as required by `kkm_open_cover`. -/
private def strom_A (i j : Fin n) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | ∀ k : Fin n, strom_value n μ x j k ≤ strom_value n μ x j i}

/-- The preference set `strom_A i j` is **closed** in `Fin n → ℝ`.

    **Proof**: `strom_A i j = ⋂_k {x | strom_value x j k ≤ strom_value x j i}`, a finite
    intersection of closed sublevel sets of continuous functions. -/
private lemma strom_A_closed (i j : Fin n) : IsClosed (strom_A n μ i j) := by
  simp only [strom_A, Set.setOf_forall]
  exact isClosed_iInter fun k =>
    isClosed_le (strom_value_continuous n μ j k) (strom_value_continuous n μ j i)

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
/-- For each agent `j`, the preference sets `strom_A i j` (over `i`) cover the simplex.

    **Proof**: At any division `x`, `i ↦ strom_value μ x j i` has a maximizer on the finite
    set `Fin n`; that maximizer's preference set contains `x`. -/
private lemma strom_A_covers (j : Fin n) :
    stdSimplex ℝ (Fin n) ⊆ ⋃ i, strom_A n μ i j := by
  intro x _
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => strom_value n μ x j i) hne
  exact Set.mem_iUnion.mpr ⟨i, fun k => hi k (Finset.mem_univ k)⟩

omit [∀ i, NoAtoms (μ i)] in
/-- The preference set `strom_A i j` does **not intersect** the face `simplexFaceOpp i`.

    **Proof**: At any `x ∈ simplexFaceOpp i`, piece `i` is empty (`strom_piece_empty_iff`),
    so `strom_value μ x j i = 0`.  But the pieces partition `[0,1)` (by `strom_piece_partition`)
    and `μ j (Ico 0 1) > 0` (by `hpos`), so by finite additivity some piece has positive measure.
    Agent `j` therefore prefers some piece over the empty piece `i`, contradicting `x ∈ strom_A`.

    **Note**: `hpos` is required; the lemma is false for the zero measure. -/
private lemma strom_A_avoids_face (i j : Fin n) (hpos : 0 < μ j (Set.Ico 0 1)) :
    strom_A n μ i j ∩ simplexFaceOpp i = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x ⟨hA, hface⟩
  simp only [simplexFaceOpp, Set.mem_inter_iff, Set.mem_setOf_eq] at hface
  obtain ⟨hxi, hx_simp⟩ := hface
  -- Piece i is empty at this division
  have hpi : strom_piece n x i = ∅ :=
    (strom_piece_empty_iff n x hx_simp i).mpr hxi
  -- Value of piece i for agent j is 0
  have hvi : strom_value n μ x j i = 0 := by
    simp [strom_value, hpi]
  -- hA says piece i is weakly best, so every piece has value 0 for agent j
  have hv_zero : ∀ k, μ j (strom_piece n x k) = 0 := by
    intro k
    have hle : strom_value n μ x j k ≤ 0 := hvi ▸ hA k
    have hnn : 0 ≤ strom_value n μ x j k := ENNReal.toReal_nonneg
    have heq : strom_value n μ x j k = 0 := le_antisymm hle hnn
    simp only [strom_value, ENNReal.toReal_eq_zero_iff] at heq
    exact heq.resolve_right (measure_ne_top _ _)
  -- The pieces partition [0,1) (from strom_piece_partition)
  obtain ⟨hmeas, hdisj, hcover⟩ := strom_piece_partition n x hx_simp
  -- By countable additivity, μ j (Ico 0 1) = ∑ k, μ j (strom_piece n x k) = 0
  have hmeasure_zero : μ j (Set.Ico 0 1) = 0 := by
    rw [← hcover, measure_iUnion (fun ⦃a b⦄ hab => hdisj a b hab) hmeas, tsum_fintype]
    exact Finset.sum_eq_zero (fun k _ => hv_zero k)
  exact absurd hmeasure_zero (ne_of_gt hpos)

/-! #### Unique preference sets -/

/-- **Unique preference set** `strom_B i j`: the set of points where piece `i` is agent
    `j`'s **unique** maximizer.

    `strom_B n μ i j = strom_A n μ i j \ ⋃_{k ≠ i} strom_A n μ k j`.

    Equivalently, `strom_B i j = ⋂_{k ≠ i} {x | strom_value x j k < strom_value x j i}`,
    which makes openness immediate.  Since `strom_A` is defined on all of `Fin n → ℝ`,
    `strom_B i j` is genuinely **open** in the ambient space. -/
private def strom_B (i j : Fin n) : Set (Fin n → ℝ) :=
  strom_A n μ i j \ ⋃ k ∈ Finset.univ.filter (· ≠ i), strom_A n μ k j

/-- The unique-preference set `strom_B i j` is **open** in `Fin n → ℝ`.

    **Proof**: Show `strom_B i j = ⋂_{k ≠ i} {x | strom_value x j k < strom_value x j i}`,
    a finite intersection of open strict-sublevel sets of the continuous function `strom_value`. -/
private lemma strom_B_open (i j : Fin n) : IsOpen (strom_B n μ i j) := by
  have hkey : strom_B n μ i j =
      ⋂ k ∈ Finset.univ.filter (· ≠ i),
        {x : Fin n → ℝ | strom_value n μ x j k < strom_value n μ x j i} := by
    ext x
    simp only [strom_B, strom_A, Set.mem_diff, Set.mem_setOf_eq, Set.mem_iUnion,
               Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iInter, not_exists]
    constructor
    · intro ⟨hmax, hno⟩ k hki
      exact lt_of_le_of_ne (hmax k) (fun h => hno k hki (fun m => h ▸ hmax m))
    · intro hlt
      refine ⟨fun k => ?_, fun k hki hAk => absurd (hAk i) (not_le.mpr (hlt k hki))⟩
      rcases eq_or_ne k i with rfl | hki
      · exact le_refl _
      · exact le_of_lt (hlt k hki)
  rw [hkey]
  apply isOpen_biInter_finset
  intro k _
  exact isOpen_lt (strom_value_continuous n μ j k) (strom_value_continuous n μ j i)

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
/-- The unique-preference sets `strom_B i j` (over `j`) are pairwise disjoint for fixed `i`.

    **Proof**: If `x ∈ strom_B i j ∩ strom_B i j'` with `j ≠ j'`, then piece `i` is the unique
    maximizer for both `j` and `j'` at `x`, which is not a contradiction per se.  The disjointness
    that matters is: for fixed `j`, the sets `strom_B i j` over `i` are pairwise disjoint
    (since piece `i` cannot be uniquely preferred if it ties with another piece). -/
private lemma strom_B_disjoint_over_i (j : Fin n) (i i' : Fin n) (hii' : i ≠ i') :
    Disjoint (strom_B n μ i j) (strom_B n μ i' j) := by
  simp only [Set.disjoint_left, strom_B]
  intro x ⟨_, hnotA⟩ ⟨hAi', _⟩
  apply hnotA
  rw [Set.mem_iUnion₂]
  exact ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hii'.symm⟩, hAi'⟩

/-! #### Agent preference union -/

/-- **Agent preference union** `strom_U i`: the set of divisions where *some* agent uniquely
    prefers piece `i`.

    `strom_U n μ i = ⋃ j, strom_B n μ i j`. -/
private def strom_U (i : Fin n) : Set (Fin n → ℝ) :=
  ⋃ j, strom_B n μ i j

/-- `strom_U i` is **open** (as a union of open sets). -/
private lemma strom_U_open (i : Fin n) : IsOpen (strom_U n μ i) := by
  exact isOpen_iUnion (strom_B_open n μ i ·)

omit [∀ i, NoAtoms (μ i)] in
/-- `strom_U i` does **not intersect** the face `simplexFaceOpp i`.

    **Proof**: `strom_B i j ⊆ strom_A i j`, and `strom_A i j ∩ simplexFaceOpp i = ∅`
    by `strom_A_avoids_face`. Requires `hpos : ∀ j, 0 < μ j (Ico 0 1)`. -/
private lemma strom_U_avoids_face (i : Fin n) (hpos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1)) :
    strom_U n μ i ∩ simplexFaceOpp i = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x ⟨hU, hface⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
  have hB_sub_A : strom_B n μ i j ⊆ strom_A n μ i j := Set.diff_subset
  have hA_mem : x ∈ strom_A n μ i j := hB_sub_A hj
  have := Set.eq_empty_iff_forall_notMem.mp (strom_A_avoids_face n μ i j (hpos j)) x
  exact this ⟨hA_mem, hface⟩

/-! #### The usual case: KKM gives a fair assignment -/

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
/-- **Fair assignment from a common KKM point**: given a point `x*` in `⋂ᵢ strom_U i`,
    produce an injective map `assign : Fin n → Fin n` such that agent `assign i` uniquely
    prefers piece `i` at `x*`.

    **Proof**: At `x*`, for each `i` there exists `j` with `x* ∈ strom_B i j`, i.e., agent `j`
    uniquely prefers piece `i`.  The map `i ↦ j` is well-defined.  Injectivity follows from
    `strom_B_disjoint_over_i`: if `assign i = assign i' = j`, then `x* ∈ strom_B i j` and
    `x* ∈ strom_B i' j`, but for fixed `j`, the sets `strom_B i j` and `strom_B i' j` are
    disjoint — contradiction. -/
private lemma strom_fair_assignment (x : Fin n → ℝ) (hU : ∀ i, x ∈ strom_U n μ i) :
    ∃ assign : Fin n → Fin n, Function.Injective assign ∧
      ∀ i, x ∈ strom_A n μ i (assign i) ∧
           ∀ k ≠ i, strom_value n μ x (assign i) k < strom_value n μ x (assign i) i := by
  have hchoice : ∀ i, ∃ j, x ∈ strom_B n μ i j := fun i => Set.mem_iUnion.mp (hU i)
  refine ⟨fun i => (hchoice i).choose, ?_, ?_⟩
  · intro i i' heq
    by_contra hii'
    have h1 : x ∈ strom_B n μ i ((hchoice i).choose) := (hchoice i).choose_spec
    have h2 : x ∈ strom_B n μ i' ((hchoice i').choose) := (hchoice i').choose_spec
    simp only at heq
    rw [heq] at h1
    exact Set.disjoint_left.mp (strom_B_disjoint_over_i n μ _ i i' hii') h1 h2
  · intro i
    have hB : x ∈ strom_B n μ i ((hchoice i).choose) := (hchoice i).choose_spec
    have hA : x ∈ strom_A n μ i ((hchoice i).choose) := Set.diff_subset hB
    -- hA : ∀ k, strom_value n μ x (assign i) k ≤ strom_value n μ x (assign i) i
    constructor
    · exact hA
    · intro k hki
      have hnotAk : x ∉ strom_A n μ k ((hchoice i).choose) := by
        intro hc
        exact hB.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki⟩) hc)
      exact lt_of_le_of_ne (hA k)
        (fun h => hnotAk (fun m => h ▸ hA m))

/-- **Usual case**: if `strom_U` covers the simplex, construct an EF allocation.

    **Proof**: Apply `kkm_open_cover` to get `x* ∈ ⋂ᵢ strom_U i`.  Use `strom_fair_assignment`
    to produce an injective assignment `assign : Fin n ↪ Fin n` (which is a bijection since
    `Fin n` is finite).  Define the allocation `A i = strom_piece n x* (assign⁻¹ i)`, extended
    to cover `ℝ \ [0,1)` on agent `0` (measure zero by `hsupp`).
    EF holds: agent `i` uniquely prefers `strom_piece n x* (assign⁻¹ i)` over all others.

    **Note**: `hpos` and `hsupp` are needed: `hpos` for `strom_U_avoids_face` (face-avoidance),
    and `hsupp` so the `ℝ \ [0,1)` extension is measure-zero for all agents. -/
private lemma strom_usual_case
    (hn : 0 < n)
    (hcover : stdSimplex ℝ (Fin n) ⊆ ⋃ i, strom_U n μ i)
    (hpos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1))
    (hsupp : ∀ j : Fin n, μ j = (μ j).restrict (Set.Ico 0 1)) :
    ∃ A : Allocation (Fin n) ℝ,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  -- Step 1: KKM gives a common point x* in ⋂ᵢ strom_U i
  obtain ⟨x, hx_simp, hx_U⟩ := kkm_open_cover hn (strom_U n μ) (strom_U_open n μ)
    (fun i => by
      intro x hx_face hx_U
      have h := Set.mem_inter hx_U hx_face
      rw [strom_U_avoids_face n μ i hpos] at h
      simp at h)
    hcover
  -- Step 2: Fair assignment: assign : pieces → agents (injective)
  obtain ⟨assign, hinj, hassign⟩ := strom_fair_assignment n μ x hx_U
  -- Step 3: assign is bijective (injective self-map on finite type)
  have hbij : Function.Bijective assign := Finite.injective_iff_bijective.mp hinj
  let e : Fin n ≃ Fin n := Equiv.ofBijective assign hbij
  -- e.symm j = piece for agent j; assign (e.symm j) = e (e.symm j) = j
  -- Step 4: Piece partition data at x*
  obtain ⟨hmeas, hdisj, hcover01⟩ := strom_piece_partition n x hx_simp
  -- Each piece lies in [0,1)
  have hpiece_sub : ∀ k, strom_piece n x k ⊆ Set.Ico 0 1 :=
    fun k => hcover01 ▸ Set.subset_iUnion (strom_piece n x) k
  -- Helper: the extension ℝ \ [0,1) is measure-zero by hsupp
  have hext : ∀ i : Fin n, μ i (Set.Iio 0 ∪ Set.Ici 1) = 0 := fun i => by
    rw [hsupp i, Measure.restrict_apply (measurableSet_Iio.union measurableSet_Ici)]
    have h1 : (Set.Iio (0:ℝ) ∪ Set.Ici 1) ∩ Set.Ico 0 1 = ∅ := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ici,
                        Set.mem_Ico, Set.mem_empty_iff_false, iff_false, not_and]
      rintro (h | h) <;> intro h2 <;> linarith
    rw [h1]; exact measure_empty
  -- Helper: ext is disjoint from any piece
  have hext_disj : ∀ k, Disjoint (strom_piece n x k) (Set.Iio 0 ∪ Set.Ici 1) :=
    fun k => Set.disjoint_left.mpr fun t ht_p ht_e => by
      have := hpiece_sub k ht_p
      simp only [Set.mem_Ico] at this
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ici] at ht_e
      rcases ht_e with h | h <;> linarith [this.1, this.2]
  -- Step 5: Build allocation; extend agent 0's piece to cover ℝ \ [0,1)
  -- Unfold helper: A_def characterizes the allocation pieces
  let z : Fin n := ⟨0, hn⟩
  -- The allocation: agent z gets piece(e.symm z) ∪ ext, others get plain pieces
  refine ⟨fun agent =>
    if agent = z then strom_piece n x (e.symm agent) ∪ (Set.Iio 0 ∪ Set.Ici 1)
    else strom_piece n x (e.symm agent), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- measurability
    intro agent; simp only [z]; split_ifs
    · exact (hmeas _).union (measurableSet_Iio.union measurableSet_Ici)
    · exact hmeas _
  · -- pairwise disjointness
    intro i j hij
    have heij : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    simp only [z]; split_ifs with hi0 hj0 hj0
    · exact absurd (hi0.trans hj0.symm) hij
    · -- A i = piece_i ∪ ext, A j = piece_j
      rw [Set.disjoint_union_left]
      exact ⟨hdisj _ _ heij, (hext_disj (e.symm j)).symm⟩
    · -- A i = piece_i, A j = piece_j ∪ ext
      rw [Set.disjoint_union_right]
      exact ⟨hdisj _ _ heij, hext_disj (e.symm i)⟩
    · -- both plain pieces
      exact hdisj _ _ heij
  · -- cover: ⋃ i, A i = Set.univ
    ext t; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases ht01 : t ∈ Set.Ico 0 1
    · rw [← hcover01] at ht01
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht01
      refine ⟨e k, ?_⟩
      split_ifs with h0
      · rw [e.symm_apply_apply]; exact Set.mem_union_left _ hk
      · rw [e.symm_apply_apply]; exact hk
    · refine ⟨z, ?_⟩
      refine Set.mem_union_right _ ?_
      simp only [Set.mem_Ico, not_and_or, not_lt] at ht01
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ici]
      rcases ht01 with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr h
  · -- IsEnvyFree: agent i prefers A i over A j
    -- μ i (A j) = μ i (strom_piece n x (e.symm j)) for all i, j (hsupp + disjointness)
    have hA_measure : ∀ (i j : Fin n),
        μ i (if j = z then strom_piece n x (e.symm j) ∪ (Set.Iio 0 ∪ Set.Ici 1)
              else strom_piece n x (e.symm j)) = μ i (strom_piece n x (e.symm j)) := by
      intro i j; split_ifs with h0
      · rw [measure_union (hext_disj _) (measurableSet_Iio.union measurableSet_Ici), hext i, add_zero]
      · rfl
    intro i j
    simp only [z] at hA_measure ⊢
    simp only [MeasureValuation]
    rw [hA_measure i j, hA_measure i i]
    -- From hassign (e.symm i): agent assign(e.symm i) = i prefers piece e.symm i over all k
    have hAi : x ∈ strom_A n μ (e.symm i) i := by
      have h := (hassign (e.symm i)).1
      have heq : assign (e.symm i) = i := e.apply_symm_apply i
      rwa [heq] at h
    have hle := hAi (e.symm j)
    simp only [strom_value] at hle
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hle

/-! #### The unusual case: shifted coordinate cells -/

/-- The open shifted cell determined by integer coordinates `p` for agent `j`.

    Stromquist's approximation perturbs the simplex by the hyperplanes
    `x_k = L / M + α_j` on the first `n - 1` coordinates.  The connected components of the
    complement are the open cells; we keep them as ambient open subsets of `Fin n → ℝ`. -/
private def strom_cellOpen (M : ℕ) (α : Fin n → ℝ) (j : Fin n) (p : Fin (n - 1) → ℤ) :
    Set (Fin n → ℝ) :=
  {x | ∀ k : Fin (n - 1),
      (p k : ℝ) < (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) ∧
        (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) < (p k : ℝ) + 1}

/-- The cell `p` *hits* piece `i` for agent `j` if that open cell meets the simplex at a point
    where agent `j` weakly prefers piece `i`. -/
private def strom_cellHits (M : ℕ) (α : Fin n → ℝ) (j i : Fin n) (p : Fin (n - 1) → ℤ) : Prop :=
  ((strom_cellOpen n hn M α j p) ∩ stdSimplex ℝ (Fin n) ∩ strom_A n μ i j).Nonempty

/-- The owner of a cell: the smallest piece index whose preference set meets the cell.

    If the cell does not meet any `strom_A i j`, the owner is `none`.  On simplex points this
    can only happen on cell boundaries; see `strom_approx_covers`. -/
private noncomputable def strom_cellOwner (M : ℕ) (α : Fin n → ℝ) (j : Fin n)
    (p : Fin (n - 1) → ℤ) : Option (Fin n) := by
  classical
  exact if h : ∃ i : Fin n, strom_cellHits n hn μ M α j i p then
    some <| (Finset.univ.filter fun i => strom_cellHits n hn μ M α j i p).min'
      (by
        rcases h with ⟨i, hi⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
  else
    none

/-- The approximate unique-preference set obtained by assigning each open cell to its owner. -/
private noncomputable def strom_B' (M : ℕ) (α : Fin n → ℝ) (i j : Fin n) : Set (Fin n → ℝ) :=
  ⋃ p : Fin (n - 1) → ℤ,
    if strom_cellOwner n hn μ M α j p = some i then
      strom_cellOpen n hn M α j p
    else
      ∅

/-- The approximate agent-preference union for piece `i`. -/
private noncomputable def strom_U' (M : ℕ) (α : Fin n → ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  ⋃ j : Fin n, strom_B' n hn μ M α i j

private lemma strom_cellOpen_open (M : ℕ) (α : Fin n → ℝ) (j : Fin n)
    (p : Fin (n - 1) → ℤ) : IsOpen (strom_cellOpen n hn M α j p) := by
  classical
  change IsOpen ({x | ∀ k : Fin (n - 1),
      (p k : ℝ) < (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) ∧
        (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) < (p k : ℝ) + 1} : Set (Fin n → ℝ))
  rw [show ({x | ∀ k : Fin (n - 1),
      (p k : ℝ) < (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) ∧
        (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) < (p k : ℝ) + 1} : Set (Fin n → ℝ)) =
      ⋂ k ∈ (Finset.univ : Finset (Fin (n - 1))),
        {x | (p k : ℝ) < (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) ∧
          (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) < (p k : ℝ) + 1} by
    ext x
    simp]
  refine isOpen_biInter_finset fun k _ => ?_
  let g : (Fin n → ℝ) → ℝ := fun x => (M : ℝ) * (x ⟨k.1, by omega⟩ - α j)
  have hg : Continuous g := by
    fun_prop
  simpa [g] using (isOpen_lt continuous_const hg).inter (isOpen_lt hg continuous_const)

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
private lemma strom_B'_open (M : ℕ) (α : Fin n → ℝ) (i j : Fin n) :
    IsOpen (strom_B' n hn μ M α i j) := by
  classical
  refine isOpen_iUnion fun p => ?_
  by_cases h : strom_cellOwner n hn μ M α j p = some i
  · simp [h, strom_cellOpen_open]
  · simp [h]

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
private lemma strom_U'_open (M : ℕ) (α : Fin n → ℝ) (i : Fin n) :
    IsOpen (strom_U' n hn μ M α i) := by
  exact isOpen_iUnion (strom_B'_open n hn μ M α i ·)

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
private lemma strom_B'_disjoint_over_i (M : ℕ) (α : Fin n → ℝ) (j : Fin n) (i i' : Fin n)
    (hii' : i ≠ i') :
    Disjoint (strom_B' n hn μ M α i j) (strom_B' n hn μ M α i' j) := by
  classical
  simp only [Set.disjoint_left, strom_B']
  intro x hx hx'
  rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hx' with ⟨q, hq⟩
  by_cases hpOwner : strom_cellOwner n hn μ M α j p = some i
  · simp [hpOwner] at hp
    by_cases hqOwner : strom_cellOwner n hn μ M α j q = some i'
    · simp [hqOwner] at hq
      have hxp : x ∈ strom_cellOpen n hn M α j p := hp
      have hxq : x ∈ strom_cellOpen n hn M α j q := hq
      have hpEq : p = q := by
        funext k
        rcases hxp k with ⟨hpk0, hpk1⟩
        rcases hxq k with ⟨hqk0, hqk1⟩
        let t : ℝ := (M : ℝ) * (x ⟨k.1, by omega⟩ - α j)
        have hpFloor : Int.floor t = p k := by
          rw [Int.floor_eq_iff]
          exact ⟨le_of_lt hpk0, hpk1⟩
        have hqFloor : Int.floor t = q k := by
          rw [Int.floor_eq_iff]
          exact ⟨le_of_lt hqk0, hqk1⟩
        exact hpFloor.symm.trans hqFloor
      have hOwnerq : strom_cellOwner n hn μ M α j p = some i' := by simpa [hpEq] using hqOwner
      have : some i = some i' := hpOwner.symm.trans hOwnerq
      exact hii' (Option.some.inj this)
    · simp [hqOwner] at hq
  · simp [hpOwner] at hp

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
private lemma strom_cellOwner_eq_some_imp_hits (M : ℕ) (α : Fin n → ℝ) (j i : Fin n)
    (p : Fin (n - 1) → ℤ)
    (h : strom_cellOwner n hn μ M α j p = some i) :
    strom_cellHits n hn μ M α j i p := by
  classical
  unfold strom_cellOwner at h
  split_ifs at h with hex
  · have hmem :
        (Finset.univ.filter fun i => strom_cellHits n hn μ M α j i p).min'
          (by
            rcases hex with ⟨i0, hi0⟩
            exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩) ∈
        (Finset.univ.filter fun i => strom_cellHits n hn μ M α j i p) :=
      Finset.min'_mem _ _
    have hhit :
        strom_cellHits n hn μ M α j
          ((Finset.univ.filter fun i => strom_cellHits n hn μ M α j i p).min'
            (by
              rcases hex with ⟨i0, hi0⟩
              exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0⟩⟩)) p :=
      (Finset.mem_filter.mp hmem).2
    injection h with hi
    simpa [hi] using hhit

/-- A simplex point lies on an agent-`j` boundary hyperplane if one of its first `n - 1`
    coordinates is congruent to `α j` modulo `1 / M`. -/
private def strom_onBoundary (M : ℕ) (α : Fin n → ℝ) (j : Fin n) (x : Fin n → ℝ) : Prop :=
  ∃ k : Fin (n - 1), ∃ z : ℤ,
    (M : ℝ) * (x ⟨k.1, by omega⟩ - α j) = z

private lemma strom_mem_cellOpen_of_not_onBoundary
    (α : Fin n → ℝ) (M : ℕ) (x : Fin n → ℝ) (j : Fin n)
    (hx : ¬ strom_onBoundary n hn M α j x) :
    let p : Fin (n - 1) → ℤ := fun k =>
      Int.floor ((M : ℝ) * (x ⟨k.1, by omega⟩ - α j))
    x ∈ strom_cellOpen n hn M α j p := by
  intro p k
  have hk : k.1 < n := Nat.lt_of_lt_of_le k.2 (Nat.sub_le n 1)
  constructor
  · have hle :
        ((Int.floor ((M : ℝ) * (x ⟨k.1, hk⟩ - α j))) : ℝ) ≤
          (M : ℝ) * (x ⟨k.1, hk⟩ - α j) :=
      Int.floor_le _
    have hne :
        ((Int.floor ((M : ℝ) * (x ⟨k.1, hk⟩ - α j))) : ℝ) ≠
          (M : ℝ) * (x ⟨k.1, hk⟩ - α j) := by
      intro hEq
      apply hx
      exact ⟨k, Int.floor ((M : ℝ) * (x ⟨k.1, hk⟩ - α j)), hEq.symm⟩
    exact lt_of_le_of_ne hle hne
  · simp [p]

omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
/-- The shifted-cell unions `strom_U' M α i` cover the simplex provided the shifts are pairwise
    incongruent modulo `ℚ`.  This is the combinatorial heart of Stromquist's unusual case:
    if a simplex point lies outside every `strom_U' i`, then for each agent `j` the point must lie
    on a `j`-boundary hyperplane.  There are only `n - 1` independent simplex coordinates, so this
    is impossible for `n` agents when distinct agents cannot share a boundary coordinate. -/
private lemma strom_approx_covers
    (α : Fin n → ℝ)
    (hα : Pairwise fun j k : Fin n => Irrational (α j - α k))
    (M : ℕ) (hM : 0 < M) :
    stdSimplex ℝ (Fin n) ⊆ ⋃ i, strom_U' n hn μ M α i := by
  intro x hx
  by_contra hxU
  have hxU' : ∀ i : Fin n, x ∉ strom_U' n hn μ M α i := by
    intro i hi
    exact hxU (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hxBoundary : ∀ j : Fin n, strom_onBoundary n hn M α j x := by
    intro j
    by_contra hj
    let p : Fin (n - 1) → ℤ := fun k =>
      Int.floor ((M : ℝ) * (x ⟨k.1, by omega⟩ - α j))
    have hxCell : x ∈ strom_cellOpen n hn M α j p :=
      strom_mem_cellOpen_of_not_onBoundary n hn α M x j hj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (strom_A_covers n μ j hx)
    have hHit : strom_cellHits n hn μ M α j i p := by
      refine ⟨x, ?_⟩
      exact ⟨⟨hxCell, hx⟩, hi⟩
    have hOwnerNeNone : strom_cellOwner n hn μ M α j p ≠ none := by
      classical
      have hex : ∃ i : Fin n, strom_cellHits n hn μ M α j i p := ⟨i, hHit⟩
      unfold strom_cellOwner
      simp [hex]
    classical
    cases hOwner : strom_cellOwner n hn μ M α j p with
    | none =>
        exact (hOwnerNeNone hOwner).elim
    | some i0 =>
        have hxB : x ∈ strom_B' n hn μ M α i0 j := by
          refine Set.mem_iUnion.mpr ⟨p, ?_⟩
          simp [hOwner, hxCell]
        have hxUi0 : x ∈ strom_U' n hn μ M α i0 := Set.mem_iUnion.mpr ⟨j, hxB⟩
        exact hxU' i0 hxUi0
  choose k z hk using hxBoundary
  have hcard : Fintype.card (Fin (n - 1)) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j, j', hjj', hkk⟩ := Fintype.exists_ne_map_eq_of_card_lt k hcard
  have hk_j :
      (M : ℝ) * (x ⟨(k j).1, by omega⟩ - α j) = z j :=
    hk j
  have hk_j' :
      (M : ℝ) * (x ⟨(k j).1, by omega⟩ - α j') = z j' := by
    simpa [hkk] using hk j'
  have hsub : (M : ℝ) * (α j - α j') = ((z j' - z j : ℤ) : ℝ) := by
    have hk_j_lin :
        (M : ℝ) * x ⟨(k j).1, by omega⟩ - (M : ℝ) * α j = z j := by
      linarith
    have hk_j'_lin :
        (M : ℝ) * x ⟨(k j).1, by omega⟩ - (M : ℝ) * α j' = z j' := by
      linarith
    have hαj : (M : ℝ) * α j = (M : ℝ) * x ⟨(k j).1, by omega⟩ - z j := by
      linarith
    have hαj' : (M : ℝ) * α j' = (M : ℝ) * x ⟨(k j).1, by omega⟩ - z j' := by
      linarith
    calc
      (M : ℝ) * (α j - α j') = (M : ℝ) * α j - (M : ℝ) * α j' := by ring
      _ = (((M : ℝ) * x ⟨(k j).1, by omega⟩ - z j) -
            ((M : ℝ) * x ⟨(k j).1, by omega⟩ - z j')) := by rw [hαj, hαj']
      _ = (z j' : ℝ) - (z j : ℝ) := by ring
      _ = ((z j' - z j : ℤ) : ℝ) := by rw [Int.cast_sub]
  have hrepr : α j - α j' = ((z j' - z j : ℤ) : ℝ) / M := by
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    apply (eq_div_iff hM0).2
    nlinarith [hsub]
  have hirr := (irrational_iff_ne_rational (α j - α j')).mp (hα hjj')
  exact hirr (z j' - z j) M (by exact_mod_cast (Nat.ne_of_gt hM)) hrepr

/-! #### Helper lemmas for the unusual case -/

/-- There exist shifts with pairwise irrational differences. -/
private lemma irrational_shifts_exist :
    ∃ α : Fin n → ℝ, Pairwise fun j k : Fin n => Irrational (α j - α k) := by
      by_contra! h_contra;
      -- Consider the shifts α j = j * sqrt(2). Then α j - α k = (j - k) * sqrt(2), which is irrational if j ≠ k.
      set α : Fin n → ℝ := fun j => (j : ℝ) * Real.sqrt 2;
      refine h_contra α ?_;
      intro j k hjk; simp [α]; (
      simpa [ sub_mul ] using irrational_sqrt_two.ratCast_mul ( show ( j - k : ℚ ) ≠ 0 from sub_ne_zero_of_ne <| by simpa [ Fin.ext_iff ] using hjk ))

/-- Two simplex points lying in the same shifted cell are uniformly close:
    their sup-distance is at most `↑n / ↑M`. -/
private lemma strom_same_cell_dist_bound (M : ℕ) (hM : 0 < M) (α : Fin n → ℝ) (j : Fin n)
    (p : Fin (n - 1) → ℤ) (x y : Fin n → ℝ)
    (hx : x ∈ strom_cellOpen n hn M α j p) (hy : y ∈ strom_cellOpen n hn M α j p)
    (hxs : x ∈ stdSimplex ℝ (Fin n)) (hys : y ∈ stdSimplex ℝ (Fin n)) :
    dist x y ≤ n / M := by
      -- By definition of `strom_cellOpen`, we have that for all `k : Fin (n - 1)`, `|x k - y k| ≤ 1 / M`.
      have h_diff_k : ∀ k : Fin (n - 1), |x ⟨k.1, by omega⟩ - y ⟨k.1, by omega⟩| ≤ 1 / (M : ℝ) := by
        intro k; specialize hx k; specialize hy k; rw [ abs_sub_le_iff ] ; constructor <;> nlinarith [ hx.1, hx.2, hy.1, hy.2, show ( M : ℝ ) ≥ 1 by exact_mod_cast hM, mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( M : ℝ ) ≠ 0 ) ] ;
      -- By definition of `stdSimplex`, we have that `x (Fin.mk (n - 1) (by omega)) = 1 - ∑ k : Fin (n - 1), x k` and `y (Fin.mk (n - 1) (by omega)) = 1 - ∑ k : Fin (n - 1), y k`.
      have h_diff_n : |x (Fin.mk (n - 1) (by omega)) - y (Fin.mk (n - 1) (by omega))| ≤ (n - 1) / (M : ℝ) := by
        have h_diff_n : x (Fin.mk (n - 1) (by omega)) = 1 - ∑ k : Fin (n - 1), x ⟨k.1, by omega⟩ ∧ y (Fin.mk (n - 1) (by omega)) = 1 - ∑ k : Fin (n - 1), y ⟨k.1, by omega⟩ := by
          rcases n <;> simp_all +decide [ Fin.sum_univ_castSucc, stdSimplex ];
          exact ⟨ eq_sub_of_add_eq' hxs.2, eq_sub_of_add_eq' hys.2 ⟩;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ abs_sub_comm ];
        · contradiction;
        · exact le_trans ( by simpa [ Finset.sum_sub_distrib ] using Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum fun i _ => h_diff_k i ) <| by
            change ((Fintype.card (Fin (n + 1)) : ℕ) : ℝ) * (M : ℝ)⁻¹ ≤ ((n : ℝ) + 1) * (M : ℝ)⁻¹
            norm_num [Fintype.card_fin]
      rw [ dist_pi_le_iff ];
      · intro i; by_cases hi : i.val < n - 1 <;> simp_all +decide [ dist_eq_norm ] ;
        · exact le_trans ( h_diff_k ⟨ i, hi ⟩ ) ( by rw [ inv_eq_one_div, div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] );
        · convert h_diff_n.trans ( div_le_div_of_nonneg_right ( sub_le_self _ zero_le_one ) ( Nat.cast_nonneg _ ) ) using 1;
          grind +splitImp;
      · positivity

/-
For `M` sufficiently large, the approximate preference union `strom_U' M α i` does not
    intersect the face opposite vertex `i`. This is the face-avoidance precondition
    needed to apply `kkm_open_cover` to the approximate sets.

    **Proof sketch**: By `strom_A_avoids_face`, `simplexFaceOpp i` and `strom_A i j` are
    disjoint closed subsets, with `simplexFaceOpp i` compact.  Hence the distance between
    them is some `δ > 0`.  For `M` large enough (`↑n / ↑M < δ`), any cell containing a
    face point has diameter less than `δ`, so the cell cannot hit `strom_A i j`.
    Consequently, no cell owner equals `i`, and the face is disjoint from `strom_U' M α i`.
-/
private lemma strom_face_avoidance_U'_large_M (α : Fin n → ℝ)
    (hα : Pairwise fun j k : Fin n => Irrational (α j - α k))
    (hpos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M ≥ M₀, ∀ i, simplexFaceOpp i ⊆ (strom_U' n hn μ M α i)ᶜ := by
      -- For each i and j, `simplexFaceOpp i` and `strom_A n μ i j ∩ stdSimplex ℝ (Fin n)` are disjoint (by `strom_A_avoids_face`), with `simplexFaceOpp i` compact (closed subset of compact simplex) and `strom_A n μ i j` closed (by `strom_A_closed`). Therefore, there exists δ_{i,j} > 0 such that every point in `simplexFaceOpp i` is at distance ≥ δ_{i,j} from `strom_A n μ i j`.
      have h_dist_pos (i : Fin n) (j : Fin n) :
          ∃ δ > 0, ∀ x ∈ simplexFaceOpp i, ∀ y ∈ strom_A n μ i j ∩ stdSimplex ℝ (Fin n), δ ≤ dist x y := by
            have h_compact : IsCompact (simplexFaceOpp i) := by
              refine' IsCompact.inter_left _ _;
              · exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( isClosed_Ici.preimage continuous_id' |> IsClosed.inter <| isClosed_eq ( continuous_finset_sum _ fun _ _ => continuous_apply _ ) continuous_const ) fun x hx => ⟨ fun _ => hx.1 _, fun _ => hx.2 ▸ Finset.single_le_sum ( fun a _ => hx.1 a ) ( Finset.mem_univ _ ) ⟩;
              · exact isClosed_eq ( continuous_apply i ) continuous_const
            have h_closed : IsClosed (strom_A n μ i j ∩ stdSimplex ℝ (Fin n)) := by
              exact IsClosed.inter ( strom_A_closed n μ i j ) ( isClosed_stdSimplex ℝ (Fin n) )
            have h_disjoint : Disjoint (simplexFaceOpp i) (strom_A n μ i j ∩ stdSimplex ℝ (Fin n)) := by
              exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by have := strom_A_avoids_face n μ i j ( hpos j ) ; exact this.subset ⟨ hx₂.1, hx₁ ⟩ ;
            contrapose! h_disjoint;
            rw [ Set.not_disjoint_iff ];
            have h_seq : ∃ seq : ℕ → (Fin n → ℝ), (∀ k, seq k ∈ simplexFaceOpp i) ∧ ∃ seq' : ℕ → (Fin n → ℝ), (∀ k, seq' k ∈ strom_A n μ i j ∩ stdSimplex ℝ (Fin n)) ∧ Filter.Tendsto (fun k => dist (seq k) (seq' k)) Filter.atTop (nhds 0) := by
              choose! seq seq' hseq hseq' hseq'' using h_disjoint;
              exact ⟨ fun k => seq ( 1 / 2 ^ k ), fun k => seq' _ ( by positivity ), fun k => hseq ( 1 / 2 ^ k ), fun k => hseq' _ ( by positivity ), squeeze_zero ( fun k => dist_nonneg ) ( fun k => le_of_lt ( hseq'' _ ( by positivity ) ) ) ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) ⟩;
            obtain ⟨ seq, hseq₁, seq', hseq₂, hseq₃ ⟩ := h_seq;
            have h_seq_conv : ∃ x ∈ simplexFaceOpp i, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun k => seq (subseq k)) Filter.atTop (nhds x) := by
              exact h_compact.isSeqCompact fun k => hseq₁ k;
            obtain ⟨ x, hx₁, subseq, hsubseq₁, hsubseq₂ ⟩ := h_seq_conv;
            have h_seq_conv' : Filter.Tendsto (fun k => seq' (subseq k)) Filter.atTop (nhds x) := by
              have h_seq_conv' : Filter.Tendsto (fun k => dist (seq (subseq k)) (seq' (subseq k))) Filter.atTop (nhds 0) := by
                exact hseq₃.comp hsubseq₁.tendsto_atTop;
              rw [ tendsto_iff_dist_tendsto_zero ] at *;
              exact squeeze_zero ( fun _ => dist_nonneg ) ( fun k => dist_triangle_left _ _ _ ) ( by simpa using h_seq_conv'.add hsubseq₂ );
            exact ⟨ x, hx₁, h_closed.mem_of_tendsto h_seq_conv' ( Filter.Eventually.of_forall fun k => hseq₂ _ ) ⟩;
      -- Take δ = min over all (i, j) of δ_{i,j} > 0 (finite minimum of positive values).
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ i j, ∀ x ∈ simplexFaceOpp i, ∀ y ∈ strom_A n μ i j ∩ stdSimplex ℝ (Fin n), δ ≤ dist x y := by
        choose! δ hδ_pos hδ using h_dist_pos;
        rcases n with ( _ | n ) <;> norm_num at *;
        exact ⟨ Finset.min' ( Finset.univ.image fun p : Fin ( n + 1 ) × Fin ( n + 1 ) => δ p.1 p.2 ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ( 0, 0 ) ) ⟩, by have := Finset.min'_mem ( Finset.univ.image fun p : Fin ( n + 1 ) × Fin ( n + 1 ) => δ p.1 p.2 ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ( 0, 0 ) ) ⟩ ; aesop, fun i j x hx y hy hy' => Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ ( i, j ) ) ) |> le_trans <| hδ i j x hx y hy hy' ⟩;
      -- Choose M₀ > n/δ.
      obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M ≥ M₀, n / (M : ℝ) < δ := by
        exact ⟨ ⌊n / δ⌋₊ + 1, Nat.succ_pos _, fun M hM => by rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( n / δ ), show ( M : ℝ ) ≥ ⌊n / δ⌋₊ + 1 by exact_mod_cast hM, mul_div_cancel₀ ( n : ℝ ) hδ_pos.ne' ] ⟩;
      refine' ⟨ M₀, hM₀.1, fun M hM i x hx => _ ⟩;
      simp +decide [ strom_U', strom_B' ];
      intro j p hp hx';
      obtain ⟨ y, hy₁, hy₂ ⟩ := strom_cellOwner_eq_some_imp_hits n hn μ M α j i p hp;
      have := strom_same_cell_dist_bound n hn M ( by linarith ) α j p x y hx' hy₁.1 ( by
        exact hx.2 ) hy₁.2;
      linarith [ hM₀.2 M hM, hδ i j x hx y ⟨ hy₂, hy₁.2 ⟩ ]

/-
For each `M` satisfying face avoidance, applying KKM to the approximate preference sets
    `strom_U' M α` yields a simplex point `x_M` and a permutation `σ_M` such that, for
    every agent `j`, a witness `y_j ∈ strom_A (σ_M.symm j) j` exists within distance
    `↑n / ↑M` of `x_M`.

    This is the approximate analogue of the usual-case KKM argument.
-/
omit [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] in
private lemma strom_approx_witnesses (α : Fin n → ℝ)
    (hα : Pairwise fun j k : Fin n => Irrational (α j - α k))
    (_hpos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1))
    (M : ℕ) (hM : 0 < M)
    (hface_avoidance : ∀ i, simplexFaceOpp i ⊆ (strom_U' n hn μ M α i)ᶜ) :
    ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n)) (perm : Fin n ≃ Fin n),
      ∀ j : Fin n, ∃ y ∈ strom_A n μ (perm.symm j) j,
        y ∈ stdSimplex ℝ (Fin n) ∧ dist x y ≤ n / M := by
          obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, x ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, x ∈ strom_U' n hn μ M α i := by
            apply kkm_open_cover hn (strom_U' n hn μ M α) (strom_U'_open n hn μ M α) hface_avoidance (strom_approx_covers n hn μ α hα M hM);
          obtain ⟨perm, hperm⟩ : ∃ perm : Equiv.Perm (Fin n), ∀ i, x ∈ strom_B' n hn μ M α i (perm i) := by
            have h_perm : ∀ i, ∃ j, x ∈ strom_B' n hn μ M α i j := by
              intro i; specialize hx; have := hx.2 i; simp_all +decide [ strom_U' ] ;
            choose perm hperm using h_perm;
            have h_inj : Function.Injective perm := by
              intros i j hij;
              have := strom_B'_disjoint_over_i n hn μ M α ( perm i ) i j; simp_all +decide [ Set.disjoint_left ] ;
              exact Classical.not_not.1 fun hi => this hi ( by simpa [ hij ] using hperm i ) ( by simpa [ hij ] using hperm j );
            exact ⟨ Equiv.ofBijective perm ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩, hperm ⟩;
          refine' ⟨ x, hx.1, perm, _ ⟩;
          intro j
          obtain ⟨p, hp⟩ : ∃ p : Fin (n - 1) → ℤ, x ∈ strom_cellOpen n hn M α (perm (perm.symm j)) p ∧ strom_cellOwner n hn μ M α (perm (perm.symm j)) p = some (perm.symm j) := by
            specialize hperm (perm.symm j);
            unfold strom_B' at hperm; aesop;
          obtain ⟨y, hy⟩ : ∃ y ∈ strom_cellOpen n hn M α (perm (perm.symm j)) p ∩ stdSimplex ℝ (Fin n) ∩ strom_A n μ (perm.symm j) j, True := by
            have := strom_cellOwner_eq_some_imp_hits n hn μ M α ( perm ( perm.symm j ) ) ( perm.symm j ) p hp.2; aesop;
          exact ⟨ y, hy.1.2, hy.1.1.2, strom_same_cell_dist_bound n hn M hM α ( perm ( perm.symm j ) ) p x y hp.1 hy.1.1.1 hx.1 hy.1.1.2 ⟩

/-
**Approximation-to-exact limit argument**: if for every `ε > 0` there exists a simplex
    point, a permutation, and witnesses within `ε` of the preference sets, then there
    exists an exact solution.

    Uses compactness of the standard simplex to extract a convergent subsequence,
    finiteness of `Fin n ≃ Fin n` to stabilize the permutation, and closedness of
    `strom_A` to pass to the limit.
-/
private lemma strom_approx_to_exact
    (h : ∀ ε > (0:ℝ), ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n))
        (e : Fin n ≃ Fin n),
      ∀ j : Fin n, ∃ y ∈ strom_A n μ (e.symm j) j, dist x y < ε) :
    ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n)) (e : Fin n ≃ Fin n),
      ∀ j : Fin n, x ∈ strom_A n μ (e.symm j) j := by
        have h_compact : IsCompact (stdSimplex ℝ (Fin n)) := by
          exact isCompact_stdSimplex ℝ (Fin n);
        have h_seq : ∃ (x : ℕ → Fin n → ℝ), (∀ k, x k ∈ stdSimplex ℝ (Fin n)) ∧ ∃ (e : ℕ → Fin n ≃ Fin n), ∀ k, ∀ j, ∃ y ∈ strom_A n μ (e k |>.symm j) j, dist (x k) y < 1 / (k + 1) := by
          choose x hx e he using h;
          exact ⟨ fun k => x ( 1 / ( k + 1 ) ) ( by positivity ), fun k => hx _ _, fun k => e ( 1 / ( k + 1 ) ) ( by positivity ), fun k j => he _ _ _ ⟩;
        obtain ⟨x, hx_seq, e, he⟩ := h_seq
        obtain ⟨x_star, hx_star⟩ : ∃ x_star ∈ stdSimplex ℝ (Fin n), ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧ Filter.Tendsto (fun r => x (subseq r)) Filter.atTop (nhds x_star) := by
          have := h_compact.isSeqCompact fun k => hx_seq k; aesop;
        obtain ⟨ subseq, hsubseq_mono, hsubseq_tendsto ⟩ := hx_star.2
        have h_e_const : ∃ e₀ : Fin n ≃ Fin n, Set.Infinite {r | e (subseq r) = e₀} := by
          by_contra h_contra; push_neg at h_contra; (
          exact Set.infinite_univ ( Set.Finite.subset ( Set.Finite.biUnion ( Set.toFinite ( Set.univ : Set ( Fin n ≃ Fin n ) ) ) fun e₀ _ => h_contra e₀ ) fun r _ => by simp +decide ));
        obtain ⟨ e₀, he₀ ⟩ := h_e_const
        obtain ⟨ subsubseq, hsubsubseq_mono, hsubsubseq_tendsto ⟩ : ∃ subsubseq : ℕ → ℕ, StrictMono subsubseq ∧ ∀ r, e (subseq (subsubseq r)) = e₀ := by
          exact ⟨ fun r => Nat.recOn r ( Nat.find <| he₀.nonempty ) fun r ih => Nat.find <| he₀.exists_gt ih, strictMono_nat_of_lt_succ fun r => Nat.find_spec ( he₀.exists_gt _ ) |>.2, fun r => Nat.recOn r ( Nat.find_spec <| he₀.nonempty ) fun r ih => Nat.find_spec ( he₀.exists_gt _ ) |>.1 ⟩;
        have h_y_tendsto : ∀ j, Filter.Tendsto (fun r => Classical.choose (he (subseq (subsubseq r)) j)) Filter.atTop (nhds x_star) := by
          intro j
          have h_dist : Filter.Tendsto (fun r => dist (x (subseq (subsubseq r))) (Classical.choose (he (subseq (subsubseq r)) j))) Filter.atTop (nhds 0) := by
            exact squeeze_zero ( fun _ => dist_nonneg ) ( fun r => Classical.choose_spec ( he ( subseq ( subsubseq r ) ) j ) |>.2.le ) ( tendsto_one_div_add_atTop_nhds_zero_nat.comp <| hsubseq_mono.tendsto_atTop.comp hsubsubseq_mono.tendsto_atTop );
          have h_y_tendsto : Filter.Tendsto (fun r => x (subseq (subsubseq r)) - Classical.choose (he (subseq (subsubseq r)) j)) Filter.atTop (nhds 0) := by
            exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa [ dist_eq_norm ] using h_dist );
          simpa using h_y_tendsto.neg.add ( hsubseq_tendsto.comp hsubsubseq_mono.tendsto_atTop );
        use x_star, hx_star.1, e₀;
        intro j
        have h_y_in_A : ∀ r, Classical.choose (he (subseq (subsubseq r)) j) ∈ strom_A n μ (e₀.symm j) j := by
          exact fun r => by simpa only [ hsubsubseq_tendsto r ] using Classical.choose_spec ( he ( subseq ( subsubseq r ) ) j ) |>.1;
        exact IsClosed.mem_of_tendsto ( strom_A_closed n μ ( e₀.symm j ) j ) ( h_y_tendsto j ) ( Filter.Eventually.of_forall h_y_in_A )

omit [∀ i, NoAtoms (μ i)] in
private lemma strom_ef_from_pref_point
    (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (e : Fin n ≃ Fin n)
    (hpref : ∀ j : Fin n, x ∈ strom_A n μ (e.symm j) j)
    (hsupp : ∀ j : Fin n, μ j = (μ j).restrict (Set.Ico 0 1)) :
    ∃ A : Allocation (Fin n) ℝ,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  -- Let's define the allocation A based on x and the permutation e.
  use fun j => if j = ⟨0, hn⟩ then strom_piece n x (e.symm j) ∪ (Set.Iio 0 ∪ Set.Ici 1) else strom_piece n x (e.symm j);
  constructor;
  · constructor;
    · intro i; split_ifs <;> [ exact MeasurableSet.union ( measurableSet_Ico ) ( MeasurableSet.union ( measurableSet_Iio ) ( measurableSet_Ici ) ) ; exact measurableSet_Ico ] ;
    · intro i j hij; split_ifs <;> simp +decide [ *, Set.disjoint_left ] ;
      · grind;
      · intro a ha hb;
        rcases ha with ( ha | ha | ha );
        · have := strom_piece_partition n x hx;
          exact Set.disjoint_left.mp ( this.2.1 _ _ ( by simpa [ ‹i = ⟨ 0, hn ⟩ › ] using hij ) ) ha hb;
        · unfold strom_piece at hb; norm_num at hb; linarith [ show 0 ≤ ∑ k ∈ Finset.univ.filter ( fun k => k < e.symm j ), x k from Finset.sum_nonneg fun _ _ => hx.1 _ ] ;
        · contrapose! ha;
          refine' lt_of_lt_of_le hb.2 _;
          exact hx.2 ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => hx.1 _;
      · intro a ha; have := strom_piece_partition n x hx; simp +decide [ *, Set.disjoint_left ] at this ⊢;
        exact ⟨ this.2.1 _ _ ( by simp [*] ) ha, by have := this.2.2.subset ( Set.mem_iUnion_of_mem ( e.symm i ) ha ) ; exact this.1, by have := this.2.2.subset ( Set.mem_iUnion_of_mem ( e.symm i ) ha ) ; exact this.2 ⟩;
      · intro a ha hb; have := strom_piece_partition n x hx; simp +decide [ Set.disjoint_left ] at this;
        exact this.2.1 _ _ ( by simp [ e.symm.injective.ne hij ] ) ha hb;
    · ext y;
      by_cases hy : y ∈ Set.Ico 0 1;
      · have := strom_piece_partition n x hx;
        replace this := Set.ext_iff.mp this.2.2 y; simp +decide [ hy ] at this ⊢;
        obtain ⟨ i, hi ⟩ := this; use e i; simp +decide ;
        split_ifs <;> simp +decide [ hi ];
      · simp;
        use ⟨0, hn⟩;
        grind;
  · intro i j;
    have hext : ∀ i, μ i (Set.Iio 0 ∪ Set.Ici 1) = 0 := by
      intro i; specialize hsupp i; rw [ hsupp ] ; simp +decide [ MeasureTheory.Measure.restrict_apply ] ;
      exact MeasureTheory.measure_mono_null ( fun x hx => by cases hx.1 <;> norm_num at * <;> linarith ) ( MeasureTheory.measure_empty );
    have hext : ∀ j, (μ i (strom_piece n x (e.symm j) ∪ (Set.Iio 0 ∪ Set.Ici 1))) = (μ i (strom_piece n x (e.symm j))) := by
      intro j;
      rw [ MeasureTheory.measure_union₀ ];
      · rw [ hext i, add_zero ];
      · exact MeasurableSet.nullMeasurableSet ( measurableSet_Iio.union measurableSet_Ici );
      · exact MeasureTheory.measure_mono_null ( fun x hx => by simp +decide at hx ⊢; tauto ) ( hext i );
    convert hpref i ( e.symm j ) using 1;
    simp +decide [ MeasureValuation, strom_value ];
    split_ifs <;> simp +decide [ hext ]

private lemma strom_common_pref_exists
    (hn : 0 < n)
    (hpos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1))
    (_hsupp : ∀ j : Fin n, μ j = (μ j).restrict (Set.Ico 0 1)) :
    ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n)) (e : Fin n ≃ Fin n),
      ∀ j : Fin n, x ∈ strom_A n μ (e.symm j) j := by
  have hface : ∀ i, simplexFaceOpp i ⊆ (strom_U n μ i)ᶜ := by
    intro i x hx_face hx_U
    exact Set.eq_empty_iff_forall_notMem.mp (strom_U_avoids_face n μ i hpos) x ⟨hx_U, hx_face⟩
  by_cases hcover : stdSimplex ℝ (Fin n) ⊆ ⋃ i, strom_U n μ i
  · obtain ⟨x, hx_simp, hx_U⟩ := kkm_open_cover hn (strom_U n μ) (strom_U_open n μ) hface hcover
    obtain ⟨assign, hinj, hassign⟩ := strom_fair_assignment n μ x hx_U
    have hbij := Finite.injective_iff_bijective.mp hinj
    refine ⟨x, hx_simp, Equiv.ofBijective assign hbij, fun j => ?_⟩
    have h := (hassign ((Equiv.ofBijective assign hbij).symm j)).1
    rwa [show assign ((Equiv.ofBijective assign hbij).symm j) = j from
      (Equiv.ofBijective assign hbij).apply_symm_apply j] at h
  · -- Unusual case: use approximate sets + compactness
    obtain ⟨α, hα⟩ := @irrational_shifts_exist n
    obtain ⟨M₀, hM₀_pos, hM₀_face⟩ :=
      @strom_face_avoidance_U'_large_M n hn μ _ _ α hα hpos
    -- Apply the approximation-to-exact limit argument
    exact @strom_approx_to_exact n μ _ _ fun ε hε => by
      -- Choose M large enough: n/M ≤ ε and M ≥ M₀
      set M := ⌈↑n / ε⌉₊ + M₀ + 1 with hM_def
      have hMge : M₀ ≤ M := by omega
      have hMnat : 0 < M := by omega
      have hnM : (↑n : ℝ) / ↑M < ε := by
        rw [div_lt_iff₀ (by exact_mod_cast hMnat : (0:ℝ) < ↑M)]
        calc (↑n : ℝ) = ↑n / ε * ε := by rw [div_mul_cancel₀ _ (ne_of_gt hε)]
          _ ≤ ↑⌈↑n / ε⌉₊ * ε := by
              exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε.le
          _ < ↑M * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              exact_mod_cast show ⌈↑n / ε⌉₊ < M by omega
          _ = ε * ↑M := by ring
      obtain ⟨x, hx, perm, hperm⟩ :=
        strom_approx_witnesses (n := n) (hn := hn) (μ := μ) α hα hpos M hMnat (hM₀_face M hMge)
      exact ⟨x, hx, perm, fun j => by
        obtain ⟨y, hy_mem, _, hy_dist⟩ := hperm j
        exact ⟨y, hy_mem, lt_of_le_of_lt hy_dist hnM⟩⟩

/-- **Unusual case**: construct an envy-free allocation by Stromquist's shifted-cell
    approximation.

    The proof follows the standard compactness completion of Stromquist's argument.

    1. Choose shifts `α_j` with pairwise irrational differences
       (`irrational_shifts_exist`).
    2. For sufficiently fine meshes `M`, show the approximate open cover `strom_U' M α`
       avoids the forbidden faces (`strom_face_avoidance_U'_large_M`).
    3. Apply KKM to each such approximate cover and extract approximate witness data:
       a simplex point together with a permutation of pieces (`strom_approx_witnesses`).
    4. Pass to the limit using compactness of the simplex and closedness of the exact
       preference sets (`strom_approx_to_exact`) to obtain a common preference point for the
       original sets `strom_A`.
    5. Turn that common preference point into an envy-free allocation
       (`strom_ef_from_pref_point`).

    A small extra case split handles agents whose measure of `Set.Ico 0 1` is zero: they are
    temporarily replaced by a fixed nonatomic reference measure to produce the common preference
    point, and then one checks that such agents value every piece equally anyway. -/
private lemma strom_unusual_case
    (hn : 0 < n)
    (hsupp : ∀ j : Fin n, μ j = (μ j).restrict (Set.Ico 0 1)) :
    ∃ A : Allocation (Fin n) ℝ,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  have h_common_pref : ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n)) (e : Fin n ≃ Fin n),
    ∀ j : Fin n, x ∈ strom_A n μ (e.symm j) j := by
      by_cases h_pos : ∀ j : Fin n, 0 < μ j (Set.Ico 0 1);
      · exact strom_common_pref_exists n μ hn h_pos hsupp;
      · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, μ j₀ (Set.Ico 0 1) = 0 := by
          exact by push Not at h_pos; exact h_pos.imp fun j hj => le_antisymm hj zero_le;
        -- Zero-measure agents are indifferent between all pieces, so we may replace them
        -- temporarily by a fixed nonatomic reference measure to construct a common point.
        have h_zero_measure : ∀ j : Fin n, μ j (Set.Ico 0 1) = 0 → ∀ i : Fin n, ∀ x : Fin n → ℝ, strom_value n μ x j i = 0 := by
          intros j hj i x
          have h_zero_measure : μ j (strom_piece n x i) = 0 := by
            rw [ hsupp j, MeasureTheory.Measure.restrict_apply' ];
            · exact MeasureTheory.measure_mono_null ( fun y hy => hy.2 ) hj;
            · norm_num;
          unfold strom_value; simp +decide [ h_zero_measure ] ;
        obtain ⟨x, hx, e, hpref⟩ : ∃ (x : Fin n → ℝ) (_ : x ∈ stdSimplex ℝ (Fin n)) (e : Fin n ≃ Fin n),
          ∀ j : Fin n, μ j (Set.Ico 0 1) > 0 → x ∈ strom_A n μ (e.symm j) j := by
            have := @strom_common_pref_exists ( n := n ) ( μ := fun j => if 0 < μ j ( Set.Ico 0 1 ) then μ j else MeasureTheory.Measure.restrict ( MeasureTheory.MeasureSpace.volume ) ( Set.Ico 0 1 ) ) ?_ ?_ ?_;
            · refine' this _ _ |> fun ⟨ x, hx, e, he ⟩ => ⟨ x, hx, e, fun j hj => _ ⟩;
              · intro j; split_ifs <;> norm_num;
                assumption;
              · intro j; split_ifs <;> simp +decide [ ← hsupp j ] ;
              · convert he j using 1;
                ext; simp [strom_A];
                unfold strom_value; simp +decide [ hj ] ;
            · intro i; by_cases hi : 0 < μ i ( Set.Ico 0 1 ) <;> simp +decide [ hi ] ;
              · infer_instance;
              · infer_instance;
            · intro i; by_cases hi : 0 < μ i ( Set.Ico 0 1 ) <;> simp +decide [ hi ] ;
              · infer_instance;
              · infer_instance;
            · exact hn;
        refine' ⟨ x, hx, e, fun j => _ ⟩;
        by_cases hj : μ j (Set.Ico 0 1) > 0;
        · exact hpref j hj;
        · exact fun k => by simp +decide [ h_zero_measure j ( le_antisymm ( le_of_not_gt hj ) zero_le ) ] ;
  exact strom_ef_from_pref_point n μ hn _ h_common_pref.choose_spec.1 _ h_common_pref.choose_spec.2.choose_spec hsupp

end StromquistProof

/-! ### EF existence (general n agents) -/

/-- **EF allocations always exist** for any finite number of agents with non-atomic finite
    measures on `[0,1]`.

    This is the fundamental existence theorem of divisible fair division (Stromquist 1980).

    **Proof** (via Stromquist's KKM argument, sketched):

    1. Push each measure on `[0,1]` forward along `Subtype.val : I → ℝ`.
    2. Reindex agents as `Fin n` (n = Fintype.card N) via `Fintype.equivFin N`.
    3. Apply `strom_unusual_case` to get an EF allocation for `Fin n` agents.
       (`strom_unusual_case` subsumes the usual case: it handles both via the approximation
       argument, which reduces to `strom_usual_case` when the U sets already cover the simplex.)
    4. Pull the allocation back to `[0,1]` along `Subtype.val` and transport it back along
       the bijection.

    See the module docstring for the full proof strategy. -/
theorem ef_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NoAtoms (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  -- Step 1: reindex via the canonical bijection e : N ≃ Fin n
  set n := Fintype.card N
  set e := Fintype.equivFin N
  have hn : 0 < n := Fintype.card_pos
  let μ' : Fin n → Measure ℝ := fun j => (μ (e.symm j)).map Subtype.val
  haveI : ∀ j : Fin n, IsFiniteMeasure (μ' j) := fun j => by
    dsimp [μ']
    infer_instance
  haveI : ∀ j : Fin n, NoAtoms (μ' j) := fun j => by
    dsimp [μ']
    infer_instance
  -- Step 2: apply the Stromquist construction for Fin n agents on the ambient real line
  have hsupp' : ∀ j : Fin n, μ' j = (μ' j).restrict (Set.Ico 0 1) := by
    intro j; rw [ Measure.restrict_eq_self_of_ae_mem ] ; simp +decide [*];
    constructor <;> rw [ MeasureTheory.ae_map_iff ] <;> norm_num;
    any_goals exact measurableSet_Iio.mem;
    · exact Filter.Eventually.of_forall fun x => x.2.1;
    · exact measurable_subtype_coe.aemeasurable;
    · exact measurableSet_Ici.mem;
    · convert MeasureTheory.measure_singleton ⟨ 1, by norm_num ⟩ |> MeasureTheory.measure_mono_null ( show { a : I | ¬a < 1 } ⊆ { ⟨ 1, by norm_num ⟩ } from fun x hx => ?_ ) using 1;
      · exact le_antisymm ( Subtype.mk_le_mk.mpr ( show x.val ≤ 1 from x.2.2 ) ) ( not_lt.mp hx );
      · grind;
    · exact measurable_subtype_coe.aemeasurable
  obtain ⟨A', hA', hef'⟩ := strom_unusual_case n μ' hn hsupp'
  -- Step 3: pull the allocation back to `[0,1]` and transport along e
  refine ⟨fun i => Subtype.val ⁻¹' A' (e i), ?_, ?_⟩
  · refine ⟨fun i => (hA'.measurable (e i)).preimage measurable_subtype_coe,
            fun i j hij => (hA'.disjoint (e i) (e j) (fun h => hij (e.injective h))).preimage _,
            ?_⟩
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hA'.cover ▸ Set.mem_univ (x : ℝ))
    exact ⟨e.symm j, by simpa [e.apply_symm_apply] using hj⟩
  · -- IsEnvyFree: transport the EF condition along e
    intro i j
    show (MeasureValuation μ).val i (Subtype.val ⁻¹' A' (e j)) ≤
        (MeasureValuation μ).val i (Subtype.val ⁻¹' A' (e i))
    have hμ_i : μ' (e i) = (μ i).map Subtype.val := by
      dsimp [μ']
      rw [e.symm_apply_apply]
    calc
      (MeasureValuation μ).val i (Subtype.val ⁻¹' A' (e j))
          = μ i (Subtype.val ⁻¹' A' (e j)) := rfl
      _ = μ' (e i) (A' (e j)) := by
            rw [hμ_i, Measure.map_apply measurable_subtype_coe (hA'.measurable (e j))]
      _ ≤ μ' (e i) (A' (e i)) := hef' (e i) (e j)
      _ = μ i (Subtype.val ⁻¹' A' (e i)) := by
            rw [hμ_i, Measure.map_apply measurable_subtype_coe (hA'.measurable (e i))]

/-! ### Corollaries -/

/-- EF implies proportional (corollary of `IsEnvyFree.isProportional`): the EF allocation
    produced by `ef_exists` is also proportional.

    This is an immediate consequence of `IsEnvyFree.isProportional`, recorded here as a
    standalone corollary for convenience. -/
theorem ef_exists_and_proportional
    {N : Type*} [Fintype N] [Nonempty N]
    (μ : N → Measure I)
    [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NoAtoms (μ i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      IsEnvyFree (MeasureValuation μ) A ∧
      IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  obtain ⟨A, hA, hef⟩ := ef_exists μ
  exact ⟨A, hA, hef, hef.isProportional μ A hA⟩

/-! ### Bundled measure-instance entrypoints -/

/-- Proportional existence for bundled measure instances on `[0,1]`. -/
theorem MeasureInstance.proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NoAtoms (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      M.IsProportional (Fintype.card N) A :=
  SocialChoice.FairDivision.Divisible.proportional_exists M.measure

/-- Envy-free existence for bundled measure instances on `[0,1]`. -/
theorem MeasureInstance.envyFree_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NoAtoms (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧ M.IsEnvyFree A :=
  ef_exists M.measure

/-- Combined envy-free and proportional existence for bundled measure instances
    on `[0,1]`. -/
theorem MeasureInstance.envyFree_and_proportional_exists
    {N : Type*} [Fintype N] [Nonempty N]
    (M : MeasureInstance N I)
    [∀ i, IsFiniteMeasure (M.measure i)]
    [∀ i, NoAtoms (M.measure i)] :
    ∃ A : Allocation N I,
      IsAllocation A ∧
      M.IsEnvyFree A ∧
      M.IsProportional (Fintype.card N) A :=
  ef_exists_and_proportional M.measure

-- Note: the 2-agent case `ef_exists_two_agents` in `EnvyFree.lean` is a direct instance
-- of `ef_exists`. The `ef_exists_two_agents` statement requires only `NoAtoms (μ 0)` (not
-- agent 1), because the cut-and-choose argument is asymmetric: only agent 0's CDF is used
-- to find the cut point. `ef_exists` requires all agents' measures to be non-atomic, which
-- is the natural hypothesis for the general topological existence argument.

end Divisible
end FairDivision
end SocialChoice
