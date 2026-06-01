/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.UnitInterval
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier

The **Dubins–Spanier moving-knife algorithm** for n-agent proportional divisible allocation.

## Algorithm (informal)

Given `n` agents with non-atomic finite measures `μ₀, …, μ_{n-1}` on `[0,1]`:

1. For each agent `i`, find a threshold `tᵢ ∈ [0,1]` with
   `μᵢ([0, tᵢ]) = μᵢ([0,1]) / n`.

2. Let `i* = argmin { tᵢ : i ∈ [n] }` and `t* = tᵢ*`.

3. Assign agent `i*` the piece `[0, t*]`.

4. Restrict each remaining agent `j ≠ i*` to `(t*, 1]` and apply the algorithm
   recursively with `n - 1` agents.

## Why proportionality holds

- Agent `i*`: by construction, `μᵢ*([0, t*]) = μᵢ*([0,1])/n`. ✓

- Remaining agent `j`: since `t* ≤ tⱼ`, `μⱼ([0, t*]) ≤ μⱼ([0,1])/n`, so
  `μⱼ((t*, 1]) ≥ (n-1)/n · μⱼ([0,1])`. By induction on the remaining `n - 1` agents,
  agent `j`'s piece has value at least `μⱼ([0,1])/n`. ✓

## Main results

* `cut_exists` — IVT: for any `0 < c < μ([0,1])`, there exists `t ∈ [0,1]` with
  `μ([0,t]) = c`.
* `dubinsSpanierProportional` — proportional allocations always exist for n ≥ 1 agents.

## Status

All lemmas and theorems are fully proved, including `ds_step` (the moving-knife inductive step)
which constructs the full allocation via `Fin.insertNth` and proves partition validity and
proportionality using `ennreal_prop_step`.

## References

* Dubins–Spanier, "How to Cut a Cake Fairly", *Amer. Math. Monthly* (1961)
* Nisan et al., *Algorithmic Game Theory*, Chapter 13
-/

open MeasureTheory Set
open scoped unitInterval

namespace SocialChoice
namespace FairDivision
namespace Divisible

/-! ### Helpers for the unit-interval model -/

private lemma map_Iic_eq (μ : Measure I) (t : I) :
    (μ.map Subtype.val) (Set.Iic (t : ℝ)) = μ (Set.Iic t) := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  rfl

private lemma map_univ_eq (μ : Measure I) :
    (μ.map Subtype.val) Set.univ = μ Set.univ := by
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp

/-! ### IVT lemmas for measures -/

/-- **Intermediate Value Theorem for measures on ℝ**: for a finite non-atomic measure `μ`
    and any target 0 < c < (μ Set.univ).toReal, there exists a cut point t with
    `(μ (Set.Iic t)).toReal = c`.

    The strict bounds `0 < c < M` are necessary for a general non-atomic measure without
    bounded support: the CDF of e.g. a Gaussian is always strictly positive and never
    reaches its total mass. This is kept private and used to prove the public unit-interval
    version below by pushing forward along `Subtype.val`. -/
private lemma cut_exists_real (μ : Measure ℝ) [IsFiniteMeasure μ] [NoAtoms μ]
    (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < (μ Set.univ).toReal) :
    ∃ t : ℝ, (μ (Set.Iic t)).toReal = c := by
  -- ── CDF f and its properties ────────────────────────────────────────────────
  let f : ℝ → ℝ := fun t => (μ (Set.Iic t)).toReal
  set M := (μ Set.univ).toReal with hM_def
  -- Limit at +∞
  have hf_top : Filter.Tendsto f Filter.atTop (nhds M) :=
    (ENNReal.continuousAt_toReal (measure_ne_top μ Set.univ)).tendsto.comp
      (tendsto_measure_Iic_atTop μ)
  -- Limit at −∞
  have hf_bot : Filter.Tendsto f Filter.atBot (nhds 0) := by
    have h_conv : Filter.Tendsto (μ ∘ Set.Iic) Filter.atBot (nhds 0) := by
      have h0 : Filter.Tendsto (μ ∘ Set.Iic) Filter.atBot
          (nhds (μ (⋂ t : ℝ, Set.Iic t))) :=
        tendsto_measure_iInter_atBot
          (fun _ => measurableSet_Iic.nullMeasurableSet)
          (fun _ _ h => Set.Iic_subset_Iic.mpr h)
          ⟨0, measure_ne_top _ _⟩
      have h_empty : ⋂ t : ℝ, Set.Iic t = (∅ : Set ℝ) := by
        ext x; simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
        exact fun h => absurd (h (x - 1)) (by linarith)
      simp only [h_empty, measure_empty] at h0; exact h0
    simpa using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h_conv
  have hf_cont : Continuous f := cdfRealContinuous μ
  -- ── IVT: c ∈ (0, M) lies in the range of f ──────────────────────────────────
  have h₁ : ∃ a, f a ≤ c :=
    (hf_bot.eventually (Iio_mem_nhds hc_pos)).exists.imp fun _ ha => le_of_lt ha
  have h₂ : ∃ b, c ≤ f b :=
    (hf_top.eventually (Ioi_mem_nhds hc_lt)).exists.imp fun _ hb => le_of_lt hb
  exact mem_range_of_exists_le_of_exists_ge hf_cont h₁ h₂

/-- **Intermediate Value Theorem for measures on `[0,1]`**: for a finite non-atomic
    measure `μ` on the unit interval and any target `0 < c < μ([0,1])`, there exists
    `t ∈ [0,1]` such that the initial segment `Set.Iic t` has value exactly `c`.

    This is the analytic step used by the Dubins–Spanier moving-knife argument in its
    standard unit-interval formulation. -/
lemma cut_exists (μ : Measure I) [IsFiniteMeasure μ] [NoAtoms μ]
    (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < (μ Set.univ).toReal) :
    ∃ t : I, (μ (Set.Iic t)).toReal = c := by
  let ν : Measure ℝ := μ.map Subtype.val
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  haveI : NoAtoms ν := noAtomsMapSubtypeVal μ
  have hc_lt' : c < (ν Set.univ).toReal := by
    simpa [ν, map_univ_eq] using hc_lt
  obtain ⟨t, ht⟩ := cut_exists_real ν c hc_pos hc_lt'
  have ht_nonneg : 0 ≤ t := by
    by_contra ht_neg
    push_neg at ht_neg
    have h_zero : ν (Set.Iic t) = 0 := by
      rw [show ν = μ.map Subtype.val by rfl, Measure.map_apply measurable_subtype_coe
        measurableSet_Iic]
      have hpre : Subtype.val ⁻¹' Set.Iic t = (∅ : Set I) := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_preimage, Set.mem_Iic] at hx
          linarith [unitInterval.nonneg x]
        · intro hx
          simp at hx
      rw [hpre, measure_empty]
    have : c = 0 := by
      rw [← ht, h_zero]
      simp
    linarith
  have ht_le_one : t ≤ 1 := by
    by_contra ht_gt
    push_neg at ht_gt
    have h_full : ν (Set.Iic t) = ν Set.univ := by
      rw [show ν = μ.map Subtype.val by rfl, Measure.map_apply measurable_subtype_coe
        measurableSet_Iic]
      have hpre : Subtype.val ⁻¹' Set.Iic t = (Set.univ : Set I) := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          simp only [Set.mem_preimage, Set.mem_Iic]
          linarith [unitInterval.le_one x, ht_gt]
      rw [hpre]
      simpa [ν] using (map_univ_eq μ).symm
    have h_eq : c = (ν Set.univ).toReal := by
      rw [← ht, h_full]
    have : ¬ c < (ν Set.univ).toReal := by
      rw [h_eq]
      exact lt_irrefl ((ν Set.univ).toReal)
    exact this hc_lt'
  let tI : I := ⟨t, ⟨ht_nonneg, ht_le_one⟩⟩
  refine ⟨tI, ?_⟩
  rw [← map_Iic_eq μ tI]
  simpa [ν, tI] using ht

/-! ### ENNReal proportionality arithmetic -/

/-
Key arithmetic for the Dubins–Spanier inductive step (in ENNReal).

    Given:
    - `P + Q = M`          (partition of the cake measure)
    - `(n+1) * P ≤ M`     (threshold minimality: agent i* is the first stopper)
    - `Q ≤ n * X`         (IH: remaining n agents get n*X ≥ Q from the remainder)
    - `P ≠ ⊤`             (finite)

    Conclude: `M ≤ (n+1) * X`  (proportionality for the remaining agents).

    **Proof sketch**:
    - From (n+1)*P ≤ P+Q, cancel P: n*P ≤ Q.
    - From n*P ≤ Q ≤ n*X, cancel n (≥ 1): P ≤ X.
    - Then (n+1)*X = X + n*X ≥ P + Q = M. ✓

    The cancellation step uses `ENNReal.le_of_add_le_add_right` (finite P) and
    `ENNReal.mul_le_mul_left'` inverted (n ≥ 1).
-/
private lemma ennreal_prop_step (n : ℕ) (hn : 0 < n) (P : ENNReal) (Q : ENNReal) (X : ENNReal) (M : ENNReal)
    (hM : P + Q = M)
    (hP_fin : P ≠ ⊤)
    (hPQ : (↑(n + 1) : ENNReal) * P ≤ M)
    (hIH : Q ≤ ↑n * X) :
    M ≤ (↑(n + 1) : ENNReal) * X := by
  rw [ ← hM, mul_comm ];
  convert add_le_add ( show P ≤ X from ?_ ) hIH using 1;
  · grind;
  · have h_cancel : n * P ≤ n * X := by
      refine' le_trans _ hIH;
      convert tsub_le_tsub_right hPQ P using 1;
      · simp +decide [ add_mul, ENNReal.add_sub_cancel_right hP_fin ];
      · rw [ ← hM, ENNReal.add_sub_cancel_left hP_fin ];
    rw [ ENNReal.mul_le_mul_iff_right ] at h_cancel <;> aesop

/-! ### Inductive proportional existence (Fin n) -/

/-- The inductive predicate for the Dubins–Spanier algorithm:
    for n agents indexed by `Fin n`, a complete proportional allocation exists. -/
private def DubinsSpanierProp (n : ℕ) : Prop :=
  ∀ (μ : Fin n → Measure I),
    (∀ i, IsFiniteMeasure (μ i)) →
    (∀ i, NoAtoms (μ i)) →
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ IsProportional n (MeasureValuation μ) A

/-- Base case: 1 agent receives the whole cake.
    Proportionality holds trivially on the whole unit interval. -/
private lemma ds_one : DubinsSpanierProp 1 := by
  intro μ _ _
  refine ⟨fun _ => Set.univ, ⟨fun i => ?_, fun i j hij => ?_, ?_⟩, fun i => ?_⟩
  · -- measurability
    fin_cases i; exact MeasurableSet.univ
  · -- disjointness
    (fin_cases i; fin_cases j; exact absurd rfl hij)
  · -- cover
    simp [Set.iUnion_const]
  · -- proportionality: μ 0 univ ≤ 1 * μ 0 univ
    fin_cases i; simp [MeasureValuation]

/-- Inductive step: if n ≥ 1 agents can be allocated proportionally, so can n+1.
    Proved via the Dubins–Spanier moving-knife algorithm.

    **Proof structure**:

    Step 1. For each i : Fin (n+1), choose threshold tᵢ ∈ [0,1] with
      `(n+1) * μᵢ(Iic tᵢ) ≤ μᵢ(univ)`.
      — For μᵢ(univ) = 0: any tᵢ works.
      — For μᵢ(univ) > 0: `cut_exists` gives tᵢ with `μᵢ(Iic tᵢ) = μᵢ(univ)/(n+1)` exactly.

    Step 2. Let i* = argmin tᵢ (`Finset.exists_min_image`). Set t* = tᵢ*.

    Step 3. Assign A(i*) = Iic t*. For the remaining n agents j : Fin n (embedded via
      `Fin.succAbove i*`), apply the IH with restricted measures
      `(μ (i*.succAbove j)).restrict (Ioi t*)`.

    Step 4. Define A(i*.succAbove j) = A_rem j ∩ Ioi t* for j : Fin n.

    Step 5–6. Verify partition and proportionality using `ennreal_prop_step`. -/
private lemma ds_step (n : ℕ) (hn : 0 < n) (ih : DubinsSpanierProp n) :
    DubinsSpanierProp (n + 1) := by
  intro μ hfin hnoatoms
  -- ── Step 1: choose threshold tᵢ for each agent ─────────────────────────────
  have hn1_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hn1_gt1 : (1 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ hn
  -- For each i, find tᵢ with (n+1)*μᵢ(Iic tᵢ) ≤ μᵢ(univ)
  have hthresh : ∀ i : Fin (n + 1), ∃ t : I,
      (↑(n + 1) : ENNReal) * μ i (Set.Iic t) = μ i Set.univ := by
    intro i
    rcases eq_or_ne (μ i Set.univ) 0 with h0 | hpos
    · -- Zero-measure agent: μᵢ(Iic 0) = μᵢ(univ) = 0
      exact ⟨0, by
        have hle : μ i (Set.Iic 0) ≤ μ i Set.univ := measure_mono (Set.subset_univ _)
        rw [h0] at hle
        rw [h0, le_antisymm hle zero_le, mul_zero]⟩
    · -- Positive measure: apply cut_exists with c = M/(n+1)
      haveI := hfin i
      have hM_fin : μ i Set.univ ≠ ⊤ := measure_ne_top _ _
      have hM_pos : 0 < (μ i Set.univ).toReal := ENNReal.toReal_pos hpos hM_fin
      have hc_pos : 0 < (μ i Set.univ).toReal / (↑(n + 1) : ℝ) :=
        div_pos hM_pos hn1_pos
      have hc_lt : (μ i Set.univ).toReal / (↑(n + 1) : ℝ) < (μ i Set.univ).toReal :=
        div_lt_self hM_pos hn1_gt1
      obtain ⟨ti, hti⟩ := cut_exists (μ i) _ hc_pos hc_lt
      refine ⟨ti, ?_⟩
      -- Show (n+1) * μᵢ(Iic tᵢ) = μᵢ(univ) via ENNReal ← toReal equality
      have hIic_fin : μ i (Set.Iic ti) ≠ ⊤ := measure_ne_top _ _
      have hLHS_fin : (↑(n + 1) : ENNReal) * μ i (Set.Iic ti) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hIic_fin
      have heq : (↑(n + 1) : ENNReal) * μ i (Set.Iic ti) = μ i Set.univ := by
        have h_toReal :
            ((↑(n + 1) : ENNReal) * μ i (Set.Iic ti)).toReal = (μ i Set.univ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hti]
          have hn1_ne : (n + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hn1_ne]
        rw [← ENNReal.ofReal_toReal hLHS_fin, h_toReal, ENNReal.ofReal_toReal hM_fin]
      exact heq
  -- Choose a threshold for each agent via Classical.choice
  let t : Fin (n + 1) → I := fun i => (hthresh i).choose
  have ht_prop : ∀ i, (↑(n + 1) : ENNReal) * μ i (Set.Iic (t i)) = μ i Set.univ :=
    fun i => (hthresh i).choose_spec
  -- ── Step 2: find i* = argmin tᵢ ────────────────────────────────────────────
  obtain ⟨i_star, _, hi_star⟩ :=
    Finset.exists_min_image Finset.univ t Finset.univ_nonempty
  have ht_min : ∀ j : Fin (n + 1), t i_star ≤ t j := fun j =>
    hi_star j (Finset.mem_univ j)
  -- Monotonicity: for all j, (n+1)*μⱼ(Iic t*) ≤ μⱼ(univ)
  -- because t* ≤ tⱼ implies Iic t* ⊆ Iic tⱼ
  have ht_mono : ∀ j : Fin (n + 1),
      (↑(n + 1) : ENNReal) * μ j (Set.Iic (t i_star)) ≤ μ j Set.univ :=
    fun j => le_trans
      (mul_le_mul_of_nonneg_left
        (measure_mono (Set.Iic_subset_Iic.mpr (ht_min j))) zero_le)
      (ht_prop j).le
  -- ── Steps 3-6: apply IH and combine ─────────────────────────────────────────
  -- Remaining agents: Fin n embedded in Fin (n+1) via Fin.succAbove i_star.
  -- Restricted measures on Ioi t*:
  let μ_rem : Fin n → Measure I :=
    fun j => (μ (i_star.succAbove j)).restrict (Set.Ioi (t i_star))
  haveI hfin_rem : ∀ j : Fin n, IsFiniteMeasure (μ_rem j) :=
    fun j => inferInstance
  haveI hnoatoms_rem : ∀ j : Fin n, NoAtoms (μ_rem j) := fun j => inferInstance
  -- Apply IH to get a proportional allocation A_rem of the right remainder for n agents
  obtain ⟨A_rem, hA_rem, hprop_rem⟩ :=
    ih μ_rem (fun j => hfin_rem j) (fun j => hnoatoms_rem j)
  -- ── Step 3: construct the full allocation via Fin.insertNth ─────────────────
  let A : Allocation (Fin (n + 1)) I :=
    Fin.insertNth i_star (Set.Iic (t i_star)) (fun j => A_rem j ∩ Set.Ioi (t i_star))
  have hA_star : A i_star = Set.Iic (t i_star) := Fin.insertNth_apply_same _ _ _
  have hA_other : ∀ j : Fin n, A (i_star.succAbove j) = A_rem j ∩ Set.Ioi (t i_star) :=
    fun j => Fin.insertNth_apply_succAbove _ _ _ j
  refine ⟨A, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- Measurability
    intro i
    by_cases hi : i = i_star
    · rw [hi, hA_star]; exact measurableSet_Iic
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [hA_other]
      exact (hA_rem.measurable j).inter measurableSet_Ioi
  · -- Disjointness
    intro i₁ i₂ hi₁₂
    by_cases h₁ : i₁ = i_star <;> by_cases h₂ : i₂ = i_star
    · exact absurd (h₁.trans h₂.symm) hi₁₂
    · obtain ⟨j₂, rfl⟩ := Fin.exists_succAbove_eq h₂
      rw [h₁, hA_star, hA_other]
      exact Set.disjoint_of_subset_right Set.inter_subset_right (Set.Iic_disjoint_Ioi le_rfl)
    · obtain ⟨j₁, rfl⟩ := Fin.exists_succAbove_eq h₁
      rw [h₂, hA_star, hA_other]
      exact (Set.disjoint_of_subset_right Set.inter_subset_right (Set.Iic_disjoint_Ioi le_rfl)).symm
    · obtain ⟨j₁, rfl⟩ := Fin.exists_succAbove_eq h₁
      obtain ⟨j₂, rfl⟩ := Fin.exists_succAbove_eq h₂
      rw [hA_other, hA_other]
      have hj₁₂ : j₁ ≠ j₂ := fun h => hi₁₂ (congrArg _ h)
      exact Set.disjoint_of_subset_left Set.inter_subset_left
        (Set.disjoint_of_subset_right Set.inter_subset_left (hA_rem.disjoint _ _ hj₁₂))
  · -- Cover
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ≤ t i_star
    · exact ⟨_, by rw [hA_star]; exact hx⟩
    · push_neg at hx
      have hx_ioi : x ∈ Set.Ioi (t i_star) := hx
      obtain ⟨j, hj⟩ := hA_rem.mem_iUnion x
      exact ⟨i_star.succAbove j, (hA_other j).symm ▸ ⟨hj, hx_ioi⟩⟩
  · -- Proportionality
    intro i
    simp only [MeasureValuation]
    by_cases hi : i = i_star
    · -- Agent i*: (n+1) * μ i_star (Iic t*) ≤ μ i_star univ
      subst hi; rw [hA_star]; exact (ht_prop i).ge
    · -- Remaining agent: use ennreal_prop_step
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [hA_other]
      apply ennreal_prop_step n hn
        (μ (i_star.succAbove j) (Set.Iic (t i_star)))
        (μ (i_star.succAbove j) (Set.Ioi (t i_star)))
        (μ (i_star.succAbove j) (A_rem j ∩ Set.Ioi (t i_star)))
      · -- P + Q = M
        rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi]
      · -- P ≠ ⊤
        exact measure_ne_top _ _
      · -- (n+1)*P ≤ M
        exact ht_mono (i_star.succAbove j)
      · -- Q ≤ n * X  (from IH)
        have hpj := hprop_rem j
        simp only [MeasureValuation] at hpj
        -- hpj : μ_rem j univ ≤ n * μ_rem j (A_rem j)
        -- μ_rem j = (μ (i_star.succAbove j)).restrict (Ioi (t i_star))
        -- μ_rem j univ = μ (i_star.succAbove j) (Ioi (t i_star))
        -- μ_rem j (A_rem j) = μ (i_star.succAbove j) (A_rem j ∩ Ioi (t i_star))
        rw [show μ_rem j Set.univ = μ (i_star.succAbove j) (Set.Ioi (t i_star)) from
          Measure.restrict_apply_univ _] at hpj
        rw [show μ_rem j (A_rem j) = μ (i_star.succAbove j) (A_rem j ∩ Set.Ioi (t i_star)) from
          Measure.restrict_apply (hA_rem.measurable j)] at hpj
        exact hpj

/-! ### Main induction -/

private lemma dubinsSpanierFin : ∀ (n : ℕ), 0 < n → DubinsSpanierProp n := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (Nat.lt_irrefl 0)
  | succ n ihn =>
    intro _
    by_cases hn' : n = 0
    · subst hn'; exact ds_one
    · exact ds_step n (Nat.pos_of_ne_zero hn') (ihn (Nat.pos_of_ne_zero hn'))

/-! ### Main theorem -/

/-- **Dubins–Spanier**: proportional allocations always exist for n ≥ 1 agents with
    non-atomic finite measures on `[0,1]`.

    For any n ≥ 1 agents `(μ : Fin n → Measure I)` with `IsFiniteMeasure` and `NoAtoms`,
    there is a complete measurable partition `A` of `[0,1]` such that every agent `i` values their
    piece A i at at least `1/n` of the whole cake:

    `∀ i, μ i Set.univ ≤ n · μ i (A i)`.

    **Proof**: induction on n using `ds_one` (base) and `ds_step` (inductive step). -/
theorem dubinsSpanierProportional (n : ℕ) (hn : 0 < n)
    (μ : Fin n → Measure I) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NoAtoms (μ i)] :
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ IsProportional n (MeasureValuation μ) A :=
  dubinsSpanierFin n hn μ (fun _ => inferInstance) (fun _ => inferInstance)

/-- Bundled-instance form of Dubins-Spanier proportional existence. -/
theorem dubinsSpanier_exists_proportional_allocation (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NoAtoms (M.measure i)] :
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ M.IsProportional n A :=
  dubinsSpanierProportional n hn M.measure

/-- The Dubins-Spanier rule on bundled measure instances. It chooses one of the
    proportional allocations supplied by the constructive existence proof. -/
noncomputable def dubinsSpanierRule (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NoAtoms (M.measure i)] :
    {A : Allocation (Fin n) I // IsAllocation A} :=
  let A := Classical.choose (dubinsSpanier_exists_proportional_allocation n hn M)
  ⟨A, (Classical.choose_spec (dubinsSpanier_exists_proportional_allocation n hn M)).1⟩

/-- The bundled Dubins-Spanier rule is proportional. -/
theorem dubinsSpanierRule_isProportional (n : ℕ) (hn : 0 < n)
    (M : MeasureInstance (Fin n) I)
    [∀ i, IsFiniteMeasure (M.measure i)] [∀ i, NoAtoms (M.measure i)] :
    M.IsProportional n (dubinsSpanierRule n hn M).1 := by
  unfold dubinsSpanierRule
  exact (Classical.choose_spec (dubinsSpanier_exists_proportional_allocation n hn M)).2

end Divisible
end FairDivision
end SocialChoice
