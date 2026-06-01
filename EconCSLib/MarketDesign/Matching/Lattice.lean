/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MarketDesign.Matching.GaleShapley
import EconCSLib.MarketDesign.Matching.RuralHospitals
import EconCSLib.MarketDesign.Matching.Optimal

/-!
# EconCSLib.MarketDesign.Matching.Lattice

Building blocks for the Conway–Knuth lattice structure on the set of stable
matchings of a one-to-one market (#231 item B).

This file currently contains the **opposed-preferences lemma**, the crux on
which the lattice construction rests: across two stable matchings, whenever a
man does strictly better, the woman he gains does strictly worse. It is a
direct pairwise stability argument (no global counting, no lattice machinery).

The full lattice — `stableJoin` / `stableMeet`, their matching-validity and
stability, the `Lattice` instance and distributivity — is tracked as the
remainder of #231 item B and builds on this lemma.

## References

* [MSZ Theorem 22.12] Maschler, Solan, Zamir, *Game Theory*, §22.
* Knuth (1976), *Mariages Stables*.
* Roth & Sotomayor (1990), Ch. 2 §2.3.
-/

open GS

namespace GS

variable {n : ℕ} (w m : Preferences n)

/-- **Opposed preferences.** Let `μ` be a stable matching. If man `j` is matched
to woman `wj` under another matching `ν` and **strictly prefers** `wj` to his
`μ`-partner `wj'`, then `wj` strictly prefers her `μ`-partner `m'` to `j`.

Intuition: the two sides' interests are opposed across stable matchings — when
a man trades up, the woman he gains trades down. Proof: otherwise `(wj, j)`
would be a blocking pair for `μ` (he prefers her to his `μ`-partner by
hypothesis; she would prefer him to her `μ`-partner `m'`), contradicting
stability. Only `μ` need be stable. -/
theorem opposed_preferences
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
    {j wj wj' m' : Fin n}
    (hμ_j : μ.matchW j = some wj')
    (hpref : (m.prefs j).idxOf wj < (m.prefs j).idxOf wj')
    (hμ_w : μ.matchM wj = some m') :
    (w.prefs wj).idxOf m' < (w.prefs wj).idxOf j := by
  -- `wj ≠ wj'` since `j` strictly prefers `wj` over `wj'`.
  have hwj_ne : wj ≠ wj' := by
    intro he; rw [he] at hpref; exact (lt_irrefl _ hpref)
  -- `j ≠ m'`: else `μ` would match `wj` to `j`, contradicting `μ.matchW j = some wj'`.
  have hj_ne : j ≠ m' := by
    intro he; subst he
    have : μ.matchW j = some wj := (μ.consistent wj j).mp hμ_w
    rw [hμ_j] at this
    exact hwj_ne (Option.some.inj this).symm
  -- Suppose `wj` does NOT strictly prefer `m'` to `j`; derive a blocking pair.
  by_contra hle
  push_neg at hle  -- (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf m'
  -- `wj` then strictly prefers `j` to `m'` (strictness from `j ≠ m'`).
  have hlt : (w.prefs wj).idxOf j < (w.prefs wj).idxOf m' := by
    refine lt_of_le_of_ne hle (fun e => hj_ne ?_)
    exact (List.idxOf_inj (pref_list_mem _ (w.valid wj).1 (w.valid wj).2 j)).mp e
  -- `(wj, j)` blocks `μ`.
  exact hμ wj j
    ⟨by rw [hμ_w]; exact ⟨by show (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf m'; omega,
                          by show ¬ (w.prefs wj).idxOf m' ≤ (w.prefs wj).idxOf j; omega⟩,
     by rw [hμ_j]; exact ⟨by show (m.prefs j).idxOf wj ≤ (m.prefs j).idxOf wj'; omega,
                          by show ¬ (m.prefs j).idxOf wj' ≤ (m.prefs j).idxOf wj; omega⟩⟩

/-! ### Partner extraction (stable ⇒ perfect) -/

variable {w m}

/-- The woman partnered to man `j` under a stable matching `μ` (total, since a
stable matching of the balanced market is perfect). -/
noncomputable def wPartner (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) (j : Fin n) : Fin n :=
  (μ.matchW j).get ((stable_matching_perfect w m μ hμ).2 j)

/-- The man partnered to woman `i` under a stable matching `μ`. -/
noncomputable def mPartner (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) (i : Fin n) : Fin n :=
  (μ.matchM i).get ((stable_matching_perfect w m μ hμ).1 i)

@[simp] lemma matchW_wPartner (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) (j : Fin n) :
    μ.matchW j = some (wPartner μ hμ j) := (Option.some_get _).symm

@[simp] lemma matchM_mPartner (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) (i : Fin n) :
    μ.matchM i = some (mPartner μ hμ i) := (Option.some_get _).symm

/-- The man-of and woman-of partner maps are inverse to each other. -/
lemma wPartner_eq_iff (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) {i j : Fin n} :
    wPartner μ hμ j = i ↔ mPartner μ hμ i = j := by
  constructor
  · intro h
    have h1 : μ.matchW j = some i := by rw [matchW_wPartner μ hμ j, h]
    have h2 : μ.matchM i = some j := (μ.consistent i j).mpr h1
    rw [matchM_mPartner μ hμ i] at h2
    exact Option.some.inj h2
  · intro h
    have h1 : μ.matchM i = some j := by rw [matchM_mPartner μ hμ i, h]
    have h2 : μ.matchW j = some i := (μ.consistent i j).mp h1
    rw [matchW_wPartner μ hμ j] at h2
    exact Option.some.inj h2

/-! ### The join (man-optimal of two) and its injectivity -/

variable (μ ν : Matching (Fin n) (Fin n))
  (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ)
  (hν : Matching.IsStable (MatchingMarket.ofEquivData w m) ν)

/-- Man `j`'s more-preferred partner across stable matchings `μ` and `ν`. -/
noncomputable def joinWoman (j : Fin n) : Fin n :=
  if (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf (wPartner ν hν j)
  then wPartner μ hμ j else wPartner ν hν j

lemma joinWoman_eq_or (j : Fin n) :
    joinWoman μ ν hμ hν j = wPartner μ hμ j ∨ joinWoman μ ν hμ hν j = wPartner ν hν j := by
  unfold joinWoman; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- If `i` is man `j`'s join-partner then `j` is one of `i`'s two men. -/
lemma joinWoman_mem_men {j i : Fin n} (h : joinWoman μ ν hμ hν j = i) :
    mPartner μ hμ i = j ∨ mPartner ν hν i = j := by
  rcases joinWoman_eq_or μ ν hμ hν j with he | he
  · exact Or.inl ((wPartner_eq_iff μ hμ).mp (he ▸ h))
  · exact Or.inr ((wPartner_eq_iff ν hν).mp (he ▸ h))

/-- If `i` is the join-partner of her `μ`-man `j`, then `i` weakly prefers her
`ν`-man to `j` (so `j` is her worse man). -/
lemma joinWoman_worse_left {j i : Fin n}
    (hji : joinWoman μ ν hμ hν j = i) (hμji : mPartner μ hμ i = j) :
    (w.prefs i).idxOf (mPartner ν hν i) ≤ (w.prefs i).idxOf j := by
  have hμw : wPartner μ hμ j = i := (wPartner_eq_iff μ hμ).mpr hμji
  by_cases heq : wPartner ν hν j = i
  · -- `i` is also `j`'s ν-woman, so `mPartner ν i = j`.
    have : mPartner ν hν i = j := (wPartner_eq_iff ν hν).mp heq
    rw [this]
  · -- `j` strictly prefers `i` (his μ-woman) over his ν-woman; opposed prefs.
    have hbranch : joinWoman μ ν hμ hν j = wPartner μ hμ j := by rw [hji, hμw]
    have hle : (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf (wPartner ν hν j) := by
      by_contra hgt
      unfold joinWoman at hbranch
      rw [if_neg hgt] at hbranch
      exact heq (hbranch.trans hμw)
    rw [hμw] at hle
    have hlt : (m.prefs j).idxOf i < (m.prefs j).idxOf (wPartner ν hν j) := by
      refine lt_of_le_of_ne hle (fun e => heq ?_)
      exact ((List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i)).mp e).symm
    have := opposed_preferences w m ν hν (wj := i) (wj' := wPartner ν hν j)
      (m' := mPartner ν hν i) (matchW_wPartner ν hν j) hlt (matchM_mPartner ν hν i)
    omega

/-- Dual of `joinWoman_worse_left` with the roles of `μ`, `ν` swapped. -/
lemma joinWoman_worse_right {j i : Fin n}
    (hji : joinWoman μ ν hμ hν j = i) (hνji : mPartner ν hν i = j) :
    (w.prefs i).idxOf (mPartner μ hμ i) ≤ (w.prefs i).idxOf j := by
  have hνw : wPartner ν hν j = i := (wPartner_eq_iff ν hν).mpr hνji
  by_cases heq : wPartner μ hμ j = i
  · have : mPartner μ hμ i = j := (wPartner_eq_iff μ hμ).mp heq
    rw [this]
  · have hbranch : joinWoman μ ν hμ hν j = wPartner ν hν j := by rw [hji, hνw]
    have hlt0 : (m.prefs j).idxOf (wPartner ν hν j) < (m.prefs j).idxOf (wPartner μ hμ j) := by
      by_contra hge
      push_neg at hge
      unfold joinWoman at hbranch
      rw [if_pos hge] at hbranch
      exact heq (hbranch.trans hνw)
    rw [hνw] at hlt0
    have hlt : (m.prefs j).idxOf i < (m.prefs j).idxOf (wPartner μ hμ j) := hlt0
    have := opposed_preferences w m μ hμ (wj := i) (wj' := wPartner μ hμ j)
      (m' := mPartner μ hμ i) (matchW_wPartner μ hμ j) hlt (matchM_mPartner μ hμ i)
    omega

/-- The join woman-assignment is injective. -/
lemma joinWoman_injective : Function.Injective (joinWoman μ ν hμ hν) := by
  intro j1 j2 he
  set i := joinWoman μ ν hμ hν j1 with hidef
  have h1 : joinWoman μ ν hμ hν j1 = i := hidef.symm
  have h2 : joinWoman μ ν hμ hν j2 = i := he.symm.trans hidef.symm
  rcases joinWoman_mem_men μ ν hμ hν h1 with hm1 | hn1 <;>
    rcases joinWoman_mem_men μ ν hμ hν h2 with hm2 | hn2
  · exact hm1.symm.trans hm2          -- both μ-men of i
  · -- j1 = μ-man, j2 = ν-man
    have a := joinWoman_worse_left μ ν hμ hν h1 hm1   -- idxOf (mPartner ν i) ≤ idxOf j1
    have b := joinWoman_worse_right μ ν hμ hν h2 hn2  -- idxOf (mPartner μ i) ≤ idxOf j2
    rw [hn2] at a; rw [hm1] at b
    exact (List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j1)).mp
      (le_antisymm b a)
  · -- j1 = ν-man, j2 = μ-man
    have a := joinWoman_worse_right μ ν hμ hν h1 hn1  -- idxOf (mPartner μ i) ≤ idxOf j1
    have b := joinWoman_worse_left μ ν hμ hν h2 hm2   -- idxOf (mPartner ν i) ≤ idxOf j2
    rw [hm2] at a; rw [hn1] at b
    exact (List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j1)).mp
      (le_antisymm b a)
  · exact hn1.symm.trans hn2          -- both ν-men of i

/-! ### Strict-preference reductions for the `ofEquivData` market -/

lemma prefM_strict {i a b : Fin n} :
    strict ((MatchingMarket.ofEquivData w m).prefM i).rel (some a) (some b) ↔
      (w.prefs i).idxOf a < (w.prefs i).idxOf b := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (w.prefs i).idxOf a ≤ (w.prefs i).idxOf b := h1
    have e2 : ¬ (w.prefs i).idxOf b ≤ (w.prefs i).idxOf a := h2
    omega
  · intro h
    exact ⟨show (w.prefs i).idxOf a ≤ (w.prefs i).idxOf b by omega,
           show ¬ (w.prefs i).idxOf b ≤ (w.prefs i).idxOf a by omega⟩

lemma prefW_strict {j a b : Fin n} :
    strict ((MatchingMarket.ofEquivData w m).prefW j).rel (some a) (some b) ↔
      (m.prefs j).idxOf a < (m.prefs j).idxOf b := by
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (m.prefs j).idxOf a ≤ (m.prefs j).idxOf b := h1
    have e2 : ¬ (m.prefs j).idxOf b ≤ (m.prefs j).idxOf a := h2
    omega
  · intro h
    exact ⟨show (m.prefs j).idxOf a ≤ (m.prefs j).idxOf b by omega,
           show ¬ (m.prefs j).idxOf b ≤ (m.prefs j).idxOf a by omega⟩

/-! ### The join as a stable matching -/

/-- The join woman-assignment packaged as an equivalence (injective on the
finite `Fin n`, hence bijective). -/
noncomputable def joinEquiv : Fin n ≃ Fin n :=
  Equiv.ofBijective (joinWoman μ ν hμ hν)
    (Finite.injective_iff_bijective.mp (joinWoman_injective μ ν hμ hν))

/-- The **join** `μ ∨ ν`: each man keeps his more-preferred of the two
partners; each woman keeps her less-preferred man. -/
noncomputable def stableJoin : Matching (Fin n) (Fin n) where
  matchM i := some ((joinEquiv μ ν hμ hν).symm i)
  matchW j := some (joinWoman μ ν hμ hν j)
  consistent := by
    intro i j
    simp only [Option.some.injEq]
    rw [Equiv.symm_apply_eq]
    exact eq_comm

@[simp] lemma stableJoin_matchW (j : Fin n) :
    (stableJoin μ ν hμ hν).matchW j = some (joinWoman μ ν hμ hν j) := rfl

@[simp] lemma stableJoin_matchM (i : Fin n) :
    (stableJoin μ ν hμ hν).matchM i = some ((joinEquiv μ ν hμ hν).symm i) := rfl

lemma joinWoman_le_left (j : Fin n) :
    (m.prefs j).idxOf (joinWoman μ ν hμ hν j) ≤ (m.prefs j).idxOf (wPartner μ hμ j) := by
  unfold joinWoman; split_ifs with h
  · exact le_refl _
  · push_neg at h; omega

lemma joinWoman_le_right (j : Fin n) :
    (m.prefs j).idxOf (joinWoman μ ν hμ hν j) ≤ (m.prefs j).idxOf (wPartner ν hν j) := by
  unfold joinWoman; split_ifs with h
  · exact h
  · exact le_refl _

/-- The join of two stable matchings is stable. -/
theorem stableJoin_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m) (stableJoin μ ν hμ hν) := by
  intro i j hblock
  obtain ⟨hi, hj⟩ := hblock
  rw [stableJoin_matchM] at hi
  rw [stableJoin_matchW] at hj
  set jm := (joinEquiv μ ν hμ hν).symm i with hjmdef
  have hi' : (w.prefs i).idxOf j < (w.prefs i).idxOf jm := prefM_strict.mp hi
  have hj' : (m.prefs j).idxOf i < (m.prefs j).idxOf (joinWoman μ ν hμ hν j) := prefW_strict.mp hj
  have hjoin_jm : joinWoman μ ν hμ hν jm = i := (joinEquiv μ ν hμ hν).apply_symm_apply i
  rcases joinWoman_mem_men μ ν hμ hν hjoin_jm with hm | hn
  · -- `jm` is `i`'s `μ`-man, so `(i, j)` blocks `μ`.
    refine hμ i j ⟨?_, ?_⟩
    · rw [matchM_mPartner μ hμ i, hm]; exact prefM_strict.mpr hi'
    · rw [matchW_wPartner μ hμ j]
      exact prefW_strict.mpr (lt_of_lt_of_le hj' (joinWoman_le_left μ ν hμ hν j))
  · -- `jm` is `i`'s `ν`-man, so `(i, j)` blocks `ν`.
    refine hν i j ⟨?_, ?_⟩
    · rw [matchM_mPartner ν hν i, hn]; exact prefM_strict.mpr hi'
    · rw [matchW_wPartner ν hν j]
      exact prefW_strict.mpr (lt_of_lt_of_le hj' (joinWoman_le_right μ ν hμ hν j))

/-! ### The meet (man-pessimal of two), dual to the join

The meet `μ ∧ ν` gives every man his *worse* of the two partners, equivalently
every woman her *better* of the two men. We mirror the join construction over
women: `meetMan` (each woman's preferred man) is the relevant bijection. -/

/-- Dual of `opposed_preferences`: if woman `i` strictly prefers man `mi` to her
`candidate`-man `mi'`, then `mi` strictly prefers his `candidate`-woman to `i`. -/
theorem opposed_preferences_women
    (candidate : Matching (Fin n) (Fin n))
    (hcandidate : Matching.IsStable (MatchingMarket.ofEquivData w m) candidate)
    {i mi mi' j' : Fin n}
    (hcandidate_i : candidate.matchM i = some mi')
    (hpref : (w.prefs i).idxOf mi < (w.prefs i).idxOf mi')
    (hcandidate_m : candidate.matchW mi = some j') :
    (m.prefs mi).idxOf j' < (m.prefs mi).idxOf i := by
  have hmi_ne : mi ≠ mi' := by
    intro he; rw [he] at hpref; exact (lt_irrefl _ hpref)
  have hi_ne : i ≠ j' := by
    intro he; subst he
    have : candidate.matchM i = some mi := (candidate.consistent i mi).mpr hcandidate_m
    rw [hcandidate_i] at this
    exact hmi_ne (Option.some.inj this).symm
  by_contra hle
  push_neg at hle
  have hlt : (m.prefs mi).idxOf i < (m.prefs mi).idxOf j' := by
    refine lt_of_le_of_ne hle (fun e => hi_ne ?_)
    exact (List.idxOf_inj (pref_list_mem _ (m.valid mi).1 (m.valid mi).2 i)).mp e
  exact hcandidate i mi
    ⟨by rw [hcandidate_i]; exact ⟨by show (w.prefs i).idxOf mi ≤ (w.prefs i).idxOf mi'; omega,
                          by show ¬ (w.prefs i).idxOf mi' ≤ (w.prefs i).idxOf mi; omega⟩,
     by rw [hcandidate_m]; exact ⟨by show (m.prefs mi).idxOf i ≤ (m.prefs mi).idxOf j'; omega,
                          by show ¬ (m.prefs mi).idxOf j' ≤ (m.prefs mi).idxOf i; omega⟩⟩

/-- Woman `i`'s more-preferred man across `μ` and `ν`. -/
noncomputable def meetMan (i : Fin n) : Fin n :=
  if (w.prefs i).idxOf (mPartner μ hμ i) ≤ (w.prefs i).idxOf (mPartner ν hν i)
  then mPartner μ hμ i else mPartner ν hν i

lemma meetMan_eq_or (i : Fin n) :
    meetMan μ ν hμ hν i = mPartner μ hμ i ∨ meetMan μ ν hμ hν i = mPartner ν hν i := by
  unfold meetMan; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma meetMan_mem_women {i j : Fin n} (h : meetMan μ ν hμ hν i = j) :
    wPartner μ hμ j = i ∨ wPartner ν hν j = i := by
  rcases meetMan_eq_or μ ν hμ hν i with he | he
  · exact Or.inl ((wPartner_eq_iff μ hμ).mpr (he ▸ h))
  · exact Or.inr ((wPartner_eq_iff ν hν).mpr (he ▸ h))

lemma meetMan_worse_left {i j : Fin n}
    (hij : meetMan μ ν hμ hν i = j) (hμij : wPartner μ hμ j = i) :
    (m.prefs j).idxOf (wPartner ν hν j) ≤ (m.prefs j).idxOf i := by
  have hμm : mPartner μ hμ i = j := (wPartner_eq_iff μ hμ).mp hμij
  by_cases heq : mPartner ν hν i = j
  · have : wPartner ν hν j = i := (wPartner_eq_iff ν hν).mpr heq
    rw [this]
  · have hbranch : meetMan μ ν hμ hν i = mPartner μ hμ i := by rw [hij, hμm]
    have hle : (w.prefs i).idxOf (mPartner μ hμ i) ≤ (w.prefs i).idxOf (mPartner ν hν i) := by
      by_contra hgt
      unfold meetMan at hbranch
      rw [if_neg hgt] at hbranch
      exact heq (hbranch.trans hμm)
    rw [hμm] at hle
    have hlt : (w.prefs i).idxOf j < (w.prefs i).idxOf (mPartner ν hν i) := by
      refine lt_of_le_of_ne hle (fun e => heq ?_)
      exact ((List.idxOf_inj (pref_list_mem _ (w.valid i).1 (w.valid i).2 j)).mp e).symm
    have := opposed_preferences_women ν hν (mi := j) (mi' := mPartner ν hν i)
      (j' := wPartner ν hν j) (matchM_mPartner ν hν i) hlt (matchW_wPartner ν hν j)
    omega

lemma meetMan_worse_right {i j : Fin n}
    (hij : meetMan μ ν hμ hν i = j) (hνij : wPartner ν hν j = i) :
    (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf i := by
  have hνm : mPartner ν hν i = j := (wPartner_eq_iff ν hν).mp hνij
  by_cases heq : mPartner μ hμ i = j
  · have : wPartner μ hμ j = i := (wPartner_eq_iff μ hμ).mpr heq
    rw [this]
  · have hbranch : meetMan μ ν hμ hν i = mPartner ν hν i := by rw [hij, hνm]
    have hlt0 : (w.prefs i).idxOf (mPartner ν hν i) < (w.prefs i).idxOf (mPartner μ hμ i) := by
      by_contra hge
      push_neg at hge
      unfold meetMan at hbranch
      rw [if_pos hge] at hbranch
      exact heq (hbranch.trans hνm)
    rw [hνm] at hlt0
    have hlt : (w.prefs i).idxOf j < (w.prefs i).idxOf (mPartner μ hμ i) := hlt0
    have := opposed_preferences_women μ hμ (mi := j) (mi' := mPartner μ hμ i)
      (j' := wPartner μ hμ j) (matchM_mPartner μ hμ i) hlt (matchW_wPartner μ hμ j)
    omega

lemma meetMan_injective : Function.Injective (meetMan μ ν hμ hν) := by
  intro i1 i2 he
  set j := meetMan μ ν hμ hν i1 with hjdef
  have h1 : meetMan μ ν hμ hν i1 = j := hjdef.symm
  have h2 : meetMan μ ν hμ hν i2 = j := he.symm.trans hjdef.symm
  rcases meetMan_mem_women μ ν hμ hν h1 with hm1 | hn1 <;>
    rcases meetMan_mem_women μ ν hμ hν h2 with hm2 | hn2
  · exact hm1.symm.trans hm2
  · have a := meetMan_worse_left μ ν hμ hν h1 hm1
    have b := meetMan_worse_right μ ν hμ hν h2 hn2
    rw [hn2] at a; rw [hm1] at b
    exact (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i1)).mp
      (le_antisymm b a)
  · have a := meetMan_worse_right μ ν hμ hν h1 hn1
    have b := meetMan_worse_left μ ν hμ hν h2 hm2
    rw [hm2] at a; rw [hn1] at b
    exact (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 i1)).mp
      (le_antisymm b a)
  · exact hn1.symm.trans hn2

/-- The meet man-assignment packaged as an equivalence. -/
noncomputable def meetEquiv : Fin n ≃ Fin n :=
  Equiv.ofBijective (meetMan μ ν hμ hν)
    (Finite.injective_iff_bijective.mp (meetMan_injective μ ν hμ hν))

/-- The **meet** `μ ∧ ν`: each woman keeps her more-preferred man; each man
keeps his less-preferred woman. -/
noncomputable def stableMeet : Matching (Fin n) (Fin n) where
  matchM i := some (meetMan μ ν hμ hν i)
  matchW j := some ((meetEquiv μ ν hμ hν).symm j)
  consistent := by
    intro i j
    simp only [Option.some.injEq]
    rw [Equiv.symm_apply_eq]
    exact eq_comm

@[simp] lemma stableMeet_matchM (i : Fin n) :
    (stableMeet μ ν hμ hν).matchM i = some (meetMan μ ν hμ hν i) := rfl

@[simp] lemma stableMeet_matchW (j : Fin n) :
    (stableMeet μ ν hμ hν).matchW j = some ((meetEquiv μ ν hμ hν).symm j) := rfl

lemma meetMan_le_left (i : Fin n) :
    (w.prefs i).idxOf (meetMan μ ν hμ hν i) ≤ (w.prefs i).idxOf (mPartner μ hμ i) := by
  unfold meetMan; split_ifs with h
  · exact le_refl _
  · push_neg at h; omega

lemma meetMan_le_right (i : Fin n) :
    (w.prefs i).idxOf (meetMan μ ν hμ hν i) ≤ (w.prefs i).idxOf (mPartner ν hν i) := by
  unfold meetMan; split_ifs with h
  · exact h
  · exact le_refl _

/-- The meet of two stable matchings is stable. -/
theorem stableMeet_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m) (stableMeet μ ν hμ hν) := by
  intro i j hblock
  obtain ⟨hi, hj⟩ := hblock
  rw [stableMeet_matchM] at hi
  rw [stableMeet_matchW] at hj
  set jw := (meetEquiv μ ν hμ hν).symm j with hjwdef
  have hi' : (w.prefs i).idxOf j < (w.prefs i).idxOf (meetMan μ ν hμ hν i) := prefM_strict.mp hi
  have hj' : (m.prefs j).idxOf i < (m.prefs j).idxOf jw := prefW_strict.mp hj
  have hmeet_jw : meetMan μ ν hμ hν jw = j := (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν hmeet_jw with hm | hn
  · -- `jw` is `j`'s `μ`-woman, so `(i, j)` blocks `μ`.
    refine hμ i j ⟨?_, ?_⟩
    · rw [matchM_mPartner μ hμ i]
      exact prefM_strict.mpr (lt_of_lt_of_le hi' (meetMan_le_left μ ν hμ hν i))
    · rw [matchW_wPartner μ hμ j, hm]; exact prefW_strict.mpr hj'
  · -- `jw` is `j`'s `ν`-woman, so `(i, j)` blocks `ν`.
    refine hν i j ⟨?_, ?_⟩
    · rw [matchM_mPartner ν hν i]
      exact prefM_strict.mpr (lt_of_lt_of_le hi' (meetMan_le_right μ ν hμ hν i))
    · rw [matchW_wPartner ν hν j, hn]; exact prefW_strict.mpr hj'

/-! ### Order-theoretic characterizations of join and meet -/

lemma wPartner_stableJoin (j : Fin n) :
    wPartner (stableJoin μ ν hμ hν) (stableJoin_isStable μ ν hμ hν) j
      = joinWoman μ ν hμ hν j := rfl

lemma wPartner_stableMeet (j : Fin n) :
    wPartner (stableMeet μ ν hμ hν) (stableMeet_isStable μ ν hμ hν) j
      = (meetEquiv μ ν hμ hν).symm j := rfl

/-- The meet woman of man `j` is one of his two partners (his worse). -/
lemma meetEquiv_symm_eq_or (j : Fin n) :
    (meetEquiv μ ν hμ hν).symm j = wPartner μ hμ j ∨
    (meetEquiv μ ν hμ hν).symm j = wPartner ν hν j := by
  have h : meetMan μ ν hμ hν ((meetEquiv μ ν hμ hν).symm j) = j :=
    (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν h with hm | hn
  · exact Or.inl hm.symm
  · exact Or.inr hn.symm

lemma stableMeet_ge_left (j : Fin n) :
    (m.prefs j).idxOf (wPartner μ hμ j) ≤ (m.prefs j).idxOf ((meetEquiv μ ν hμ hν).symm j) := by
  have h : meetMan μ ν hμ hν ((meetEquiv μ ν hμ hν).symm j) = j :=
    (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν h with hm | hn
  · exact le_of_eq (congrArg (fun x => (m.prefs j).idxOf x) hm)
  · exact meetMan_worse_right μ ν hμ hν h hn

lemma stableMeet_ge_right (j : Fin n) :
    (m.prefs j).idxOf (wPartner ν hν j) ≤ (m.prefs j).idxOf ((meetEquiv μ ν hμ hν).symm j) := by
  have h : meetMan μ ν hμ hν ((meetEquiv μ ν hμ hν).symm j) = j :=
    (meetEquiv μ ν hμ hν).apply_symm_apply j
  rcases meetMan_mem_women μ ν hμ hν h with hm | hn
  · exact meetMan_worse_left μ ν hμ hν h hm
  · exact le_of_eq (congrArg (fun x => (m.prefs j).idxOf x) hn)

/-! ### The lattice of stable matchings -/

/-- The type of stable matchings of a one-to-one market. -/
def StableMatching (w' m' : Preferences n) : Type :=
  { μ : Matching (Fin n) (Fin n) // Matching.IsStable (MatchingMarket.ofEquivData w' m') μ }

namespace StableMatching

/-- Man `j`'s partner under a stable matching. -/
noncomputable def partner (μ : StableMatching w m) (j : Fin n) : Fin n := wPartner μ.1 μ.2 j

lemma matchW_partner (μ : StableMatching w m) (j : Fin n) :
    μ.1.matchW j = some (μ.partner j) := matchW_wPartner μ.1 μ.2 j

/-- Men-preference order: `μ ≤ ν` iff every man weakly prefers his `ν`-partner
to his `μ`-partner (smaller `idxOf` = more preferred). -/
instance : PartialOrder (StableMatching w m) where
  le μ ν := ∀ j : Fin n, (m.prefs j).idxOf (ν.partner j) ≤ (m.prefs j).idxOf (μ.partner j)
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 j := le_trans (h2 j) (h1 j)
  le_antisymm μ ν h1 h2 := by
    have hpart : ∀ j, μ.partner j = ν.partner j := fun j =>
      (List.idxOf_inj (pref_list_mem _ (m.valid j).1 (m.valid j).2 _)).mp
        (le_antisymm (h2 j) (h1 j))
    apply Subtype.ext
    apply Matching.ext
    · funext i
      apply Option.ext; intro k
      rw [μ.1.consistent i k, ν.1.consistent i k,
        matchW_partner μ k, matchW_partner ν k, hpart k]
    · funext j
      rw [matchW_partner μ j, matchW_partner ν j, hpart j]

/-- **Conway–Knuth lattice.** The stable matchings of a one-to-one market form
a lattice under the men-preference order: the join gives every man his more-
preferred of two partners, the meet his less-preferred, and both are stable. -/
noncomputable instance : Lattice (StableMatching w m) :=
  { (inferInstance : PartialOrder (StableMatching w m)) with
    sup := fun μ ν => ⟨stableJoin μ.1 ν.1 μ.2 ν.2, stableJoin_isStable μ.1 ν.1 μ.2 ν.2⟩
    inf := fun μ ν => ⟨stableMeet μ.1 ν.1 μ.2 ν.2, stableMeet_isStable μ.1 ν.1 μ.2 ν.2⟩
    le_sup_left := fun μ ν j => joinWoman_le_left μ.1 ν.1 μ.2 ν.2 j
    le_sup_right := fun μ ν j => joinWoman_le_right μ.1 ν.1 μ.2 ν.2 j
    sup_le := fun μ ν bound h1 h2 j => by
      show (m.prefs j).idxOf (bound.partner j) ≤ (m.prefs j).idxOf (joinWoman μ.1 ν.1 μ.2 ν.2 j)
      rcases joinWoman_eq_or μ.1 ν.1 μ.2 ν.2 j with he | he
      · rw [he]; exact h1 j
      · rw [he]; exact h2 j
    inf_le_left := fun μ ν j => stableMeet_ge_left μ.1 ν.1 μ.2 ν.2 j
    inf_le_right := fun μ ν j => stableMeet_ge_right μ.1 ν.1 μ.2 ν.2 j
    le_inf := fun bound μ ν h1 h2 j => by
      show (m.prefs j).idxOf ((meetEquiv μ.1 ν.1 μ.2 ν.2).symm j)
        ≤ (m.prefs j).idxOf (bound.partner j)
      rcases meetEquiv_symm_eq_or μ.1 ν.1 μ.2 ν.2 j with he | he
      · rw [he]; exact h1 j
      · rw [he]; exact h2 j }

/-! ### Men-optimality as the lattice maximum -/

/-- The men-proposing Gale–Shapley output, as an element of the lattice of
stable matchings. -/
noncomputable def gsStable (w' m' : Preferences n) [NeZero n] : StableMatching w' m' :=
  ⟨Matching.ofGS (gs w' m') (gs_bijective w' m'), galeShapley_isStable w' m'⟩

/-- **The GS output is the greatest stable matching** in the men-preference
order: every man weakly prefers his GS partner to his partner in any other
stable matching. This is `galeShapley_isProposingOptimal` packaged as the
lattice maximum (`⊤`-like greatest element). -/
theorem gsStable_greatest [NeZero n] (μ : StableMatching w m) : μ ≤ gsStable w m := by
  intro j
  show (m.prefs j).idxOf ((gsStable w m).partner j) ≤ (m.prefs j).idxOf (μ.partner j)
  have hg : (gsStable w m).partner j
      = (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j := rfl
  rw [hg]
  exact galeShapley_isProposingOptimal w m μ.1 μ.2 j (μ.partner j) (matchW_partner μ j)

/-- `gsStable` is the greatest element of the stable-matching lattice. -/
theorem gsStable_isGreatest [NeZero n] :
    IsGreatest (Set.univ : Set (StableMatching w m)) (gsStable w m) :=
  ⟨Set.mem_univ _, fun μ _ => gsStable_greatest μ⟩

end StableMatching

end GS
