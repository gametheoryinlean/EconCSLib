/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MarketDesign.Matching.GaleShapley

/-!
# EconCSLib.MarketDesign.Matching.Optimal

**Men-optimal property** of the men-proposing Gale–Shapley deferred-acceptance
algorithm: every man's GS partner is at least as preferred (by him) as his
partner in any other stable matching.

This is the **proposer-side dominance** result. The dual receiver-side
pessimality result belongs with the lattice and Rural-Hospitals developments.

## Main theorem

* `galeShapley_isProposingOptimal` — for every other stable matching `μ`
  pairing man `j` with `wj` (via `μ.matchW j = some wj`; recall the
  codebase convention `M = women, W = men` in `MatchingMarket M W`),
  the GS partner of `j` is ranked at most as high (i.e., as good or
  better) as `wj` in `m.prefs j`.

## Proof strategy (Gale–Shapley 1962 / Gusfield–Irving 1989)

The standard achievable-partner argument. A pair `(j, wj)` is **achievable**
if some stable matching pairs them (`IsAchievable`). The heart of the proof
is the **no-achievable-rejection** invariant on the GS run state:

```
∀ j wj, IsAchievable j wj →
  (m.prefs j).idxOf wj < s.nextChoice j → s.holding wj = some j
```

— informally: "if man `j` has already proposed to woman `wj` and `wj` is
achievable for him, then `wj` is currently holding `j`." Equivalently, no
man has been *rejected* by any of his achievable partners.

Once this invariant holds at `finalState`, the main theorem follows
mechanically: `j`'s GS partner is in his proposed-prefix (by `HoldInv`),
and any other achievable partner must either *also* be in the prefix
(and then by injectivity = the GS partner), or lie strictly past the
prefix (so it's a worse rank).

The inductive step `daStep_NoAchievableRejection` is the deep core (now
proved): if at `daStep` man `q` displaces man `j` at woman `wj` (i.e., `wj`
was holding `j` and switches to `q`), and `wj` is achievable for `j` via
stable matching `μ`, then `(q, wj)` blocks `μ` — because the run invariant
for `s` forces `q` to be free *and* to not yet have proposed past any of his
μ-achievable partners, hence `q` strictly prefers `wj` over his μ-partner.
The invariant carries `HoldInv` and holding-injectivity alongside (both
preserved by `daStep`).

## References

* [MSZ Theorem 22.10] Maschler, Solan, Zamir, *Game Theory*, §22.
* [Gale-Shapley 1962] *Am. Math. Monthly* 69(1):9–15 — original proof.
* [Gusfield-Irving 1989] *The Stable Marriage Problem*, MIT Press.
* [Roth-Sotomayor 1990] *Two-Sided Matching*, Cambridge, §2.2.

-/

open GS

namespace GS

variable {n : ℕ} [NeZero n]
variable (w m : Preferences n)

/-! ### Achievability -/

/-- `IsAchievable w m j wj` says woman `wj` is **achievable** for man `j`:
some stable matching pairs them. Recall the codebase convention
`MatchingMarket M W` with `M = women, W = men`; man `j`'s partner under
`μ` is `μ.matchW j`. -/
def IsAchievable (j wj : Fin n) : Prop :=
  ∃ μ : Matching (Fin n) (Fin n),
    Matching.IsStable (MatchingMarket.ofEquivData w m) μ ∧ μ.matchW j = some wj

/-- The GS output itself witnesses that `gs.symm j` is achievable for `j`. -/
lemma gs_partner_isAchievable (j : Fin n) :
    IsAchievable w m j ((Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j) :=
  ⟨Matching.ofGS (gs w m) (gs_bijective w m), galeShapley_isStable w m, rfl⟩

/-! ### Run-state invariant: no rejection by an achievable partner -/

/-- Run-state invariant for proposer optimality.

`NoAchievableRejection w m s` says: at state `s`, for every achievable pair
`(j, wj)`, if man `j` has already proposed to `wj` (i.e. `idxOf wj < nextChoice j`),
then `wj` is currently holding `j`. Contrapositively, `j` has not been
*rejected* by `wj`. -/
def NoAchievableRejection (s : DAState n) : Prop :=
  ∀ j wj : Fin n, IsAchievable w m j wj →
    (m.prefs j).idxOf wj < s.nextChoice j → s.holding wj = some j

/-- The invariant holds vacuously at `initState`: no man has proposed yet. -/
lemma initState_NoAchievableRejection :
    NoAchievableRejection w m (initState n) := by
  intro j wj _ h
  simp [initState] at h

/-- **Inductive step (KEY LEMMA).** `NoAchievableRejection` is preserved by
one `daStep`. Also threads `HoldInv` (for the old-holder index bound) and
holding-injectivity (a man is held by at most one woman).

Proof: reduce `(daStep).holding wj` to its `match` and split on whether `j`
had already proposed to `wj` before this round (`hinv` then pins
`s.holding wj = some j`) or proposes exactly now (`j ∈ pl wj`). In every
branch where some `h ≠ j` ends up holding `wj`, the local `build_block`
helper produces a blocking pair `(h, wj)` for the achievability witness `μ`:

* `wj` prefers `h` to `j = μ.matchM wj` — because `daStep`'s `argmin`/`if`
  chose `h` over `j` (and `idxOf` is injective on the Nodup list).
* `h` prefers `wj` to his μ-partner `wh` — because `(m.prefs h).idxOf wj ≤
  s.nextChoice h` (propTarget identity if `h` just proposed; `HoldInv` if `h`
  was already holding `wj`), while `hinv` applied to `(h, wh)` forces
  `s.nextChoice h ≤ (m.prefs h).idxOf wh` (using that `h` is not held by `wh`
  at `s` — freshness, or injectivity since `h` holds `wj ≠ wh`).

A blocking pair contradicts `μ`'s stability, so no such displacement occurs:
`wj` keeps/takes `j`, and the invariant is preserved. -/
lemma daStep_NoAchievableRejection (s : DAState n)
    (hhold : HoldInv m s)
    (hinj : ∀ j1 j2 i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2)
    (hinv : NoAchievableRejection w m s) :
    NoAchievableRejection w m (daStep w m s) := by
  intro j wj hach hlt
  obtain ⟨μ, hμ_stable, hμ_match⟩ := hach
  have hach2 : IsAchievable w m j wj := ⟨μ, hμ_stable, hμ_match⟩
  -- `μ` pairs woman `wj` with man `j` (consistency: M = women, W = men).
  have hμ_m : μ.matchM wj = some j := (μ.consistent wj j).mpr hμ_match
  -- Abbreviations matching `daStep`'s inner `let`s.
  set pl : Fin n → List (Fin n) := fun p =>
    (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList with pl_def
  set bn : Fin n → Option (Fin n) := fun p =>
    (pl p).argmin (fun k => (w.prefs p).idxOf k) with bn_def
  -- Every member of `pl wj` is a free man who proposed to `wj` this round.
  have pl_props : ∀ q, q ∈ pl wj →
      isFree s q = true ∧ propTarget m q (s.nextChoice q) = some wj := by
    intro q hq
    rw [pl_def] at hq
    simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hq
    exact hq
  -- For a proposer `q`, `wj` sits at index `s.nextChoice q` of `m.prefs q`.
  have proposer_idx : ∀ q, q ∈ pl wj → (m.prefs q).idxOf wj = s.nextChoice q := by
    intro q hq
    obtain ⟨_, hpt⟩ := pl_props q hq
    obtain ⟨hlt', hget⟩ : ∃ h, (m.prefs q)[s.nextChoice q]'h = wj :=
      List.getElem?_eq_some_iff.mp hpt
    rw [← hget, (m.valid q).1.idxOf_getElem _ hlt']
  -- If `j` is free and his cursor points at `wj`, then `j ∈ pl wj`.
  have j_in_pl : isFree s j = true → (m.prefs j).idxOf wj = s.nextChoice j → j ∈ pl wj := by
    intro hfj hidx
    rw [pl_def]
    simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter, Finset.mem_univ,
      true_and, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hfj, ?_⟩
    show (m.prefs j)[s.nextChoice j]? = some wj
    rw [← hidx]
    exact List.getElem?_idxOf (pref_list_mem _ (m.valid j).1 (m.valid j).2 wj)
  -- `idxOf`-injectivity helper on a preference list.
  have idxOf_lt_of_ne : ∀ (p a b : Fin n), a ≠ b →
      (w.prefs p).idxOf a ≤ (w.prefs p).idxOf b → (w.prefs p).idxOf a < (w.prefs p).idxOf b := by
    intro p a b hab hle
    refine lt_of_le_of_ne hle (fun e => hab ?_)
    exact (List.idxOf_inj (pref_list_mem _ (w.valid p).1 (w.valid p).2 a)).mp e
  -- THE BLOCKING-PAIR CONTRADICTION (Gusfield–Irving core).
  -- Given a man `h ≠ j` whom `wj` prefers to `j`, who has proposed to `wj` by
  -- round `s` (idxOf `wj` ≤ his cursor), and who is either free or already
  -- holding `wj`, the pair `(h, wj)` blocks the achievability witness `μ`.
  have build_block : ∀ h : Fin n, h ≠ j →
      (w.prefs wj).idxOf h < (w.prefs wj).idxOf j →
      (m.prefs h).idxOf wj ≤ s.nextChoice h →
      (isFree s h = true ∨ s.holding wj = some h) →
      False := by
    intro h hne hpref hbound hsrc
    -- Man side: `h` strictly prefers `wj` to his μ-partner.
    have hman : strict ((MatchingMarket.ofEquivData w m).prefW h).rel (some wj) (μ.matchW h) := by
      cases hwh : μ.matchW h with
      | none => exact ⟨trivial, not_false⟩
      | some wh =>
          have hwh_ne : wh ≠ wj := by
            intro heq
            have hcon : μ.matchM wj = some h := (μ.consistent wj h).mpr (heq ▸ hwh)
            rw [hμ_m] at hcon
            exact hne (Option.some.inj hcon).symm
          have hnotheld : s.holding wh ≠ some h := by
            rcases hsrc with hfree | hheld
            · exact (isFree_iff s h).mp hfree wh
            · intro hcon; exact hwh_ne (hinj wh wj h hcon hheld)
          have hge : s.nextChoice h ≤ (m.prefs h).idxOf wh := by
            by_contra hlt2; push_neg at hlt2
            exact hnotheld (hinv h wh ⟨μ, hμ_stable, hwh⟩ hlt2)
          have hidx_ne : (m.prefs h).idxOf wj ≠ (m.prefs h).idxOf wh := fun heq =>
            hwh_ne ((List.idxOf_inj (pref_list_mem _ (m.valid h).1 (m.valid h).2 wj)).mp heq).symm
          refine ⟨?_, ?_⟩
          · show (m.prefs h).idxOf wj ≤ (m.prefs h).idxOf wh; omega
          · show ¬ (m.prefs h).idxOf wh ≤ (m.prefs h).idxOf wj; omega
    -- Woman side: `wj` strictly prefers `h` to her μ-partner `j`.
    have hwoman : strict ((MatchingMarket.ofEquivData w m).prefM wj).rel (some h) (μ.matchM wj) := by
      rw [hμ_m]
      exact ⟨by show (w.prefs wj).idxOf h ≤ (w.prefs wj).idxOf j; omega,
             by show ¬ (w.prefs wj).idxOf j ≤ (w.prefs wj).idxOf h; omega⟩
    exact hμ_stable wj h ⟨hwoman, hman⟩
  -- Reduce `(daStep).holding wj` to the canonical `match` and fold `bn`.
  rw [daStep_holding]
  change (match s.holding wj, bn wj with
    | none,   none   => none
    | some h, none   => some h
    | none,   some q => some q
    | some h, some q =>
        if (w.prefs wj).idxOf q < (w.prefs wj).idxOf h then some q else some h) = some j
  -- Dichotomy from `hlt`: either `j` had already proposed to `wj` before this
  -- round, or `j` is free and proposes to `wj` exactly now.
  rcases (by
      by_cases hfj : isFree s j = true
      · rw [daStep_nc_free hfj] at hlt
        rcases Nat.lt_or_ge ((m.prefs j).idxOf wj) (s.nextChoice j) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hfj, by omega⟩
      · simp only [Bool.not_eq_true] at hfj
        rw [daStep_nc_held hfj] at hlt
        exact Or.inl hlt :
      (m.prefs j).idxOf wj < s.nextChoice j ∨
        (isFree s j = true ∧ (m.prefs j).idxOf wj = s.nextChoice j)) with hlt' | ⟨hfj, hidx⟩
  · -- `j` already proposed: `hinv` forces `wj` to currently hold `j`.
    have hsj : s.holding wj = some j := hinv j wj hach2 hlt'
    rw [hsj]
    cases hbq : bn wj with
    | none => rfl
    | some q =>
        show (if (w.prefs wj).idxOf q < (w.prefs wj).idxOf j then some q else some j) = some j
        have hq_pl : q ∈ pl wj := List.argmin_mem hbq
        obtain ⟨hfq, _⟩ := pl_props q hq_pl
        split_ifs with hcmp
        · by_cases hqj : q = j
          · rw [hqj]
          · exact (build_block q hqj hcmp (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
        · rfl
  · -- `j` proposes this round, so `j ∈ pl wj` and `bn wj` is non-`none`.
    have hjpl : j ∈ pl wj := j_in_pl hfj hidx
    cases hbq : bn wj with
    | none =>
        exfalso
        have hnil : pl wj = [] := List.argmin_eq_none.mp (by simpa only [bn_def] using hbq)
        rw [hnil] at hjpl
        simp at hjpl
    | some q =>
        have hq_pl : q ∈ pl wj := List.argmin_mem hbq
        obtain ⟨hfq, _⟩ := pl_props q hq_pl
        have hq_le : (w.prefs wj).idxOf q ≤ (w.prefs wj).idxOf j :=
          List.le_of_mem_argmin hjpl hbq
        cases hsw : s.holding wj with
        | none =>
            show some q = some j
            by_cases hqj : q = j
            · rw [hqj]
            · exact (build_block q hqj (idxOf_lt_of_ne wj q j hqj hq_le)
                (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
        | some h0 =>
            show (if (w.prefs wj).idxOf q < (w.prefs wj).idxOf h0 then some q else some h0)
              = some j
            split_ifs with hcmp
            · by_cases hqj : q = j
              · rw [hqj]
              · exact (build_block q hqj (idxOf_lt_of_ne wj q j hqj hq_le)
                  (le_of_eq (proposer_idx q hq_pl)) (Or.inl hfq)).elim
            · by_cases hh0j : h0 = j
              · rw [hh0j]
              · refine (build_block h0 hh0j ?_ ?_ (Or.inr hsw)).elim
                · -- `wj` prefers `h0` to `j`: idxOf h0 ≤ idxOf q ≤ idxOf j, strict.
                  push_neg at hcmp
                  exact idxOf_lt_of_ne wj h0 j hh0j (le_trans hcmp hq_le)
                · -- `h0` holds `wj`, so by HoldInv `wj` is in his proposed-prefix.
                  have hmem := hhold h0 wj hsw
                  have := (List.mem_take_iff_idxOf_lt
                    (pref_list_mem _ (m.valid h0).1 (m.valid h0).2 wj)).mp hmem
                  omega

/-- `NoAchievableRejection` is preserved by `daRun` (threading `HoldInv` and
holding-injectivity, both also preserved by `daStep`). -/
lemma daRun_NoAchievableRejection (fuel : ℕ) (s : DAState n)
    (hhold : HoldInv m s)
    (hinj : ∀ j1 j2 i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2)
    (hinv : NoAchievableRejection w m s) :
    NoAchievableRejection w m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hinv
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (holdinv_step w m s hhold) (holding_injective_step w m s hinj)
          (daStep_NoAchievableRejection w m s hhold hinj hinv)
      · exact hinv

/-- The invariant holds at `finalState`. -/
lemma finalState_NoAchievableRejection :
    NoAchievableRejection w m (finalState w m) :=
  daRun_NoAchievableRejection w m (n * n + 1) (initState n)
    (holdinv_init m) (initState_injective (n := n))
    (initState_NoAchievableRejection w m)

/-! ### Main theorem -/

/-- **Men-optimal stable matching** (Gale–Shapley 1962, [MSZ 22.10]):
in the men-proposing DA, every man's GS partner is at least as preferred
(by him) as his partner under *any* other stable matching `μ`.

Equivalently: for any stable `μ` pairing man `j` with woman `wj`, the GS
output's matching of `j` is ranked at most as high (i.e., as good or
better) as `wj` in `m.prefs j`. -/
theorem galeShapley_isProposingOptimal
    (μ : Matching (Fin n) (Fin n))
    (hμ : Matching.IsStable (MatchingMarket.ofEquivData w m) μ) :
    ∀ (j wj : Fin n), μ.matchW j = some wj →
      (m.prefs j).idxOf ((Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j) ≤
        (m.prefs j).idxOf wj := by
  intro j wj hwj
  -- `(j, wj)` is achievable via `μ`.
  have hach : IsAchievable w m j wj := ⟨μ, hμ, hwj⟩
  -- Let `wjs` be j's GS partner.
  set wjs : Fin n := (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j with wjs_def
  -- Step 1. `wjs` holds `j` in `finalState`.
  have hwjs_apply : gs w m wjs = j :=
    (Equiv.ofBijective (gs w m) (gs_bijective w m)).apply_symm_apply j
  have hwjs_holds : (finalState w m).holding wjs = some j := by
    obtain ⟨h, hh⟩ := final_all_women_hold w m wjs
    have hgs_h : gs w m wjs = h := by simp [gs, hh]
    rw [hgs_h] at hwjs_apply
    exact hwjs_apply ▸ hh
  -- Step 2. By `HoldInv` at `finalState`, `idxOf wjs < nextChoice j`.
  have hwjs_lt : (m.prefs j).idxOf wjs < (finalState w m).nextChoice j :=
    (List.mem_take_iff_idxOf_lt
        (pref_list_mem _ (m.valid j).1 (m.valid j).2 _)).mp
      (holdinv_finalState w m j wjs hwjs_holds)
  -- Step 3. Case-split on whether `wj` lies inside j's proposed-prefix.
  by_cases hwj_lt : (m.prefs j).idxOf wj < (finalState w m).nextChoice j
  · -- `wj` was proposed to. By the invariant, `wj` must currently hold `j`.
    have hwj_holds : (finalState w m).holding wj = some j :=
      finalState_NoAchievableRejection w m j wj hach hwj_lt
    -- Both `wjs` and `wj` hold `j` — by injectivity, they're equal.
    have hwj_eq_wjs : wj = wjs :=
      final_holding_injective w m wj wjs j hwj_holds hwjs_holds
    rw [hwj_eq_wjs]
  · -- `wj` was not proposed to: `nextChoice j ≤ idxOf wj`.
    push_neg at hwj_lt
    omega

end GS
