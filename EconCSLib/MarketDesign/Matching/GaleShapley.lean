/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MarketDesign.Matching.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# EconCSLib.MarketDesign.Matching.GaleShapley

Standard Gale-Shapley deferred-acceptance algorithm for two-sided matching markets.

Replaces the earlier batched-proposal (Boston-mechanism) `gs_aux` that committed
women in round 1 with no ability to upgrade — verified unstable via `#eval` (commit
1e14bf9: blocking pair (b, A) on the n=3 counterexample).

## Scope (MT-L0 + MT-L1, #202 + #203)

* `GS.Preferences n` — list-based preference type for the algorithmic layer.
* Standard DA: `GS.daStep`, `GS.daRun`, `GS.finalState`, `GS.gs`.
* `gs_bijective` — proved via injectivity + pigeonhole.
* `galeShapley_isStable` — stability via the standard deferred-acceptance argument.
* Bridge types: `MatchingMarket.ofEquivData`, `Matching.ofGS`.

## Algorithm design

Standard men-proposing DA with explicit state `(nextChoice, holding)`:

- `holding j = some i`: woman `j` currently holds man `i` tentatively.
- `nextChoice i = k`: man `i`'s next proposal is `(m.prefs i)[k]`.
- A man is *free* when no woman holds him.
- Each step: every free man proposes his next-best woman; each woman keeps the best
  of {held, new proposers} by her preference list rank; free men advance nextChoice.
- Termination: structural recursion on fuel `n*n + 1`. At most `n*n` proposals
  total (n men × n proposals each).

## Key invariants

All preserved by every `daStep` (preservation lemmas listed in parentheses).

1. **Rank monotonicity** — a woman's held man's rank only decreases over time;
   once she upgrades, she never downgrades (`holding_rank_mono_step` / `_run`).
2. **Holding injectivity** — at most one woman holds any given man at any
   time (`holding_injective_step` / `_run`).
3. **`JInv`** — *proposed ⇒ held*: every woman who has ever been proposed
   to is currently held by someone (`jinv_step`).
4. **`HoldInv`** — *held ⇒ proposed*: every currently-held pair `(p, j)` has
   `j` having already proposed to `p` (`holdinv_step`).
5. **`RSInv`** — the deferred-acceptance rank invariant (the stability engine):
   every woman a man has proposed to is currently holding someone at least as
   preferred as that man (`rsinv_step`).
6. At termination: all men held → all women hold someone (by pigeonhole on
   `holding_injective`).

## Proof strategy (from primitives to stability)

```
            initState
                │
                │  daStep (preserves all six invariants)
                ▼
            finalState
            │   │   │
            │   │   └─► holding_injective  ──┐
            │   │                            ├─► gs_bijective ──┐
            │   └─────► all men held        ─┘                  │
            │                                                   ▼
            └─────► RSInv@finalState ──► no blocking pair (stability)
                       │       └────── HoldInv@finalState
                       │
                       └── relies on rank-mono + JInv
```

Roughly: cursors and holdings stay in two-sided correspondence (`JInv`
+ `HoldInv`); a held pair only upgrades (`holding_rank_mono`); at most
one woman holds any man (`holding_injective`); cursors are bounded by
`n` (`nc_le_n_run`) and grow monotonically (`nc_sum_grows`), so the
fuel `n*n + 1` always suffices for termination (`finalState_no_free_men`);
and at termination `RSInv` rules out blocking pairs (`rsinv_stability`).

## References

* [Gale-Shapley 1962] *Am. Math. Monthly* 69(1):9-15 — original existence proof.
* [Roth-Sotomayor 1990] *Two-Sided Matching*, Ch. 2-3 — textbook treatment of
  deferred acceptance and stability.
* [MSZ Ch.22, Alg 22.6 + Thm 22.7] Maschler, Solan, Zamir, *Game Theory* — the
  deferred-acceptance algorithm and its stability theorem.
-/

open List Finset

namespace GS

/-! ### Preference type -/

/-- List-based preferences: `prefs i` is a full permutation of `Fin n`,
    ordered from most to least preferred. -/
structure Preferences (n : ℕ) where
  prefs : Fin n → List (Fin n)
  valid : ∀ i, (prefs i).Nodup ∧ (prefs i).length = n

/-! ### Helper lemmas -/

/-- Every element of `Fin n` appears in a full-permutation list. -/
lemma pref_list_mem {n : ℕ} (l : List (Fin n)) (hnd : l.Nodup) (hlen : l.length = n)
    (x : Fin n) : x ∈ l := by
  rw [← List.mem_toFinset]
  exact (Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, hlen,
    Fintype.card_fin])).symm ▸ Finset.mem_univ _

/-! ### DA state -/

/-- DA state: per-man proposal cursor + per-woman tentative hold. -/
structure DAState (n : ℕ) where
  nextChoice : Fin n → ℕ
  holding    : Fin n → Option (Fin n)

/-- Initial state: all women free, all men start at proposal index 0. -/
def initState (n : ℕ) : DAState n :=
  { nextChoice := fun _ => 0, holding := fun _ => none }

/-! ### Free-man predicate -/

/-- Man `i` is free in `s` iff no woman holds him. -/
def isFree {n : ℕ} (s : DAState n) (i : Fin n) : Bool :=
  decide (∀ j : Fin n, s.holding j ≠ some i)

lemma isFree_iff {n : ℕ} (s : DAState n) (i : Fin n) :
    isFree s i = true ↔ ∀ j : Fin n, s.holding j ≠ some i := by simp [isFree]

lemma not_isFree_iff {n : ℕ} (s : DAState n) (i : Fin n) :
    isFree s i = false ↔ ∃ j : Fin n, s.holding j = some i := by
  simp [isFree, decide_eq_false_iff_not, not_forall, ne_eq]

/-- The finset of all free men in `s`. -/
def freeMenSet {n : ℕ} (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => isFree s i)

lemma mem_freeMenSet {n : ℕ} {s : DAState n} {i : Fin n} :
    i ∈ freeMenSet s ↔ isFree s i = true := by simp [freeMenSet]

/-! ### Proposal target -/

/-- The woman man `i` proposes to at cursor index `k` (none if out of bounds). -/
def propTarget {n : ℕ} (m : Preferences n) (i : Fin n) (k : ℕ) : Option (Fin n) :=
  (m.prefs i)[k]?

/-- `propTarget` returns `some` when `k < n`. -/
lemma propTarget_lt {n : ℕ} (m : Preferences n) (i : Fin n) {k : ℕ} (hk : k < n) :
    ∃ j, propTarget m i k = some j := by
  have hlen : k < (m.prefs i).length := by rwa [(m.valid i).2]
  exact ⟨(m.prefs i)[k], List.getElem?_eq_getElem hlen⟩

/-! ### DA step -/

/-- One step of standard men-proposing DA.

    All free men propose; women pick the best of {held, new proposers} by rank;
    free men advance their cursor by 1. -/
noncomputable def daStep {n : ℕ} (w m : Preferences n) (s : DAState n) : DAState n :=
  let newNextChoice : Fin n → ℕ := fun i =>
    if isFree s i then s.nextChoice i + 1 else s.nextChoice i
  let proposerList : Fin n → List (Fin n) := fun j =>
    (Finset.univ.filter (fun i =>
      isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList
  let bestNew : Fin n → Option (Fin n) := fun j =>
    (proposerList j).argmin (fun i => (w.prefs j).idxOf i)
  let newHolding : Fin n → Option (Fin n) := fun j =>
    match s.holding j, bestNew j with
    | none,   none   => none
    | some h, none   => some h
    | none,   some p => some p
    | some h, some p =>
        if (w.prefs j).idxOf p < (w.prefs j).idxOf h then some p else some h
  { nextChoice := newNextChoice, holding := newHolding }

lemma daStep_nc_free {n : ℕ} {w m : Preferences n} {s : DAState n} {i : Fin n}
    (hi : isFree s i = true) : (daStep w m s).nextChoice i = s.nextChoice i + 1 := by
  simp [daStep, hi]

lemma daStep_nc_held {n : ℕ} {w m : Preferences n} {s : DAState n} {i : Fin n}
    (hi : isFree s i = false) : (daStep w m s).nextChoice i = s.nextChoice i := by
  simp [daStep, hi]

/-- One step of DA: woman `p`'s new holding, expanded once.

This is the workhorse rewrite for any proof that needs to case-split on
what `(daStep w m s).holding p` is. It unfolds the outermost `match`
inside `daStep`'s `newHolding`. The statement **does inline** the auxiliary
`proposerList` / `bestNew` formulae verbatim; downstream proofs re-abbreviate
them with `set` *after* rewriting (see `holdinv_step`).

The match shape is:

```
match s.holding p, bestNew p with
| none,   none   => none                                  -- still free
| some h, none   => some h                                -- old hold kept
| none,   some q => some q                                -- new proposer
| some h, some q => if rank q < rank h then q else h      -- upgrade?
```

where `bestNew p = (proposerList p).argmin (rank in w.prefs p)` and
`proposerList p` is the list of free men who proposed to `p` this step.

Provable by `rfl` because `daStep` is `noncomputable def` and the body
is a sequence of `let`s ending in a structure literal whose `.holding p`
projects directly to the inner `match`. -/
lemma daStep_holding {n : ℕ} (w m : Preferences n) (s : DAState n) (p : Fin n) :
    (daStep w m s).holding p =
      (match s.holding p,
        ((Finset.univ.filter (fun i : Fin n =>
            isFree s i && (propTarget m i (s.nextChoice i) == some p))).val.toList).argmin
          (fun i => (w.prefs p).idxOf i) with
        | none,   none   => none
        | some h, none   => some h
        | none,   some q => some q
        | some h, some q =>
            if (w.prefs p).idxOf q < (w.prefs p).idxOf h then some q else some h) := rfl

/-! ### DA run (structurally recursive, no WF needed) -/

/-- Run DA for at most `fuel` steps, stopping early if no free men remain. -/
noncomputable def daRun {n : ℕ} (w m : Preferences n) : ℕ → DAState n → DAState n
  | 0,        s => s
  | fuel + 1, s => if (freeMenSet s).Nonempty then daRun w m fuel (daStep w m s) else s

/-- `finalState`: run `daRun` with fuel `n*n + 1` from `initState`. -/
noncomputable def finalState {n : ℕ} (w m : Preferences n) : DAState n :=
  daRun w m (n * n + 1) (initState n)

/-- The Gale-Shapley function: woman `j`'s partner at termination. -/
noncomputable def gs {n : ℕ} [NeZero n] (w m : Preferences n) : Fin n → Fin n := fun j =>
  (finalState w m).holding j |>.getD default

end GS

/-! ### Bridge to EconCSLib native types -/

namespace MatchingMarket

open GS

variable {n : ℕ} [NeZero n]

/-- Build a `MatchingMarket (Fin n) (Fin n)` from list-based preference data.
    `some j ≻ some k` iff `j` appears earlier in the list; `none` is worst.

    **Side transposition (read carefully).** `ofEquivData a b` puts `a` on the
    market's MEN (`prefM`) and `b` on the market's WOMEN (`prefW`). Hence when it
    is applied as `ofEquivData w m` with the algorithm's `w` (women's / choosing
    preferences) and `m` (men's / proposing preferences), the market's "men" are
    the algorithm's *women* and the market's "women" are the algorithm's *men* —
    the two sides are **transposed**. Stability is symmetric, so this is
    harmless, but be aware that a market-`M` index corresponds to an algorithm
    woman (and vice versa); the stability proof reasons in the algorithm frame. -/
noncomputable def ofEquivData (wPrefs mPrefs : GS.Preferences n) :
    MatchingMarket (Fin n) (Fin n) where
  prefM := fun i =>
    { rel := fun ow1 ow2 =>
        match ow1, ow2 with
        | none,    none    => True
        | none,    some _  => False
        | some _,  none    => True
        | some w1, some w2 => (wPrefs.prefs i).idxOf w1 ≤ (wPrefs.prefs i).idxOf w2
      prop :=
        { reflexive := ⟨by intro ow; cases ow <;> simp⟩
          transitive := ⟨by
            intro ow1 ow2 ow3 h12 h23
            cases ow1 <;> cases ow2 <;> cases ow3 <;> simp_all
            exact Nat.le_trans h12 h23⟩
          total := by
            intro ow1 ow2; cases ow1 <;> cases ow2 <;> simp
            exact Nat.le_or_le _ _ } }
  prefW := fun j =>
    { rel := fun om1 om2 =>
        match om1, om2 with
        | none,    none    => True
        | none,    some _  => False
        | some _,  none    => True
        | some m1, some m2 => (mPrefs.prefs j).idxOf m1 ≤ (mPrefs.prefs j).idxOf m2
      prop :=
        { reflexive := ⟨by intro om; cases om <;> simp⟩
          transitive := ⟨by
            intro om1 om2 om3 h12 h23
            cases om1 <;> cases om2 <;> cases om3 <;> simp_all
            exact Nat.le_trans h12 h23⟩
          total := by
            intro om1 om2; cases om1 <;> cases om2 <;> simp
            exact Nat.le_or_le _ _ } }

end MatchingMarket

namespace Matching

open GS

variable {n : ℕ} [NeZero n]

/-- Coerce a bijective `f : Fin n → Fin n` into `Matching (Fin n) (Fin n)`. -/
noncomputable def ofGS (f : Fin n → Fin n) (hf : Function.Bijective f) :
    Matching (Fin n) (Fin n) where
  matchM := fun w => some (f w)
  matchW := fun m => some ((Equiv.ofBijective f hf).symm m)
  consistent := by
    intro m w; simp only [Option.some.injEq]
    rw [Equiv.symm_apply_eq]; exact eq_comm

end Matching

/-! ### Correctness (MT-L1 #203) -/

section GS_Correctness

open GS

variable {n : ℕ} [NeZero n]
variable (w m : Preferences n)

/-! #### Invariant 1: `holding` rank monotonically improves -/

/-- After one `daStep`, woman `j`'s held man's rank can only decrease (she only upgrades). -/
lemma holding_rank_mono_step (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h' : Fin n, (daStep w m s).holding j = some h' ∧
      (w.prefs j).idxOf h' ≤ (w.prefs j).idxOf hval := by
  simp only [daStep]
  set pl := (Finset.univ.filter (fun i =>
    isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList
  cases pl.argmin (fun i => (w.prefs j).idxOf i) with
  | none => exact ⟨hval, by simp [hh], le_refl _⟩
  | some p =>
      simp only [hh]
      split_ifs with hlt
      · exact ⟨p, rfl, Nat.le_of_lt hlt⟩
      · exact ⟨hval, rfl, le_refl _⟩

/-- Rank-mono over any `daRun`. -/
lemma holding_rank_mono_run (fuel : ℕ) (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h' : Fin n, (daRun w m fuel s).holding j = some h' ∧
      (w.prefs j).idxOf h' ≤ (w.prefs j).idxOf hval := by
  induction fuel generalizing s hval with
  | zero   => exact ⟨hval, hh, le_refl _⟩
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne
      · obtain ⟨h1, hh1, hrk1⟩ := holding_rank_mono_step w m s j hh
        obtain ⟨h2, hh2, hrk2⟩ := ih (daStep w m s) hh1
        exact ⟨h2, hh2, Nat.le_trans hrk2 hrk1⟩
      · exact ⟨hval, hh, le_refl _⟩

/-- Once held, always held over `daRun`. -/
lemma held_preserved_run (fuel : ℕ) (s : DAState n) (j : Fin n) {hval : Fin n}
    (hh : s.holding j = some hval) :
    ∃ h', (daRun w m fuel s).holding j = some h' :=
  (holding_rank_mono_run w m fuel s j hh).imp fun _ ⟨eq, _⟩ => eq

/-! #### Invariant 2: `holding` is injective -/

/-- Helper: membership in the proposerList implies freedom and proposal target. -/
private lemma pl_free_props {n : ℕ} (s : DAState n) (m : Preferences n) (j k : Fin n) :
    let pl : Fin n → List (Fin n) := fun j' =>
      (Finset.univ.filter (fun i =>
        isFree s i && (propTarget m i (s.nextChoice i) == some j'))).val.toList
    k ∈ pl j →
    isFree s k = true ∧ propTarget m k (s.nextChoice k) = some j := by
  intro pl hk
  change k ∈ (Finset.univ.filter (fun i =>
    isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList at hk
  simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter,
    Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hk
  exact hk

/-- In `daStep`, `holding` remains injective. -/
lemma holding_injective_step (s : DAState n)
    (hinj : ∀ j1 j2 : Fin n, ∀ i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2) :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (daStep w m s).holding j1 = some i → (daStep w m s).holding j2 = some i → j1 = j2 := by
  intro j1 j2 i hj1 hj2
  -- The proposerList and bestNew for each woman
  let pl : Fin n → List (Fin n) := fun j =>
    (Finset.univ.filter (fun k =>
      isFree s k && (propTarget m k (s.nextChoice k) == some j))).val.toList
  have pl_disj : ∀ k : Fin n, ∀ j1' j2' : Fin n,
      k ∈ pl j1' → k ∈ pl j2' → j1' = j2' := by
    intro k j1' j2' hk1 hk2
    exact Option.some.inj
      ((pl_free_props s m j1' k hk1).2.symm.trans (pl_free_props s m j2' k hk2).2)
  let bn : Fin n → Option (Fin n) := fun j =>
    (pl j).argmin (fun k => (w.prefs j).idxOf k)
  have bn_mem : ∀ j p : Fin n, bn j = some p → p ∈ pl j := fun j p hp =>
    List.argmin_mem hp
  -- `newHolding j = some i` means i came via bn j or from s.holding j
  have result_source : ∀ j : Fin n,
      (daStep w m s).holding j = some i →
      bn j = some i ∨ s.holding j = some i := by
    intro j hj
    simp only [daStep] at hj
    rcases hs : s.holding j with _ | h <;> rcases hb : bn j with _ | p <;>
    simp only [hs, show (Finset.univ.filter (fun k =>
        isFree s k && (propTarget m k (s.nextChoice k) == some j))).val.toList.argmin
        (fun k => idxOf k (w.prefs j)) = bn j from rfl] at hj <;>
    simp_all [bn] <;> split_ifs at hj with hlt <;> simp_all
  rcases result_source j1 hj1 with hbn1 | hold1
  · -- i came via proposals to j1 → i was free in s
    have hi_free : isFree s i = true := (pl_free_props s m j1 i (bn_mem j1 i hbn1)).1
    rcases result_source j2 hj2 with hbn2 | hold2
    · -- both via proposals → j1 = j2 (same man can only propose to one woman)
      exact pl_disj i j1 j2 (bn_mem j1 i hbn1) (bn_mem j2 i hbn2)
    · -- j2 via old holding: i was free but s.holding j2 = some i → contradiction
      rw [isFree_iff] at hi_free; exact absurd hold2 (hi_free j2)
  · rcases result_source j2 hj2 with hbn2 | hold2
    · -- j1 via old holding, j2 via proposals → contradiction
      have hi_free : isFree s i = true := (pl_free_props s m j2 i (bn_mem j2 i hbn2)).1
      rw [isFree_iff] at hi_free; exact absurd hold1 (hi_free j1)
    · -- both via old holding → induction hypothesis
      exact hinj j1 j2 i hold1 hold2

/-- Over `daRun`, holding remains injective. -/
lemma holding_injective_run (fuel : ℕ) (s : DAState n)
    (hinj : ∀ j1 j2 : Fin n, ∀ i : Fin n,
      s.holding j1 = some i → s.holding j2 = some i → j1 = j2) :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (daRun w m fuel s).holding j1 = some i → (daRun w m fuel s).holding j2 = some i → j1 = j2 := by
  induction fuel generalizing s with
  | zero   => exact hinj
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne
      · exact ih (daStep w m s) (holding_injective_step w m s hinj)
      · exact hinj

/-- `initState` has trivially injective holding (all `none`). -/
lemma initState_injective :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (initState n).holding j1 = some i → (initState n).holding j2 = some i → j1 = j2 := by
  intro j1 j2 i h1; simp [initState] at h1

/-! #### Invariant 3: fuel sufficiency -/

end GS_Correctness

/-! The following private lemmas are defined outside `section GS_Correctness` to avoid
    implicit section variable clutter.  All parameters are explicit. -/

section GS_Fuel

open GS

variable {n : ℕ} [NeZero n]

/-- **JInv** (Proposed → Held): once man `i` has proposed to woman `p` in some
prior step, `p` is currently held by *someone* (possibly `i`, possibly someone
better).

Formally: every `p` in the prefix `(m.prefs i).take (s.nextChoice i)` of `i`'s
preference list — i.e., every woman `i` has already proposed to — has
`s.holding p = some _`.

This is the **"once proposed-to, always held"** invariant: a woman who has
ever received a proposal can never go back to being unmatched. It is the dual
of [`HoldInv`] (every currently-held woman is in her holder's proposed
prefix), which gives the converse direction.

Together `JInv` and `HoldInv` pin down a bidirectional correspondence between
the per-man cursors and the per-woman holdings, which the stability proof
needs in both directions. -/
private def JInv (m : Preferences n) (s : DAState n) : Prop :=
  ∀ i p : Fin n, p ∈ (m.prefs i).take (s.nextChoice i) → ∃ h : Fin n, s.holding p = some h

private lemma jinv_init (m : Preferences n) : JInv m (initState n) := by
  intro i p hp; simp [initState] at hp

/-- Free man `i` proposing to woman `p` makes her held in `daStep`. -/
private lemma daStep_held_of_free_prop (w m : Preferences n) (s : DAState n) (i p : Fin n)
    (hfi : isFree s i = true) (hpt : propTarget m i (s.nextChoice i) = some p) :
    ∃ h : Fin n, (daStep w m s).holding p = some h := by
  have hi_in : i ∈ (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList :=
    Multiset.mem_toList.mpr (Finset.mem_val.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hfi, hpt]⟩))
  -- The proposer list is nonempty (i is in it), so argmin returns Some.
  set pl := (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p))).val.toList with hpl_def
  have hne_pl : pl ≠ [] := List.ne_nil_of_mem hi_in
  have hbn : ∃ q : Fin n, pl.argmin (fun k => (w.prefs p).idxOf k) = some q :=
    (Option.ne_none_iff_exists.mp (List.argmin_eq_none.not.mpr hne_pl)).imp (fun _ h => h.symm)
  obtain ⟨q, hq⟩ := hbn
  simp only [daStep, ← hpl_def]
  cases hs : s.holding p with
  | none   => simp only [hs, hq]; exact ⟨q, rfl⟩
  | some h => simp only [hs, hq]; split_ifs <;> exact ⟨_, rfl⟩

/-- `JInv` is preserved by one `daStep`. -/
private lemma jinv_step (w m : Preferences n) (s : DAState n) (hj : JInv m s) :
    JInv m (daStep w m s) := by
  intro i p hp
  -- Helper: if s.holding p = some h, then (daStep s).holding p = some h' for some h'.
  have mono : ∀ h : Fin n, s.holding p = some h →
      ∃ h' : Fin n, (daStep w m s).holding p = some h' :=
    fun h hh => (holding_rank_mono_step w m s p hh).imp fun h' ⟨heq, _⟩ => heq
  by_cases hfi : isFree s i = true
  · -- Man i was free: nc increases by 1, hp : p ∈ take (nc+1) (prefs i).
    rw [daStep_nc_free hfi] at hp
    rcases lt_or_ge (s.nextChoice i) n with hnc_lt | h_ge
    · -- nc < n: take (nc+1) = take nc ++ [(prefs i)[nc]].
      rw [List.take_succ_eq_append_getElem (by rwa [(m.valid i).2])] at hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp_old | hp_eq
      · obtain ⟨h, hh⟩ := hj i p hp_old; exact mono h hh
      · -- p = (prefs i)[nc]: man i proposes to p this round.
        have hpt : propTarget m i (s.nextChoice i) = some p := by
          simp [propTarget, List.getElem?_eq_getElem (by rwa [(m.valid i).2]), hp_eq]
        exact daStep_held_of_free_prop w m s i p hfi hpt
    · -- nc ≥ n: take (nc+1) = take nc = prefs i (since length = n).
      have heq_full : (m.prefs i).take (s.nextChoice i) = m.prefs i :=
        List.take_of_length_le (by rw [(m.valid i).2]; exact h_ge)
      have hmem_take : p ∈ (m.prefs i).take (s.nextChoice i) := by
        rw [heq_full]
        rw [List.take_of_length_le (by rw [(m.valid i).2]; omega)] at hp
        exact hp
      obtain ⟨h, hh⟩ := hj i p hmem_take; exact mono h hh
  · -- Man i was not free: nc unchanged.
    simp only [Bool.not_eq_true] at hfi
    rw [daStep_nc_held hfi] at hp
    obtain ⟨h, hh⟩ := hj i p hp; exact mono h hh

/-- `JInv` over `daRun`. -/
private lemma jinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n) (hj : JInv m s) :
    JInv m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero   => exact hj
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (jinv_step w m s hj)
      · exact hj

/-- `nextChoice i ≥ n` + injectivity + `JInv` → man `i` is not free. -/
private lemma not_free_of_nc_ge (m : Preferences n) (s : DAState n) (i : Fin n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (hnc : n ≤ s.nextChoice i) :
    isFree s i = false := by
  rw [not_isFree_iff]
  have hall : ∀ j : Fin n, ∃ h, s.holding j = some h := by
    intro j
    apply hj i j
    have hmem : j ∈ m.prefs i := pref_list_mem _ (m.valid i).1 (m.valid i).2 j
    rw [List.take_of_length_le (by rw [(m.valid i).2]; exact hnc)]
    exact hmem
  -- The function j ↦ (hall j).choose is injective (by holding injectivity),
  -- hence surjective on the finite type Fin n.
  let f : Fin n → Fin n := fun j => (hall j).choose
  have hfinj : Function.Injective f := by
    intro j1 j2 heq
    exact hinj j1 j2 (hall j1).choose (hall j1).choose_spec
      (show s.holding j2 = some (f j1) from heq ▸ (hall j2).choose_spec)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  obtain ⟨j, rfl⟩ := hfsurj i
  exact ⟨j, (hall j).choose_spec⟩

/-- `nextChoice i ≤ n` for `daStep`. -/
private lemma daStep_nc_le_n (w m : Preferences n) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (i : Fin n) : (daStep w m s).nextChoice i ≤ n := by
  by_cases hfi : isFree s i = true
  · rw [daStep_nc_free hfi]
    by_contra h_gt; push_neg at h_gt
    exact absurd (not_free_of_nc_ge m s i hj hinj (by omega)) (by simp [hfi])
  · rw [daStep_nc_held (by simpa using hfi)]; exact hnc0 i

/-- `nextChoice i ≤ n` over `daRun`. -/
private lemma nc_le_n_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (i : Fin n) : (daRun w m fuel s).nextChoice i ≤ n := by
  induction fuel generalizing s with
  | zero   => exact hnc0 i
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (daStep_nc_le_n w m s hnc0 hj hinj) (jinv_step w m s hj)
            (holding_injective_step w m s hinj)
      · exact hnc0 i

/-- `∑ nextChoice` strictly increases when free men exist. -/
private lemma nc_sum_increase (w m : Preferences n) (s : DAState n)
    (hne : (freeMenSet s).Nonempty) :
    ∑ i : Fin n, s.nextChoice i < ∑ i : Fin n, (daStep w m s).nextChoice i := by
  obtain ⟨i0, hi0⟩ := hne
  rw [mem_freeMenSet] at hi0
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hfi : isFree s i = true
    · simp [daStep_nc_free hfi]
    · simp [daStep_nc_held (by simpa using hfi)]
  · exact ⟨i0, Finset.mem_univ _, by simp [daStep_nc_free hi0]⟩

/-- `∑ nextChoice ≤ n * n` is preserved over `daRun`. -/
private lemma nc_sum_le_nn (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (hsum0 : ∑ i : Fin n, s.nextChoice i ≤ n * n) :
    ∑ i : Fin n, (daRun w m fuel s).nextChoice i ≤ n * n := by
  induction fuel generalizing s with
  | zero   => exact hsum0
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · apply ih _ (daStep_nc_le_n w m s hnc0 hj hinj) (jinv_step w m s hj)
            (holding_injective_step w m s hinj)
        calc ∑ i : Fin n, (daStep w m s).nextChoice i
            ≤ ∑ _i : Fin n, n :=
              Finset.sum_le_sum (fun i _ => daStep_nc_le_n w m s hnc0 hj hinj i)
          _ = n * n := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
      · exact hsum0

/-- After `fuel` rounds ending with free men, `∑ nextChoice` grew by ≥ `fuel`. -/
private lemma nc_sum_grows (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hnc0 : ∀ i : Fin n, s.nextChoice i ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2)
    (hne_end : (freeMenSet (daRun w m fuel s)).Nonempty) :
    ∑ i : Fin n, s.nextChoice i + fuel ≤ ∑ i : Fin n, (daRun w m fuel s).nextChoice i := by
  induction fuel generalizing s with
  | zero => simp [daRun]
  | succ k ih =>
      simp only [daRun]
      split_ifs with hne_s
      · -- this round was active
        have hsum_inc := nc_sum_increase w m s hne_s
        -- freeMenSet after k more rounds of daStep s is nonempty
        have hne_k : (freeMenSet (daRun w m k (daStep w m s))).Nonempty := by
          simp only [daRun] at hne_end; simpa [hne_s] using hne_end
        have hih := ih _ (daStep_nc_le_n w m s hnc0 hj hinj) (jinv_step w m s hj)
            (holding_injective_step w m s hinj) hne_k
        linarith
      · -- freeMenSet s = ∅: daRun (k+1) s = s
        simp only [Finset.not_nonempty_iff_eq_empty] at hne_s
        simp only [daRun, hne_s, Finset.not_nonempty_iff_eq_empty, ↓reduceIte] at hne_end
        exact absurd hne_s (Finset.nonempty_iff_ne_empty.mp hne_end)

/-! #### Proposal rank bound: the core of Roth-Sotomayor -/

/-- When free man `j` proposes to woman `i` in `daStep`, the resulting hold has rank ≤ j. -/
private lemma proposal_rank_bound (w m : Preferences n) (s : DAState n) (j i : Fin n)
    (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i) :
    ∃ h : Fin n, (daStep w m s).holding i = some h ∧
      (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j := by
  -- j is in proposerList i
  have hj_in : j ∈ (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some i))).val.toList :=
    Multiset.mem_toList.mpr (Finset.mem_val.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hfj, hpt]⟩))
  set pl := (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some i))).val.toList with hpl_def
  have hne_pl : pl ≠ [] := List.ne_nil_of_mem hj_in
  -- argmin returns some q with rank ≤ j's rank
  have hbn : ∃ q : Fin n, pl.argmin (fun k => (w.prefs i).idxOf k) = some q :=
    (Option.ne_none_iff_exists.mp (List.argmin_eq_none.not.mpr hne_pl)).imp
      (fun _ h => h.symm)
  obtain ⟨q, hq⟩ := hbn
  have hq_le : (w.prefs i).idxOf q ≤ (w.prefs i).idxOf j :=
    List.le_of_mem_argmin hj_in (show q ∈ pl.argmin (fun k => (w.prefs i).idxOf k) from hq)
  -- daStep holding i = some h with rank ≤ q ≤ j
  simp only [daStep, ← hpl_def]
  cases hs : s.holding i with
  | none =>
      simp only [hs, hq]
      exact ⟨q, rfl, hq_le⟩
  | some h =>
      simp only [hs, hq]
      split_ifs with hlt
      · exact ⟨q, rfl, hq_le⟩
      · exact ⟨h, rfl, Nat.le_trans (Nat.le_of_not_lt hlt) hq_le⟩

/-- Over a daRun, if man j proposed to woman i at the first step, woman i's final partner
    has rank ≤ j's rank in w.prefs i. -/
private lemma proposal_rank_bound_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (j i : Fin n) (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i) :
    ∃ h : Fin n, (daRun w m fuel (daStep w m s)).holding i = some h ∧
      (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j := by
  obtain ⟨h0, hh0, hrk0⟩ := proposal_rank_bound w m s j i hfj hpt
  obtain ⟨h1, hh1, hrk1⟩ := holding_rank_mono_run w m fuel (daStep w m s) i hh0
  exact ⟨h1, hh1, Nat.le_trans hrk1 hrk0⟩

/-- At termination: if man j proposed to woman i at some round (j was free, i was his nc-th
    choice at state s, and the rest of the run reaches finalState), woman i's final partner has
    rank ≤ j in w.prefs i. -/
private lemma finalState_rank_bound (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (j i : Fin n) (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i)
    (hrun : daRun w m fuel (daStep w m s) = finalState w m) :
    (w.prefs i).idxOf (gs w m i) ≤ (w.prefs i).idxOf j := by
  obtain ⟨h, hh, hrk⟩ := proposal_rank_bound_run w m fuel s j i hfj hpt
  rw [hrun] at hh
  -- gs w m i = h (woman i holds man h at termination)
  have hgs : gs w m i = h := by
    simp only [gs, finalState]
    rw [show (daRun w m (n * n + 1) (initState n)).holding i = some h from hh]; simp
  rw [hgs]; exact hrk

/-! #### Roth–Sotomayor rank invariant -/

/-- **RSInv** (the deferred-acceptance rank invariant — the engine of the
stability proof): for every man `j` and every woman `i` that `j` has already
proposed to, `i` currently holds *some* man whom she prefers at least as much
as `j`.

Formally: for every `i ∈ (m.prefs j).take (s.nextChoice j)` (the prefix of
`j`'s preference list `j` has cycled through), there exists `h` such that
`s.holding i = some h` **and** `(w.prefs i).idxOf h ≤ (w.prefs i).idxOf j`
(smaller index = higher preference).

Why this is the stability lever: at termination, if `(i, j)` *were* a blocking
pair — `i` and `j` mutually prefer each other to their final partners — then
`j` would have proposed to `i` at some point, so `RSInv` at termination would
say `i` holds someone she likes at least as much as `j`. That someone is `i`'s
eventual partner (by `holding_rank_mono_run`), giving `i` no incentive to
defect. Contradiction with the blocking-pair assumption.

The invariant is preserved by every `daStep` (`rsinv_step`) and trivially
holds at `initState` (`rsinv_init`); see also `rsinv_finalState` for the
terminal form used in the stability proof. -/
private def RSInv (w m : Preferences n) (s : DAState n) : Prop :=
  ∀ j i : Fin n, i ∈ (m.prefs j).take (s.nextChoice j) →
    ∃ h : Fin n, s.holding i = some h ∧ (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j

private lemma rsinv_init (w m : Preferences n) : RSInv w m (initState n) := by
  intro j i hi; simp [initState] at hi

/-- RSInv is preserved by one daStep. -/
private lemma rsinv_step (w m : Preferences n) (s : DAState n)
    (hrs : RSInv w m s)
    (hnc0 : ∀ k : Fin n, s.nextChoice k ≤ n) :
    RSInv w m (daStep w m s) := by
  intro j i hi
  by_cases hfj : isFree s j = true
  · rw [daStep_nc_free hfj] at hi
    rcases lt_or_ge (s.nextChoice j) n with hnc_lt | h_ge
    · -- nc < n: take (nc+1) = take nc ++ [proposal]
      rw [List.take_succ_eq_append_getElem (by rwa [(m.valid j).2])] at hi
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi_old | hi_eq
      · -- i was in the old take — rank already good; use rank_mono_step
        obtain ⟨h, hh, hrk⟩ := hrs j i hi_old
        obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
        exact ⟨h', hh', Nat.le_trans hrk' hrk⟩
      · -- i = (m.prefs j)[nc] = the new proposal; use proposal_rank_bound
        have hpt : propTarget m j (s.nextChoice j) = some i := by
          simp [propTarget, List.getElem?_eq_getElem (by rwa [(m.valid j).2]), hi_eq]
        exact proposal_rank_bound w m s j i hfj hpt
    · -- nc ≥ n: take (nc+1) = take nc = full list
      have hmem_take : i ∈ (m.prefs j).take (s.nextChoice j) := by
        rw [List.take_of_length_le (by rw [(m.valid j).2]; exact h_ge)]
        rw [List.take_of_length_le (by rw [(m.valid j).2]; omega)] at hi; exact hi
      obtain ⟨h, hh, hrk⟩ := hrs j i hmem_take
      obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
      exact ⟨h', hh', Nat.le_trans hrk' hrk⟩
  · -- j not free: nc unchanged
    simp only [Bool.not_eq_true] at hfj
    rw [daStep_nc_held hfj] at hi
    obtain ⟨h, hh, hrk⟩ := hrs j i hi
    obtain ⟨h', hh', hrk'⟩ := holding_rank_mono_step w m s i hh
    exact ⟨h', hh', Nat.le_trans hrk' hrk⟩

/-- RSInv over daRun. -/
private lemma rsinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hrs : RSInv w m s)
    (hnc0 : ∀ k : Fin n, s.nextChoice k ≤ n)
    (hj : JInv m s)
    (hinj : ∀ j1 j2 k : Fin n, s.holding j1 = some k → s.holding j2 = some k → j1 = j2) :
    RSInv w m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hrs
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · apply ih
        · exact rsinv_step w m s hrs hnc0
        · exact daStep_nc_le_n w m s hnc0 hj hinj
        · exact jinv_step w m s hj
        · exact holding_injective_step w m s hinj
      · exact hrs

/-- **HoldInv** (Held → Proposed): if woman `p` currently holds man `j`, then
`j` must already have proposed to `p` — i.e., `p` is in the proposed-prefix
`(m.prefs j).take (s.nextChoice j)` of `j`'s preference list.

This is the **converse direction** of [`JInv`]: `JInv` says proposed ⇒ held;
`HoldInv` says held ⇒ proposed. Together they make the two-sided
correspondence between cursors and holdings airtight.

`HoldInv` is the one the stability proof's "the holder must be at least as
preferred as the blocker" step relies on, via `RSInv` — see the proof sketch
of [`galeShapley_isStable`] and the preservation lemma [`holdinv_step`]. -/
def HoldInv (m : Preferences n) (s : DAState n) : Prop :=
  ∀ j p : Fin n, s.holding p = some j → p ∈ (m.prefs j).take (s.nextChoice j)

lemma holdinv_init (m : Preferences n) : HoldInv m (initState n) := by
  intro j p hp; simp [initState] at hp

/-- `HoldInv` is preserved by one DA step.

Proof structure: case-analyze on the pair `(s.holding p, bestNew p)` that
drives `daStep`'s decision for woman `p`. There are four cases, two of
which (`old hold preserved` and `new free-man wins`) recur in mirrored
form depending on whether `s.holding p` was `some h` or `none`. We
extract those two arguments into the local helpers `preserve_hold` and
`new_hold` and dispatch each of the four cases with a single line.

Throughout, the key external lemmas are:

* `pl_free_props` — anyone in `proposerList p` was free and proposed to `p`.
* `daStep_nc_free` / `daStep_nc_held` — `nextChoice j` advances by 1 if `j`
  was free, stays put otherwise.
* `not_isFree_iff` — `j` is not free in `s` iff some woman holds `j`. -/
lemma holdinv_step (w m : Preferences n) (s : DAState n)
    (hhold : HoldInv m s) : HoldInv m (daStep w m s) := by
  intro j p hp
  -- Fold `(daStep w m s).holding p` to the canonical `match` form (see
  -- `daStep_holding`). This is what lets us name `pl` / `bn` afterwards
  -- without losing the connection to `hp`.
  rw [daStep_holding] at hp
  -- Names matching the inner `let`s of `daStep`.
  set pl : Fin n → List (Fin n) := fun p' =>
    (Finset.univ.filter (fun k : Fin n =>
      isFree s k && (propTarget m k (s.nextChoice k) == some p'))).val.toList with pl_def
  set bn : Fin n → Option (Fin n) := fun p' =>
    (pl p').argmin (fun k => (w.prefs p').idxOf k) with bn_def
  -- `(s.holding p, bn p)` is exactly what `daStep_holding` matches on.
  change (match s.holding p, bn p with
    | none,   none   => none
    | some h, none   => some h
    | none,   some q => some q
    | some h, some q =>
        if (w.prefs p).idxOf q < (w.prefs p).idxOf h then some q else some h) = some j at hp
  ----------------------------------------------------------------------------
  -- Reusable closer 1: woman `p`'s old hold `h` survives the step (because
  -- no new proposer outranks him). Then `h = j` and `j`'s cursor doesn't
  -- advance (since `j` is not free in `s` — woman `p` holds him).
  ----------------------------------------------------------------------------
  have preserve_hold : ∀ {h : Fin n}, h = j → s.holding p = some h →
      p ∈ (m.prefs j).take ((daStep w m s).nextChoice j) := by
    rintro h rfl hs
    -- `rfl` here substitutes `j := h`, so the conclusion is in terms of `h`.
    have hh_not_free : isFree s h = false := (not_isFree_iff s h).mpr ⟨p, hs⟩
    rw [daStep_nc_held hh_not_free]
    exact hhold h p hs
  ----------------------------------------------------------------------------
  -- Reusable closer 2: a free man `q ∈ proposerList p` becomes (or is) `p`'s
  -- holder. Then `q = j`, his cursor advances by 1 in `daStep`, and `p` sits
  -- at index `s.nextChoice q` of `m.prefs q` — so `p` is now within the
  -- *new* `take` window.
  ----------------------------------------------------------------------------
  have new_hold : ∀ {q : Fin n}, q = j → q ∈ pl p →
      p ∈ (m.prefs j).take ((daStep w m s).nextChoice j) := by
    rintro q rfl hq_in
    -- Substitution: `j := q`. Conclusion is in terms of `q`.
    have ⟨hfq, hptq⟩ := pl_free_props s m p q hq_in
    -- `propTarget m q (s.nextChoice q) = some p`, i.e.
    -- `(m.prefs q)[s.nextChoice q]? = some p`. Unpack via `getElem?_eq_some_iff`.
    obtain ⟨hq_lt_len, hget⟩ : ∃ h, (m.prefs q)[s.nextChoice q]'h = p :=
      List.getElem?_eq_some_iff.mp hptq
    -- After the step, `q`'s cursor is `s.nextChoice q + 1`; `p` sits at index
    -- `s.nextChoice q < s.nextChoice q + 1`, so `p` is inside the new prefix.
    rw [daStep_nc_free hfq, List.mem_take_iff_idxOf_lt]
    · -- `(m.prefs q).idxOf p < s.nextChoice q + 1`
      rw [← hget, (m.valid q).1.idxOf_getElem _ hq_lt_len]
      omega
    · exact pref_list_mem _ (m.valid q).1 (m.valid q).2 p
  ----------------------------------------------------------------------------
  -- Main case split — four cases, each one liner.
  ----------------------------------------------------------------------------
  cases hs : s.holding p with
  | none =>
      cases hb : bn p with
      | none =>
          -- (none, none): match returns `none`, contradicting `hp : … = some j`.
          rw [hs, hb] at hp; exact absurd hp (by simp)
      | some q =>
          -- (none, some q): new proposer `q` takes the slot; `q = j`.
          rw [hs, hb] at hp
          exact new_hold (Option.some.inj hp) (List.argmin_mem hb)
  | some h =>
      cases hb : bn p with
      | none =>
          -- (some h, none): old hold kept; `h = j`.
          rw [hs, hb] at hp
          exact preserve_hold (Option.some.inj hp) hs
      | some q =>
          -- (some h, some q): outcome depends on whether `q` outranks `h`.
          rw [hs, hb] at hp
          -- The match reduces definitionally to an `if`; force the reduction so
          -- `split_ifs` can see the conditional.
          dsimp only at hp
          split_ifs at hp with hlt
          · -- `q` upgrades: same as Case 2 above.
            exact new_hold (Option.some.inj hp) (List.argmin_mem hb)
          · -- `h` stays: same as Case 3 above.
            exact preserve_hold (Option.some.inj hp) hs

private lemma holdinv_run (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (hh : HoldInv m s) : HoldInv m (daRun w m fuel s) := by
  induction fuel generalizing s with
  | zero => exact hh
  | succ k ih =>
      simp only [daRun]; split_ifs with hne
      · exact ih _ (holdinv_step w m s hh)
      · exact hh

lemma holdinv_finalState (w m : Preferences n) :
    HoldInv m (finalState w m) :=
  holdinv_run w m (n * n + 1) (initState n) (holdinv_init m)

/-- RSInv at finalState. -/
private lemma rsinv_finalState (w m : Preferences n) :
    RSInv w m (finalState w m) := by
  apply rsinv_run w m (n * n + 1) (initState n) (rsinv_init w m)
  · simp [initState]
  · exact jinv_init m
  · exact initState_injective (n := n)

/-- If j strictly prefers i over his final partner, i's final partner has rank ≤ j. -/
private lemma rsinv_stability (w m : Preferences n) (j i : Fin n)
    (hlt : (m.prefs j).idxOf i < (finalState w m).nextChoice j) :
    (w.prefs i).idxOf (gs w m i) ≤ (w.prefs i).idxOf j := by
  have hrs := rsinv_finalState w m j i
  have hi_mem : i ∈ (m.prefs j).take ((finalState w m).nextChoice j) := by
    rw [List.mem_take_iff_idxOf_lt]
    · exact hlt
    · exact pref_list_mem _ (m.valid j).1 (m.valid j).2 i
  obtain ⟨h, hh, hrk⟩ := hrs hi_mem
  -- h = gs w m i (since holding i = some h at finalState)
  have hgs : gs w m i = h := by
    simp only [gs, finalState] at hh ⊢; simp [hh]
  rw [hgs]; exact hrk

end GS_Fuel

section GS_Correctness

open GS

variable {n : ℕ} [NeZero n]
variable (w m : Preferences n)

/-! #### Invariant 1: `holding` rank monotonically improves -/

/-! #### Invariant 3: termination -/

/-- At termination, every man is held (no free man remains).
    Proof: if a free man remained, `nc_sum_grows` would give `n*n + 1 ≤ n*n`, contradiction. -/
lemma finalState_no_free_men :
    ∀ i : Fin n, isFree (finalState w m) i = false := by
  intro i
  -- Establish the pre-conditions for the fuel-sufficiency lemmas.
  have hnc0 : ∀ j : Fin n, (initState n).nextChoice j ≤ n := by simp [initState]
  have hj0 : JInv m (initState n) := jinv_init m
  have hinj0 := initState_injective (n := n)
  -- By contradiction: suppose some man i is still free in finalState.
  by_contra hfree
  simp only [Bool.not_eq_false] at hfree
  -- freeMenSet (finalState w m) is nonempty.
  have hne : (freeMenSet (finalState w m)).Nonempty :=
    ⟨i, mem_freeMenSet.mpr hfree⟩
  -- nc_sum_grows: 0 + (n*n+1) ≤ ∑ nc at finalState.
  have hgrows := nc_sum_grows w m (n * n + 1) (initState n) hnc0 hj0 hinj0 hne
  simp only [initState, Finset.sum_const_zero] at hgrows
  -- nc_sum_le_nn: ∑ nc at finalState ≤ n*n.
  have hle := nc_sum_le_nn w m (n * n + 1) (initState n) hnc0 hj0 hinj0
    (by simp [initState])
  -- Contradiction: n*n+1 ≤ 0 + (n*n+1) ≤ ∑ nc ≤ n*n.
  simp only [initState] at hle
  omega

/-! #### Total matching -/

/-- At termination, every man is held by some woman. -/
lemma final_all_men_held :
    ∀ i : Fin n, ∃ j : Fin n, (finalState w m).holding j = some i := by
  intro i; exact (not_isFree_iff _ _).mp (finalState_no_free_men w m i)

/-- `finalState` holding is injective. -/
lemma final_holding_injective :
    ∀ j1 j2 : Fin n, ∀ i : Fin n,
      (finalState w m).holding j1 = some i → (finalState w m).holding j2 = some i → j1 = j2 :=
  holding_injective_run w m (n * n + 1) (initState n) (initState_injective (n := n))

/-- At termination, every woman holds some man. -/
lemma final_all_women_hold :
    ∀ j : Fin n, ∃ i : Fin n, (finalState w m).holding j = some i := by
  intro j
  by_contra hnone
  push_neg at hnone
  -- j holds nobody, but every man is held by some woman ≠ j (pigeon-hole).
  have hall := final_all_men_held w m
  have hinj := final_holding_injective w m
  have hf : ∀ i : Fin n, ∃ j' : Fin n, j' ≠ j ∧ (finalState w m).holding j' = some i := by
    intro i
    obtain ⟨j', hj'⟩ := hall i
    exact ⟨j', fun heq => absurd (heq ▸ hj') (hnone i), hj'⟩
  -- Inject Fin n → (univ \ {j}) of size n-1 → contradiction.
  let f : Fin n → (Finset.univ.erase j : Finset (Fin n)) := fun i =>
    ⟨(hf i).choose, Finset.mem_erase.mpr ⟨(hf i).choose_spec.1, Finset.mem_univ _⟩⟩
  have hfinj : Function.Injective f := by
    intro i1 i2 heq
    have h1 : (finalState w m).holding ((hf i1).choose) = some i1 := (hf i1).choose_spec.2
    have h2 : (finalState w m).holding ((hf i2).choose) = some i2 := (hf i2).choose_spec.2
    have hv : (hf i1).choose = (hf i2).choose := congrArg Subtype.val heq
    rw [hv] at h1
    exact Option.some.inj (h1.symm.trans h2)
  have hcard : (Finset.univ.erase j : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have : Fintype.card (Fin n) ≤ Fintype.card ↥(Finset.univ.erase j : Finset (Fin n)) :=
    Fintype.card_le_of_injective _ hfinj
  rw [Fintype.card_coe, hcard, Fintype.card_fin] at this
  exact absurd this (by have hpos := NeZero.pos n; omega)

/-! #### Bijectivity -/

/-- `gs w m` is injective. -/
lemma gs_injective : Function.Injective (gs w m) := by
  intro j1 j2 heq
  simp only [gs] at heq
  obtain ⟨i1, hi1⟩ := final_all_women_hold w m j1
  obtain ⟨i2, hi2⟩ := final_all_women_hold w m j2
  simp [hi1, hi2] at heq; subst heq
  exact final_holding_injective w m j1 j2 i1 hi1 hi2

/-- `gs w m` is a bijection on `Fin n`. -/
lemma gs_bijective : Function.Bijective (gs w m) :=
  Finite.injective_iff_bijective.mp (gs_injective w m)

/-! #### Stability -/

-- Sanity-check example: the n=3 counterexample from the old algorithm should give
-- the standard DA stable matching a-B(1), b-A(0), c-C(2).
--
-- men:   A=0: a>b>c (0>1>2),  B=1: b>a>c (1>0>2),  C=2: a>b>c (0>1>2)
-- women: a=0: B>C>A (1>2>0),  b=1: A>C>B (0>2>1),  c=2: A>B>C (0>1>2)
-- Expected stable: a holds B(1), b holds A(0), c holds C(2).
--
-- `finalState` is `noncomputable` (uses classical choice via `argmin`), so
-- `#eval` is not available.  A `native_decide`-based checker can be added once
-- a computable version is provided (future work).
-- #eval (GS.finalState wPrefs3 mPrefs3).holding 0  -- expected: some 1

/-- **Gale-Shapley stability**: the DA output has no blocking pair.

    The statement is in the *market* frame (`IsBlocking … (i : M) (j : W)`). But
    `MatchingMarket.ofEquivData w m` **transposes the two sides** (see its
    docstring), so the market-`M` index `i` is an algorithm *woman* and the
    market-`W` index `j` is an algorithm *man*. The proof therefore reads in the
    algorithm frame — `i` a woman, `j` a man — matching the inline comments.

    Proof (standard deferred acceptance): suppose `(i, j)` blocks. In algorithm
    terms man `j` strictly prefers woman `i` to his wife, so `j` proposed to `i`
    at some round: his wife is in his proposed-prefix (`holdinv_finalState`) and
    `i` is ranked at least as early (`hprefJ`). Then `rsinv_stability` (`RSInv`)
    gives that at termination woman `i` holds a man she ranks at least as high as
    `j`, so she does *not* strictly prefer `j` to her partner — contradicting the
    blocking assumption. -/
theorem galeShapley_isStable :
    Matching.IsStable (MatchingMarket.ofEquivData w m)
                      (Matching.ofGS (gs w m) (gs_bijective w m)) := by
  intro i j
  simp only [Matching.IsBlocking, Matching.ofGS, MatchingMarket.ofEquivData, strict, not_and]
  intro hprefI hprefJ
  -- After the simp+intros, the context is:
  --   hprefI : woman i strictly prefers man j to her current husband gs w m i
  --     (= idxOf j (w.prefs i) ≤ idxOf (gs w m i) ∧ ¬ converse)
  --   hprefJ : man j weakly prefers woman i to his current wife (gs w m).symm j
  --     (the "≤" half of strict; the "¬ ≤" half is the goal to refute, i.e. the
  --      goal is `¬¬ idxOf (gs w m).symm j ≤ idxOf i`, equivalent to `≤`).
  -- Strategy (Roth–Sotomayor): show woman i is in j's already-proposed prefix, so
  -- by `rsinv_stability` she'd already be holding someone she prefers at least as
  -- much as j — contradicting `hprefI`'s strict preference for j over her husband.
  obtain ⟨_, hI_strict⟩ := hprefI
  rw [not_le] at hI_strict
  -- hI_strict : idxOf j (w.prefs i) < idxOf (gs w m i) (w.prefs i)
  -- Step 1. Identify j's wife — the woman matched with j by `gs`.
  set wife : Fin n := (Equiv.ofBijective (gs w m) (gs_bijective w m)).symm j with wife_def
  have hwife_apply : gs w m wife = j :=
    (Equiv.ofBijective (gs w m) (gs_bijective w m)).apply_symm_apply j
  -- Step 2. `wife` actually holds `j` in `finalState` — follow `gs`'s definition.
  have hwife_holds : (finalState w m).holding wife = some j := by
    obtain ⟨h, hh⟩ := final_all_women_hold w m wife
    have hgs : gs w m wife = h := by simp [gs, hh]
    rw [hgs] at hwife_apply
    exact hwife_apply ▸ hh
  -- Step 3. By `HoldInv` at `finalState`, the wife is in j's already-proposed prefix.
  have hwife_in : wife ∈ (m.prefs j).take ((finalState w m).nextChoice j) :=
    holdinv_finalState w m j wife hwife_holds
  have hj_prefs_mem : ∀ x : Fin n, x ∈ m.prefs j :=
    pref_list_mem _ (m.valid j).1 (m.valid j).2
  have hwife_lt : (m.prefs j).idxOf wife < (finalState w m).nextChoice j :=
    (List.mem_take_iff_idxOf_lt (hj_prefs_mem wife)).mp hwife_in
  -- Step 4. By `hprefJ` (j weakly prefers i to wife), `i` is at least as early as
  -- wife in `m.prefs j`, so also in the proposed prefix.
  have hi_lt : (m.prefs j).idxOf i < (finalState w m).nextChoice j :=
    lt_of_le_of_lt hprefJ hwife_lt
  -- Step 5. `rsinv_stability` then says i's husband is *at least* as preferred
  -- (by i) as j — directly contradicting i's strict preference for j.
  exact absurd (rsinv_stability w m j i hi_lt) (not_le.mpr hI_strict)

end GS_Correctness
