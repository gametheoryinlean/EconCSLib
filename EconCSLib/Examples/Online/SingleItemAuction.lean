/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Algorithm.Online
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Prod.Lex

/-!
# Online Single-Item (Posted-Price) Auction

The **online single-item auction** sells one indivisible good to bidders
who arrive one at a time. At each step the system receives two pieces of
information: the bidder's **identity** `b : B` and their **value** `v : F`.
The auctioneer posts a lexicographic threshold in `WithTop (Lex (F × B))`.
A bidder with value `v` and identity `b` is accepted when the threshold
`t` satisfies `t ≤ toLex (v, b)`; when `t = ⊤` the bidder is rejected
unconditionally.

The threshold sees the full history of rejected `(identity, value)` pairs;
the "no future" constraint of online algorithms is built into the type.

## Main definitions

* `SingleItemAuction B F` — a threshold rule for lexicographic acceptance.
* `welfare` — social welfare under a given arrival sequence.
* `utility` — quasi-linear utility of a specific bidder.
* `SampleThenThreshold.auction` — the sample-then-threshold pricing rule.

## Main results

* `dsic` — truthful bidding is weakly dominant for every bidder (Problem 2.1(a)).
* `welfare_can_be_zero` — any auction with positive opening threshold can be
  forced to welfare `0` (Problem 2.1(b)).
* `SampleThenThreshold.competitive` — the sample-then-threshold rule is
  1/4-competitive under uniformly random arrival for injective identities
  (Problem 2.1(c)).
-/

set_option linter.unusedSectionVars false

namespace Online.Auction

open Online Function

variable {B F : Type*}

/-- State of an online single-item auction.

* `.unsold history` — item still available; `history` lists prior
  rejected `(identity, value)` pairs in arrival order.
* `.sold winner price` — item sold at posted price `price` to the bidder
  at position `winner` (zero-indexed). -/
inductive AuctionState (B F : Type*) where
  | unsold (history : List (B × F))
  | sold (winner : ℕ) (price : F)

/-- An online single-item auction is a *threshold rule*. Given the history
of rejected `(identity, value)` pairs, it posts a lexicographic threshold
in `WithTop (Lex (F × B))`. The threshold `⊤` rejects unconditionally;
`↑(toLex (p, b))` accepts when `p < v_i ∨ (p = v_i ∧ b ≤ b_i)`. -/
@[ext]
structure SingleItemAuction (B F : Type*) where
  threshold : List (B × F) → WithTop (Lex (F × B))

/-- Maximum of a valuation profile over `Fin n`. -/
noncomputable def maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) : F :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ v

lemma le_maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) (i : Fin n) :
    v i ≤ maxV hn v :=
  Finset.le_sup' v (Finset.mem_univ i)

namespace SingleItemAuction

variable [LinearOrder F] [LinearOrder B] (A : SingleItemAuction B F)

/-- The auction as an `OnlineAlgorithm`. Each step receives an
`Option (B × F)` input — `some (bi, vi)` for a genuine bidder,
`none` for end-of-input. Output on sale is the posted price.
Acceptance is lexicographic: accept when the threshold `t` satisfies
`t ≤ toLex (v_i, b_i)`. -/
def online : OnlineAlgorithm (B × F) (AuctionState B F) F where
  init := .unsold []
  step
    | .unsold h, some (bi, vi) =>
        match A.threshold h with
        | none   => (.unsold (h ++ [(bi, vi)]), none)
        | some t =>
            if t ≤ toLex (vi, bi)
            then (.sold h.length (ofLex t).1, some (ofLex t).1)
            else (.unsold (h ++ [(bi, vi)]), none)
    | .unsold h, none => (.unsold h, none)
    | .sold w p, _    => (.sold w p, none)

/-- Run the auction on an input sequence, returning the sale price. -/
def run (inputs : List (B × F)) : Option F :=
  (A.online.run A.online.init inputs).2

/-! ### Welfare -/

/-- Welfare helper: process bidders from index `k` onward with
accumulated rejection history `h`. Returns the value of the first
bidder whose `(value, identity)` pair clears the threshold
(lexicographically), or `0`. -/
def welfareAux [Zero F]
    (threshold : List (B × F) → WithTop (Lex (F × B)))
    {n : ℕ} (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) : F :=
  if hk : k < n then
    let entry := f ⟨k, hk⟩
    if (threshold h : WithTop (Lex (F × B))) ≤ ↑(toLex (entry.2, entry.1))
    then entry.2
    else welfareAux threshold f (h ++ [entry]) (k + 1)
  else 0
termination_by n - k

/-- Social welfare: the value of the winning bidder (or `0`) under
arrival sequence `f : Fin n → B × F`. -/
def welfare [Zero F] {n : ℕ} (f : Fin n → B × F) : F :=
  welfareAux A.threshold f [] 0

@[simp] lemma welfareAux_done [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : ¬ k < n) :
    welfareAux A.threshold f h k = 0 := by
  rw [welfareAux, dif_neg hk]

lemma welfareAux_accept [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : k < n)
    (hacc : (A.threshold h : WithTop (Lex (F × B))) ≤
            ↑(toLex ((f ⟨k, hk⟩).2, (f ⟨k, hk⟩).1))) :
    welfareAux A.threshold f h k = (f ⟨k, hk⟩).2 := by
  rw [welfareAux, dif_pos hk]
  simp only
  rw [if_pos hacc]

lemma welfareAux_reject [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : k < n)
    (hrej : ¬ ((A.threshold h : WithTop (Lex (F × B))) ≤
               ↑(toLex ((f ⟨k, hk⟩).2, (f ⟨k, hk⟩).1)))) :
    welfareAux A.threshold f h k =
      welfareAux A.threshold f (h ++ [f ⟨k, hk⟩]) (k + 1) := by
  rw [welfareAux, dif_pos hk]
  simp only
  rw [if_neg hrej]

lemma welfareAux_nonneg [Zero F] {n : ℕ}
    (f : Fin n → B × F) (hf : ∀ i, 0 ≤ (f i).2)
    (h : List (B × F)) (k : ℕ) :
    0 ≤ welfareAux A.threshold f h k := by
  by_cases hk : k < n
  · have hacc_or :
        ((A.threshold h : WithTop (Lex (F × B))) ≤
         ↑(toLex ((f ⟨k, hk⟩).2, (f ⟨k, hk⟩).1))) ∨
        ¬ ((A.threshold h : WithTop (Lex (F × B))) ≤
           ↑(toLex ((f ⟨k, hk⟩).2, (f ⟨k, hk⟩).1))) :=
      em _
    rcases hacc_or with hacc | hrej
    · rw [A.welfareAux_accept f h k hk hacc]; exact hf ⟨k, hk⟩
    · rw [A.welfareAux_reject f h k hk hrej]
      exact welfareAux_nonneg f hf _ (k + 1)
  · simp [A.welfareAux_done f h k hk]
termination_by n - k

/-! ### Utility and DSIC -/

/-- The state immediately *before* bidder `i` is processed: the auction
state reached by running only the first `i` arrivals. -/
def stateBeforeStep {n : ℕ} (f : Fin n → B × F) (i : Fin n) :
    AuctionState B F :=
  A.online.runStatus (.unsold [])
    (List.ofFn (fun j : Fin i.val => f ⟨j.val, j.isLt.trans i.isLt⟩))

/-- Utility of bidder `i` with true valuation `v i` under arrival `f`.
When `f i = (bi, bidi)`, the bid is `bidi` (which may differ from `v i`). -/
def utility [Zero F] [Sub F] {n : ℕ} (f : Fin n → B × F) (v : Fin n → F) (i : Fin n) :
    F :=
  match A.stateBeforeStep f i with
  | .unsold h =>
      match A.threshold h with
      | none   => 0
      | some t =>
          if (ofLex t).1 < (f i).2 ∨ ((ofLex t).1 = (f i).2 ∧ (ofLex t).2 ≤ (f i).1)
          then v i - (ofLex t).1
          else 0
  | .sold _ _ => 0

/-! #### (a) DSIC: truthful bidding is weakly dominant -/

/-- The state before bidder `i` is independent of bidder `i`'s entry. -/
lemma stateBeforeStep_update_self {n : ℕ}
    (f : Fin n → B × F) (i : Fin n) (x : B × F) :
    A.stateBeforeStep (update f i x) i = A.stateBeforeStep f i := by
  have hfun :
      (fun j : Fin i.val =>
        update f i x ⟨j.val, j.isLt.trans i.isLt⟩) =
      (fun j : Fin i.val =>
        f ⟨j.val, j.isLt.trans i.isLt⟩) := by
    funext j
    apply update_of_ne
    intro heq
    exact absurd (congrArg Fin.val heq) (Nat.ne_of_lt j.isLt)
  unfold stateBeforeStep
  rw [hfun]

/-- At a fixed price, with a fixed tie-breaking condition, truthful
bidding weakly dominates any other bid. -/
private lemma local_dsic [Ring F] [IsStrictOrderedRing F]
    (p v bid : F) (tie_ok : Prop) [Decidable tie_ok] :
    (if (p < bid ∨ (p = bid ∧ tie_ok)) then v - p else 0) ≤
    (if (p < v ∨ (p = v ∧ tie_ok)) then v - p else 0) := by
  by_cases hpv : p < v ∨ (p = v ∧ tie_ok)
  · rw [if_pos hpv]
    by_cases hpb : p < bid ∨ (p = bid ∧ tie_ok)
    · rw [if_pos hpb]
    · rw [if_neg hpb]
      rcases hpv with hlt | ⟨heq, _⟩
      · exact sub_nonneg.mpr hlt.le
      · rw [heq, sub_self]
  · rw [if_neg hpv]
    by_cases hpb : p < bid ∨ (p = bid ∧ tie_ok)
    · rw [if_pos hpb]
      have hvp : v ≤ p := not_lt.mp (fun h => hpv (Or.inl h))
      exact sub_nonpos.mpr hvp
    · rw [if_neg hpb]

/-- **Problem 2.1 (a): the online single-item auction is DSIC.**

For every arrival sequence `f`, every true-valuation profile `v`, and
every bidder `i`, replacing bidder `i`'s entry with `((f i).1, v i)` —
keeping their identity, switching to truthful bidding — weakly improves
their utility. -/
theorem dsic [Ring F] [IsStrictOrderedRing F] {n : ℕ}
    (f : Fin n → B × F) (v : Fin n → F) (i : Fin n) :
    A.utility f v i ≤ A.utility (update f i ((f i).1, v i)) v i := by
  simp only [utility, A.stateBeforeStep_update_self, update_self]
  split
  · split
    · exact le_refl _
    · next t _ =>
        exact local_dsic (ofLex t).1 (v i) (f i).2 ((ofLex t).2 ≤ (f i).1)
  · exact le_refl _

/-! ### (b) No constant competitive ratio against adversarial input -/

/-- If all remaining bidders have value `0`, welfare from position `k`
onward is `0`. -/
private lemma welfareAux_all_zero [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ)
    (hzero : ∀ j : Fin n, k ≤ j.val → (f j).2 = 0) :
    welfareAux A.threshold f h k = 0 := by
  if hk : k < n then
    rw [welfareAux, dif_pos hk]
    simp only
    have hv : (f ⟨k, hk⟩).2 = 0 := hzero ⟨k, hk⟩ le_rfl
    by_cases hacc :
        (A.threshold h : WithTop (Lex (F × B))) ≤
        ↑(toLex ((f ⟨k, hk⟩).2, (f ⟨k, hk⟩).1))
    · rw [if_pos hacc, hv]
    · rw [if_neg hacc]
      exact welfareAux_all_zero f (h ++ [f ⟨k, hk⟩]) (k + 1) fun j hj => by
        exact hzero j (by omega)
  else
    rw [welfareAux, dif_neg hk]
termination_by n - k

/-- **Problem 2.1 (b).** Any auction whose opening threshold has positive
value component can be forced to welfare `0` while `max v > 0`. -/
theorem welfare_can_be_zero [Inhabited B] [Field F] [IsStrictOrderedRing F]
    (hn : 1 ≤ n)
    (hpos : ∀ (t : Lex (F × B)), A.threshold [] = ↑t → (0 : F) < (ofLex t).1) :
    ∃ f : Fin n → B × F,
      (0 : F) < maxV hn (fun i => (f i).2) ∧ A.welfare f = 0 := by
  have h0n : (0 : ℕ) < n := by omega
  rcases ht : A.threshold [] with _ | t
  · -- threshold = ⊤: bidder 0 has value 1 (rejected), rest 0
    let f : Fin n → B × F := fun i => (default, if i.val = 0 then 1 else 0)
    have hrej : ¬ ((A.threshold [] : WithTop (Lex (F × B))) ≤
        ↑(toLex ((f ⟨0, h0n⟩).2, (f ⟨0, h0n⟩).1))) := by
      rw [ht]
      exact not_le.mpr (WithTop.coe_lt_top _)
    refine ⟨f, ?_, ?_⟩
    · exact lt_of_lt_of_le one_pos (le_maxV hn (fun i => (f i).2) ⟨0, h0n⟩)
    · unfold welfare
      rw [A.welfareAux_reject f [] 0 h0n hrej]
      exact A.welfareAux_all_zero f _ 1 fun j hj => by
        show (if (j : Fin n).val = 0 then (1 : F) else 0) = 0
        exact if_neg (by omega)
  · -- threshold = ↑t with 0 < (ofLex t).1
    have hp0 : (0 : F) < (ofLex t).1 := hpos t ht
    set p := (ofLex t).1 with hp_def
    let f : Fin n → B × F := fun i => (default, if i.val = 0 then p / 2 else 0)
    have hval_lt : p / 2 < p := div_lt_self hp0 one_lt_two
    have hf0v : (f ⟨0, h0n⟩).2 = p / 2 := by simp [f]
    have hrej : ¬ ((A.threshold [] : WithTop (Lex (F × B))) ≤
        ↑(toLex ((f ⟨0, h0n⟩).2, (f ⟨0, h0n⟩).1))) := by
      rw [ht, hf0v]
      change ¬ ((↑t : WithTop (Lex (F × B))) ≤ _)
      intro hle
      rw [WithTop.coe_le_coe] at hle
      have : t = toLex ((ofLex t).1, (ofLex t).2) := rfl
      rw [this, Prod.Lex.le_iff] at hle
      rcases hle with hlt | ⟨heq, _⟩
      · exact absurd hlt (not_lt.mpr hval_lt.le)
      · exact absurd heq (ne_of_gt hval_lt)
    refine ⟨f, ?_, ?_⟩
    · exact lt_of_lt_of_le (div_pos hp0 two_pos) (le_maxV hn (fun i => (f i).2) ⟨0, h0n⟩)
    · unfold welfare
      rw [A.welfareAux_reject f [] 0 h0n hrej]
      exact A.welfareAux_all_zero f _ 1 fun j hj => by
        show (if (j : Fin n).val = 0 then p / 2 else (0 : F)) = 0
        exact if_neg (by omega)

/-- **Corollary.** No deterministic online auction with positive opening
threshold achieves a constant competitive ratio. -/
theorem no_constant_competitive_ratio [Inhabited B] [Field F] [IsStrictOrderedRing F]
    (hn : 1 ≤ n) (hpos : ∀ (t : Lex (F × B)), A.threshold [] = ↑t → (0 : F) < (ofLex t).1)
    (c : F) (hc : 0 < c) :
    ∃ f : Fin n → B × F,
      (0 : F) < maxV hn (fun i => (f i).2) ∧
      A.welfare f < c * maxV hn (fun i => (f i).2) := by
  obtain ⟨f, hmax, hw⟩ := A.welfare_can_be_zero hn hpos
  exact ⟨f, hmax, by rw [hw]; exact mul_pos hc hmax⟩

end SingleItemAuction

/-! ## Sample-then-threshold auction -/

namespace SampleThenThreshold

section AuctionDef
variable {B F : Type*} [LinearOrder F] [LinearOrder B] [Zero F] [OrderBot B]

/-- The lex-max of `(value, identity)` pairs in the rejection history,
starting from `(0, ⊥)`. -/
def maxPairFold (h : List (B × F)) : F × B :=
  h.foldl (fun (acc : F × B) (p : B × F) =>
    if acc.1 < p.2 ∨ (acc.1 = p.2 ∧ acc.2 ≤ p.1) then (p.2, p.1) else acc) (0, ⊥)

/-- The sample-then-threshold pricing rule. The first `⌊n/2⌋` arrivals
face threshold `⊤` (rejected unconditionally); thereafter the threshold
is the lex-max `(value, identity)` seen so far. -/
def auction (n : ℕ) : SingleItemAuction B F where
  threshold h :=
    if h.length < n / 2 then ⊤
    else ↑(toLex (maxPairFold h))

end AuctionDef

/-! ### Competitive ratio (Problem 2.1(c)) -/

variable {B F : Type*} [LinearOrder F] [LinearOrder B] [Field F] [IsStrictOrderedRing F]
  [OrderBot B]

open SingleItemAuction

/-- The favourable event: under permutation `σ`, the lex-argmax bidder
(in the `(v, g)` lex order) arrives in the second half (position ≥ `n/2`)
while the lex-second bidder arrives in the first half (position `< n/2`). -/
structure Favorable {n : ℕ} (g : Fin n → B) (v : Fin n → F)
    (σ : Equiv.Perm (Fin n)) where
  max_pos : Fin n
  second_pos : Fin n
  v_is_max : ∀ j, v j ≤ v (σ max_pos)
  g_is_max_among_ties : ∀ j, v j = v (σ max_pos) → g j ≤ g (σ max_pos)
  lex_is_second : ∀ j, j ≠ σ max_pos →
    v j < v (σ second_pos) ∨ (v j = v (σ second_pos) ∧ g j ≤ g (σ second_pos))
  lex_second_lt_max :
    v (σ second_pos) < v (σ max_pos) ∨
    (v (σ second_pos) = v (σ max_pos) ∧ g (σ second_pos) < g (σ max_pos))
  max_in_second_half : n / 2 ≤ max_pos.val
  second_in_first_half : second_pos.val < n / 2

/-- Welfare is nonneg for the secretary auction with nonneg valuations. -/
lemma welfare_nonneg {n : ℕ} (g : Fin n → B) (v : Fin n → F)
    (hv_nn : ∀ i, 0 ≤ v i) :
    0 ≤ (auction n).welfare (fun i => (g i, v i)) :=
  (auction n).welfareAux_nonneg _ (fun i => hv_nn i) [] 0

lemma maxPairFold_append_singleton
    (h : List (B × F)) (entry : B × F) :
    maxPairFold (h ++ [entry]) =
      let acc := maxPairFold h
      if acc.1 < entry.2 ∨ (acc.1 = entry.2 ∧ acc.2 ≤ entry.1)
      then (entry.2, entry.1) else acc := by
  simp only [maxPairFold, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem welfareAux_favorable
    {n : ℕ} (hn : 2 ≤ n) (g : Fin n → B) (v : Fin n → F)
    (hg_inj : Function.Injective g) (hv_nn : ∀ i, 0 ≤ v i)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable g v σ)
    (k : ℕ) (hk : k ≤ hσ.max_pos.val)
    (h : List (B × F)) (hlen : h.length = k)
    (hfold_ub :
      (maxPairFold h).1 < v (σ hσ.second_pos) ∨
      ((maxPairFold h).1 = v (σ hσ.second_pos) ∧
       (maxPairFold h).2 ≤ g (σ hσ.second_pos)))
    (hfold_lb : hσ.second_pos.val < k →
      v (σ hσ.second_pos) < (maxPairFold h).1 ∨
      (v (σ hσ.second_pos) = (maxPairFold h).1 ∧
       g (σ hσ.second_pos) ≤ (maxPairFold h).2)) :
    welfareAux (auction n).threshold
      (fun i => (g (σ i), v (σ i))) h k =
      v (σ hσ.max_pos) := by
  set f : Fin n → B × F := fun i => (g (σ i), v (σ i))
  have hk_lt_n : k < n := lt_of_le_of_lt hk hσ.max_pos.isLt
  have ht : (auction n).threshold h =
      if h.length < n / 2 then ⊤ else ↑(toLex (maxPairFold h)) := rfl
  by_cases hk_eq : k = hσ.max_pos.val
  · -- *** ACCEPTANCE at k = max_pos ***
    have hfin_eq : (⟨k, hk_lt_n⟩ : Fin n) = hσ.max_pos := Fin.ext hk_eq
    have h_phase2 : ¬ h.length < n / 2 := by
      rw [hlen]; exact not_lt.mpr (hk_eq ▸ hσ.max_in_second_half)
    have h_accept : ((auction n).threshold h : WithTop (Lex (F × B))) ≤
        ↑(toLex ((f ⟨k, hk_lt_n⟩).2, (f ⟨k, hk_lt_n⟩).1)) := by
      rw [ht, if_neg h_phase2, WithTop.coe_le_coe]
      rw [Prod.Lex.le_iff]
      simp only [f, hfin_eq, ofLex_toLex]
      rcases hσ.lex_second_lt_max with hvlt | ⟨hveq, hglt⟩
      · left
        rcases hfold_ub with hflt | ⟨hfeq, _⟩
        · exact lt_trans hflt hvlt
        · rw [hfeq]; exact hvlt
      · rcases hfold_ub with hflt | ⟨hfeq, hfle⟩
        · left; rw [← hveq]; exact hflt
        · right; exact ⟨by rw [hfeq, hveq], le_trans hfle hglt.le⟩
    rw [(auction n).welfareAux_accept f h k hk_lt_n h_accept]
    exact congr_arg (v ∘ σ) hfin_eq
  · -- *** REJECTION at k < max_pos ***
    have hk_lt : k < hσ.max_pos.val := Nat.lt_of_le_of_ne hk hk_eq
    have hfin_ne : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.max_pos :=
      fun heq => hk_eq (congrArg Fin.val heq)
    have hσk_ne : σ ⟨k, hk_lt_n⟩ ≠ σ hσ.max_pos := σ.injective.ne hfin_ne
    have hlex_k_le_sec := hσ.lex_is_second _ hσk_ne
    have h_reject : ¬ (((auction n).threshold h : WithTop (Lex (F × B))) ≤
        ↑(toLex ((f ⟨k, hk_lt_n⟩).2, (f ⟨k, hk_lt_n⟩).1))) := by
      rw [ht]
      by_cases h_obs : h.length < n / 2
      · rw [if_pos h_obs]
        exact not_le.mpr (WithTop.coe_lt_top _)
      · rw [if_neg h_obs]
        have h_sec_lt_k : hσ.second_pos.val < k := by
          have := hσ.second_in_first_half; omega
        have h_fold_ge_sec := hfold_lb h_sec_lt_k
        have hk_ne_sec : k ≠ hσ.second_pos.val := by omega
        have hfin_ne_sec : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.second_pos :=
          fun heq => hk_ne_sec (congrArg Fin.val heq)
        have hσk_ne_sec : σ ⟨k, hk_lt_n⟩ ≠ σ hσ.second_pos := σ.injective.ne hfin_ne_sec
        have hg_ne_sec : g (σ ⟨k, hk_lt_n⟩) ≠ g (σ hσ.second_pos) := hg_inj.ne hσk_ne_sec
        have hlex_k_strict : v (σ ⟨k, hk_lt_n⟩) < v (σ hσ.second_pos) ∨
            (v (σ ⟨k, hk_lt_n⟩) = v (σ hσ.second_pos) ∧
             g (σ ⟨k, hk_lt_n⟩) < g (σ hσ.second_pos)) := by
          rcases hlex_k_le_sec with hvlt | ⟨hveq, hgle⟩
          · exact Or.inl hvlt
          · exact Or.inr ⟨hveq, lt_of_le_of_ne hgle hg_ne_sec⟩
        intro hle
        rw [WithTop.coe_le_coe, Prod.Lex.le_iff] at hle
        simp only [f, ofLex_toLex] at hle
        rcases hle with hlt | ⟨heq, hle⟩
        · rcases h_fold_ge_sec with hfvgt | ⟨hfveq, _⟩ <;>
            rcases hlex_k_strict with hvlt | ⟨hveq, _⟩ <;> linarith
        · rcases hlex_k_strict with hvlt | ⟨hveq, hglt⟩
          · rcases h_fold_ge_sec with hfvgt | ⟨hfveq, _⟩ <;> linarith
          · rcases h_fold_ge_sec with hfvgt | ⟨hfveq, hfgle⟩
            · linarith
            · exact absurd (lt_of_lt_of_le hglt (le_trans hfgle hle)) (lt_irrefl _)
    rw [(auction n).welfareAux_reject f h k hk_lt_n h_reject]
    exact welfareAux_favorable hn g v hg_inj hv_nn hσ (k + 1) (by omega)
      (h ++ [f ⟨k, hk_lt_n⟩]) (by simp [hlen])
      (by -- Upper bound on new fold
          have hmpa := maxPairFold_append_singleton h (f ⟨k, hk_lt_n⟩)
          by_cases hcond : (maxPairFold h).1 < (f ⟨k, hk_lt_n⟩).2 ∨
              ((maxPairFold h).1 = (f ⟨k, hk_lt_n⟩).2 ∧
               (maxPairFold h).2 ≤ (f ⟨k, hk_lt_n⟩).1)
          · rw [hmpa, if_pos hcond]
            show (f ⟨k, hk_lt_n⟩).2 < v (σ hσ.second_pos) ∨
              ((f ⟨k, hk_lt_n⟩).2 = v (σ hσ.second_pos) ∧
               (f ⟨k, hk_lt_n⟩).1 ≤ g (σ hσ.second_pos))
            exact hlex_k_le_sec
          · rw [hmpa, if_neg hcond]; exact hfold_ub)
      (by -- Lower bound on new fold
          intro h_sec
          have hmpa := maxPairFold_append_singleton h (f ⟨k, hk_lt_n⟩)
          rcases Nat.lt_succ_iff_lt_or_eq.mp h_sec with h_lt | h_eq
          · have h_old_lb := hfold_lb h_lt
            have hk_ne_sec : k ≠ hσ.second_pos.val := by omega
            have hfin_ne_sec : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.second_pos :=
              fun heq => hk_ne_sec (congrArg Fin.val heq)
            have hσk_ne_sec : σ ⟨k, hk_lt_n⟩ ≠ σ hσ.second_pos := σ.injective.ne hfin_ne_sec
            have hg_ne : g (σ ⟨k, hk_lt_n⟩) ≠ g (σ hσ.second_pos) := hg_inj.ne hσk_ne_sec
            have hentry_strict : v (σ ⟨k, hk_lt_n⟩) < v (σ hσ.second_pos) ∨
                (v (σ ⟨k, hk_lt_n⟩) = v (σ hσ.second_pos) ∧
                 g (σ ⟨k, hk_lt_n⟩) < g (σ hσ.second_pos)) := by
              rcases hlex_k_le_sec with hvlt | ⟨hveq, hgle⟩
              · exact Or.inl hvlt
              · exact Or.inr ⟨hveq, lt_of_le_of_ne hgle hg_ne⟩
            have h_if_false : ¬ ((maxPairFold h).1 < (f ⟨k, hk_lt_n⟩).2 ∨
                ((maxPairFold h).1 = (f ⟨k, hk_lt_n⟩).2 ∧
                 (maxPairFold h).2 ≤ (f ⟨k, hk_lt_n⟩).1)) := by
              show ¬ ((maxPairFold h).1 < v (σ ⟨k, hk_lt_n⟩) ∨
                ((maxPairFold h).1 = v (σ ⟨k, hk_lt_n⟩) ∧
                 (maxPairFold h).2 ≤ g (σ ⟨k, hk_lt_n⟩)))
              rintro (hflt | ⟨hfeq, hfle⟩)
              · rcases h_old_lb with hsvlt | ⟨hsveq, _⟩ <;>
                  rcases hentry_strict with hvlt | ⟨hveq, _⟩ <;> linarith
              · rcases hentry_strict with hvlt | ⟨hveq, hglt⟩
                · rcases h_old_lb with hsvlt | ⟨hsveq, _⟩ <;> linarith
                · rcases h_old_lb with hsvlt | ⟨hsveq, hsgle⟩
                  · linarith
                  · exact absurd (lt_of_lt_of_le hglt (le_trans hsgle hfle)) (lt_irrefl _)
            rw [hmpa, if_neg h_if_false]
            exact h_old_lb
          · have hfin_sec : (⟨k, hk_lt_n⟩ : Fin n) = hσ.second_pos := Fin.ext h_eq.symm
            by_cases hcond : (maxPairFold h).1 < (f ⟨k, hk_lt_n⟩).2 ∨
                ((maxPairFold h).1 = (f ⟨k, hk_lt_n⟩).2 ∧
                 (maxPairFold h).2 ≤ (f ⟨k, hk_lt_n⟩).1)
            · rw [hmpa, if_pos hcond]
              simp only [f, hfin_sec]
              exact Or.inr ⟨trivial, le_refl _⟩
            · rw [hmpa, if_neg hcond]
              simp only [f, hfin_sec] at hcond
              have hvle : v (σ hσ.second_pos) ≤ (maxPairFold h).1 :=
                not_lt.mp (fun hlt => hcond (Or.inl hlt))
              rcases eq_or_lt_of_le hvle with heqv | hltv
              · right; constructor
                · exact heqv
                · have : ¬ ((maxPairFold h).2 ≤ g (σ hσ.second_pos)) :=
                    fun hle => hcond (Or.inr ⟨heqv.symm, hle⟩)
                  exact (not_le.mp this).le
              · exact Or.inl hltv)
termination_by hσ.max_pos.val - k
decreasing_by omega

/-- Under the favourable event, the secretary auction allocates to
the argmax bidder, yielding welfare = `maxV v`. -/
lemma welfare_eq_max_of_favorable
    {n : ℕ} (hn : 2 ≤ n) (g : Fin n → B) (v : Fin n → F)
    (hg_inj : Function.Injective g)
    (hv_nn : ∀ i, 0 ≤ v i)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable g v σ) :
    (auction n).welfare (fun i => (g (σ i), v (σ i))) =
      maxV (by omega) v := by
  unfold SingleItemAuction.welfare
  have hmpe : maxPairFold ([] : List (B × F)) = ((0 : F), (⊥ : B)) := by
    simp [maxPairFold]
  have h_init_ub : (maxPairFold ([] : List (B × F))).1 < v (σ hσ.second_pos) ∨
      ((maxPairFold ([] : List (B × F))).1 = v (σ hσ.second_pos) ∧
       (maxPairFold ([] : List (B × F))).2 ≤ g (σ hσ.second_pos)) := by
    rw [hmpe]; dsimp only
    rcases lt_or_eq_of_le (hv_nn (σ hσ.second_pos)) with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, bot_le⟩
  rw [welfareAux_favorable hn g v hg_inj hv_nn hσ 0 (by omega) [] rfl
    h_init_ub (by omega)]
  exact le_antisymm (le_maxV _ v _) (Finset.sup'_le _ _ (fun j _ => hσ.v_is_max j))

/-- The set of permutations satisfying the favourable event. -/
noncomputable def favorableSet
    {n : ℕ} (g : Fin n → B) (v : Fin n → F) : Finset (Equiv.Perm (Fin n)) :=
  letI : DecidablePred (fun σ => Nonempty (Favorable g v σ)) := Classical.decPred _
  Finset.univ.filter (fun σ => Nonempty (Favorable g v σ))

/-- The elementary natural-number inequality at the heart of
`favorableSet_card_ge`: for every `n ≥ 2`,
`n! ≤ 4 · (n − ⌊n/2⌋) · ⌊n/2⌋ · (n − 2)!`. -/
private lemma factorial_le_four_split (n : ℕ) (hn : 2 ≤ n) :
    n.factorial ≤ 4 * (n - n / 2) * (n / 2) * (n - 2).factorial := by
  have hfac : n.factorial = n * (n - 1) * (n - 2).factorial := by
    rcases n with _ | _ | n
    · omega
    · omega
    · simp [Nat.factorial_succ]
      ring
  rw [hfac]
  have hk : 4 * (n - n / 2) * (n / 2) ≥ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hm_ge : 1 ≤ m := by omega
      have hn2 : n / 2 = m := by omega
      have hsub : n - n / 2 = m := by omega
      have hn_eq : n = 2 * m := by omega
      rw [hsub, hn2, hn_eq]
      have hsub' : 2 * m - 1 + 1 = 2 * m := by omega
      nlinarith [hm_ge, hsub']
    · have hn2 : n / 2 = m := by omega
      have hsub : n - n / 2 = m + 1 := by omega
      have hn_eq : n = 2 * m + 1 := hm
      rw [hsub, hn2, hn_eq]
      have hsub' : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hsub']
      nlinarith
  exact Nat.mul_le_mul_right _ hk

/-- For distinct `a ≠ c` and distinct `x ≠ y` in any type with decidable
equality, there is a permutation sending `a ↦ x` and `c ↦ y`. -/
private lemma exists_perm_two {α : Type*} [DecidableEq α] {a c x y : α}
    (hac : a ≠ c) (hxy : x ≠ y) :
    ∃ ρ : Equiv.Perm α, ρ a = x ∧ ρ c = y := by
  classical
  set t := Equiv.swap a x with ht
  have hcx : t c ≠ x := by
    have hta : t a = x := by rw [ht, Equiv.swap_apply_left]
    rw [← hta]
    exact fun h => hac (t.injective h).symm
  refine ⟨Equiv.swap (t c) y * t, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, ht, Equiv.swap_apply_left, ← ht]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hcx) hxy
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- Count of permutations fixing two given distinct points `a ≠ c` is `(n-2)!`. -/
private lemma fix_two_card {n : ℕ} {a c : Fin n} (hac : a ≠ c) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π a = a ∧ π c = c)).card
      = (n - 2).factorial := by
  classical
  set p : Fin n → Prop := fun z => z ≠ a ∧ z ≠ c with hp
  have hcard_eq :
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π a = a ∧ π c = c)).card
        = Fintype.card {f : Equiv.Perm (Fin n) // ∀ z, ¬ p z → f z = z} := by
    rw [Fintype.card_subtype]
    congr 1
    apply Finset.filter_congr
    intro π _
    simp only [hp, not_and_or, not_not]
    constructor
    · rintro ⟨ha, hc⟩ z (rfl | rfl)
      · exact ha
      · exact hc
    · intro h
      exact ⟨h a (Or.inl rfl), h c (Or.inr rfl)⟩
  rw [hcard_eq, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm p),
    Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype]
  have hset : Finset.filter p (Finset.univ : Finset (Fin n))
      = (Finset.univ.erase a).erase c := by
    ext z
    simp only [hp, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  have : ({x | x ≠ a ∧ x ≠ c} : Finset (Fin n)) = (Finset.univ.erase a).erase c := hset
  rw [this, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hac.symm, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- Inner count: for fixed distinct `a ≠ c` in `Fin n` and fixed distinct
`x ≠ y`, the number of permutations sending `a ↦ x` and `c ↦ y` is `(n-2)!`. -/
private lemma fiber_card {n : ℕ} {a c x y : Fin n} (hac : a ≠ c) (hxy : x ≠ y) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π a = x ∧ π c = y)).card
      = (n - 2).factorial := by
  classical
  obtain ⟨ρ, hρa, hρc⟩ := exists_perm_two hac hxy
  rw [← fix_two_card hac]
  apply Finset.card_nbij' (fun π => ρ⁻¹ * π) (fun π => ρ * π)
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hπ.1, ← hρa]; exact ρ.symm_apply_apply a
    · rw [Equiv.Perm.mul_apply, hπ.2, ← hρc]; exact ρ.symm_apply_apply c
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    refine ⟨?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hπ.1, hρa]
    · rw [Equiv.Perm.mul_apply, hπ.2, hρc]
  · intro π _
    simp [← mul_assoc]
  · intro π _
    simp [← mul_assoc]

/-- The first-half positions `{x : Fin n | x.val < n/2}` number `n/2`. -/
private lemma card_first_half (n : ℕ) :
    (Finset.univ.filter (fun x : Fin n => x.val < n / 2)).card = n / 2 := by
  classical
  conv_rhs => rw [show n / 2 = (Finset.range (n / 2)).card from (Finset.card_range _).symm]
  refine Finset.card_bij' (fun x _ => x.val)
    (fun k hk => (⟨k, (Finset.mem_range.1 hk).trans_le (Nat.div_le_self n 2)⟩ : Fin n))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hx ⊢
    exact hx
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
    exact hk
  · intro x _; rfl
  · intro k _; rfl

/-- The second-half positions `{x : Fin n | n/2 ≤ x.val}` number `n - n/2`. -/
private lemma card_second_half (n : ℕ) :
    (Finset.univ.filter (fun x : Fin n => n / 2 ≤ x.val)).card = n - n / 2 := by
  classical
  have hcompl : (Finset.univ.filter (fun x : Fin n => n / 2 ≤ x.val))
      = (Finset.univ.filter (fun x : Fin n => x.val < n / 2))ᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_lt]
  rw [hcompl, Finset.card_compl, card_first_half, Fintype.card_fin]

/-- The count `Q` of permutations sending a fixed `a` into the second half and a fixed
distinct `c` into the first half equals `(n - n/2) * (n/2) * (n-2)!`. -/
private lemma count_Q {n : ℕ} {a c : Fin n} (hac : a ≠ c) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      n / 2 ≤ (π a).val ∧ (π c).val < n / 2)).card
      = (n - n / 2) * (n / 2) * (n - 2).factorial := by
  classical
  set SH := Finset.univ.filter (fun x : Fin n => n / 2 ≤ x.val) with hSH
  set FH := Finset.univ.filter (fun x : Fin n => x.val < n / 2) with hFH
  have hmaps : (↑(Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      n / 2 ≤ (π a).val ∧ (π c).val < n / 2)) : Set (Equiv.Perm (Fin n))).MapsTo
        (fun π => (π a, π c)) (↑(SH ×ˢ FH)) := by
    intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hSH, hFH,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hπ.1, hπ.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ p ∈ SH ×ˢ FH,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
          n / 2 ≤ (π a).val ∧ (π c).val < n / 2) |>.filter
          (fun π => (π a, π c) = p)).card = (n - 2).factorial := by
    rintro ⟨x, y⟩ hp
    simp only [hSH, hFH, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    have hxy : x ≠ y := by
      intro h; rw [h] at hp; omega
    have hset : (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
          n / 2 ≤ (π a).val ∧ (π c).val < n / 2) |>.filter
          (fun π => (π a, π c) = (x, y)))
        = Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π a = x ∧ π c = y) := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, ?_⟩, h1, h2⟩
        · rw [h1]; exact hp.1
        · rw [h2]; exact hp.2
    rw [hset, fiber_card hac hxy]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_product, smul_eq_mul,
    hSH, hFH, card_second_half, card_first_half]

/-- The favourable set has at least `(n - n/2) · (n/2) · (n-2)!`
permutations. -/
private theorem favorableSet_card_lower {n : ℕ} (hn : 2 ≤ n)
    (g : Fin n → B) (v : Fin n → F)
    (hg_inj : Function.Injective g) :
    (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet g v).card := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- Find lex-argmax a
  obtain ⟨a, _, ha_max⟩ := Finset.exists_max_image Finset.univ
    (fun i => toLex (v i, g i)) hne
  -- Find lex-second c (max among j ≠ a)
  have hne2 : (Finset.univ.erase a : Finset (Fin n)).Nonempty := by
    have hcard : 0 < (Finset.univ.erase a : Finset (Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega
    exact Finset.card_pos.mp hcard
  obtain ⟨c, hc_mem, hc_max⟩ := Finset.exists_max_image (Finset.univ.erase a)
    (fun i => toLex (v i, g i)) hne2
  have hca : c ≠ a := (Finset.mem_erase.mp hc_mem).1
  have hac : a ≠ c := hca.symm
  -- Extract properties of a: lex-max means v j ≤ v a (and g j ≤ g a at ties)
  have ha_lex : ∀ j, v j < v a ∨ (v j = v a ∧ g j ≤ g a) := by
    intro j
    have h := ha_max j (Finset.mem_univ _)
    rw [Prod.Lex.le_iff] at h
    simp only [ofLex_toLex] at h
    exact h
  have ha_v_max : ∀ j, v j ≤ v a := by
    intro j; rcases ha_lex j with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq
  have ha_g_max : ∀ j, v j = v a → g j ≤ g a := by
    intro j hvj; rcases ha_lex j with hlt | ⟨_, hle⟩
    · exact absurd hlt (not_lt.mpr hvj.ge)
    · exact hle
  -- Extract properties of c: lex-second among j ≠ a
  have hc_lex_second : ∀ j, j ≠ a →
      v j < v c ∨ (v j = v c ∧ g j ≤ g c) := by
    intro j hj
    have h := hc_max j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
    rw [Prod.Lex.le_iff] at h
    simp only [ofLex_toLex] at h
    exact h
  -- c is strictly below a in lex order
  have hca_lt : v c < v a ∨ (v c = v a ∧ g c < g a) := by
    have h := ha_max c (Finset.mem_univ _)
    rw [Prod.Lex.le_iff] at h
    simp only [ofLex_toLex] at h
    rcases h with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · right; refine ⟨heq, lt_of_le_of_ne hle ?_⟩
      intro hge; exact hca (hg_inj hge)
  -- Define the candidate set via σ.symm
  set S := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    n / 2 ≤ (σ.symm a).val ∧ (σ.symm c).val < n / 2) with hS_def
  -- S ⊆ favorableSet
  have hS_sub : S ⊆ favorableSet g v := by
    intro σ hσ
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    unfold favorableSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨{
      max_pos := σ.symm a
      second_pos := σ.symm c
      v_is_max := fun j => by
        have : σ (σ.symm a) = a := σ.apply_symm_apply a
        rw [this]; exact ha_v_max j
      g_is_max_among_ties := fun j hvj => by
        have : σ (σ.symm a) = a := σ.apply_symm_apply a
        rw [this] at hvj ⊢; exact ha_g_max j hvj
      lex_is_second := fun j hj => by
        have hsa : σ (σ.symm a) = a := σ.apply_symm_apply a
        have hsc : σ (σ.symm c) = c := σ.apply_symm_apply c
        rw [hsa] at hj; rw [hsc]; exact hc_lex_second j hj
      lex_second_lt_max := by
        have hsa : σ (σ.symm a) = a := σ.apply_symm_apply a
        have hsc : σ (σ.symm c) = c := σ.apply_symm_apply c
        rw [hsa, hsc]; exact hca_lt
      max_in_second_half := hσ.1
      second_in_first_half := hσ.2
    }⟩⟩
  -- S.card = count_Q via the bijection σ ↦ σ.symm
  have hS_card : S.card = (n - n / 2) * (n / 2) * (n - 2).factorial := by
    set T := Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      n / 2 ≤ (π a).val ∧ (π c).val < n / 2) with hT_def
    have hST : S.card = T.card := by
      apply Finset.card_nbij' (fun σ => σ.symm) (fun π => π.symm)
      · intro σ hσ
        have hσ' := (Finset.mem_filter.mp hσ).2
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ'⟩)
      · intro π hπ
        have hπ' := (Finset.mem_filter.mp (Finset.mem_coe.mp hπ)).2
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        simp only [Equiv.symm_symm]; exact hπ'
      · intro σ _; exact σ.symm_symm
      · intro π _; exact π.symm_symm
    rw [hST]
    exact count_Q hac
  calc (n - n / 2) * (n / 2) * (n - 2).factorial
      = S.card := hS_card.symm
    _ ≤ (favorableSet g v).card := Finset.card_le_card hS_sub

/-- The favourable set has at least `n!/4` elements. -/
lemma favorableSet_card_ge {n : ℕ} (hn : 2 ≤ n)
    (g : Fin n → B) (v : Fin n → F) (hg_inj : Function.Injective g) :
    (n.factorial : F) ≤ 4 * ((favorableSet g v).card : F) := by
  have hlow : (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet g v).card :=
    favorableSet_card_lower hn g v hg_inj
  have hnat : n.factorial ≤ 4 * (favorableSet g v).card :=
    calc n.factorial ≤ 4 * (n - n / 2) * (n / 2) * (n - 2).factorial :=
            factorial_le_four_split n hn
      _ = 4 * ((n - n / 2) * (n / 2) * (n - 2).factorial) := by ring
      _ ≤ 4 * (favorableSet g v).card := Nat.mul_le_mul_left _ hlow
  exact_mod_cast hnat

/-- **Problem 2.1 (c).** Under uniformly random arrival, the secretary
rule achieves expected welfare `≥ (1/4) · max v` for injective identities.
-/
theorem competitive
    {n : ℕ} (hn : 2 ≤ n) (g : Fin n → B) (v : Fin n → F)
    (hg_inj : Function.Injective g)
    (hv_nn : ∀ i, 0 ≤ v i) :
    (1 / 4 : F) * maxV (by omega) v ≤
      (∑ σ : Equiv.Perm (Fin n),
        (auction n).welfare (fun i => (g (σ i), v (σ i)))) /
          (n.factorial : F) := by
  classical
  set MAX := maxV (show 1 ≤ n by omega) v with hMAX_def
  have hMAX_nn : 0 ≤ MAX :=
    le_trans (hv_nn ⟨0, by omega⟩) (le_maxV _ v _)
  have hwelfare_nn :
      ∀ σ : Equiv.Perm (Fin n),
        0 ≤ (auction n).welfare (fun i => (g (σ i), v (σ i))) :=
    fun σ => welfare_nonneg (g ∘ σ) (v ∘ σ) (fun i => hv_nn _)
  have hwelfare_FS :
      ∀ σ ∈ favorableSet g v,
        (auction n).welfare (fun i => (g (σ i), v (σ i))) = MAX := by
    intro σ hσ
    obtain ⟨fav⟩ : Nonempty (Favorable g v σ) := (Finset.mem_filter.mp hσ).2
    exact welfare_eq_max_of_favorable hn g v hg_inj hv_nn fav
  have step1 :
      ((favorableSet g v).card : F) * MAX ≤
        ∑ σ : Equiv.Perm (Fin n),
          (auction n).welfare (fun i => (g (σ i), v (σ i))) := by
    calc ((favorableSet g v).card : F) * MAX
        = ∑ _σ ∈ favorableSet g v, MAX := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ favorableSet g v,
            (auction n).welfare (fun i => (g (σ i), v (σ i))) :=
          Finset.sum_congr rfl (fun σ hσ => (hwelfare_FS σ hσ).symm)
      _ ≤ ∑ σ : Equiv.Perm (Fin n),
            (auction n).welfare (fun i => (g (σ i), v (σ i))) :=
          Finset.sum_le_univ_sum_of_nonneg (fun σ => hwelfare_nn σ)
  have step2 : (n.factorial : F) ≤ 4 * ((favorableSet g v).card : F) :=
    favorableSet_card_ge hn g v hg_inj
  have hfact_pos : (0 : F) < (n.factorial : F) := by positivity
  rw [le_div_iff₀ hfact_pos]
  calc (1 / 4 : F) * MAX * (n.factorial : F)
      = MAX * ((1 / 4 : F) * (n.factorial : F)) := by ring
    _ ≤ MAX * ((favorableSet g v).card : F) := by
        apply mul_le_mul_of_nonneg_left _ hMAX_nn
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_of_le_mul₀ (by positivity) (by positivity) (by linarith)
    _ = ((favorableSet g v).card : F) * MAX := by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
          (auction n).welfare (fun i => (g (σ i), v (σ i))) := step1

end SampleThenThreshold

/-! ## Counterexample: Strict value comparison breaks the competitive guarantee -/

namespace StrictComparison

variable {B F : Type*} [LinearOrder F] [LinearOrder B] [Zero F] [OrderBot B] [OrderTop B]

open SingleItemAuction SampleThenThreshold

/-- Sample-then-threshold auction with strict value comparison only.
The identity component of the threshold is `⊤ : B`, so acceptance
degenerates to the strict inequality `p < v` (the tie-breaking disjunct
`⊤ ≤ b` fails for every `b < ⊤`). -/
def auction (n : ℕ) : SingleItemAuction B F where
  threshold h :=
    if h.length < n / 2 then ⊤
    else ↑(toLex ((maxPairFold h).1, (⊤ : B)))

variable [Field F] [IsStrictOrderedRing F]

/-- With `n = 2`, equal values `M > 0`, and identities strictly below `⊤`,
the strict-comparison auction achieves welfare `= 0` on every arrival
sequence. Since `max v = M > 0`, this violates the `1/4`-competitive
bound. -/
theorem welfare_eq_zero
    (f : Fin 2 → B × F) (M : F) (hM : 0 < M)
    (hv : ∀ i, (f i).2 = M) (hg : ∀ i, (f i).1 < (⊤ : B)) :
    (auction 2 : SingleItemAuction B F).welfare f = 0 := by
  unfold SingleItemAuction.welfare
  -- k = 0: observe phase, threshold = ⊤, rejected
  have hrej0 : ¬ (((auction 2 : SingleItemAuction B F).threshold ([] : List (B × F)) :
      WithTop (Lex (F × B))) ≤
      ↑(toLex ((f ⟨0, by omega⟩).2, (f ⟨0, by omega⟩).1))) := by
    simp only [auction, List.length_nil]
    exact not_le.mpr (WithTop.coe_lt_top _)
  rw [welfareAux_reject _ f [] 0 (by omega) hrej0]
  -- k = 1: threshold has value M and identity ⊤; rejected since M < M fails and ⊤ ≤ g fails
  have hthr1 : (auction 2 : SingleItemAuction B F).threshold [f ⟨0, by omega⟩] =
      ↑(toLex ((maxPairFold [f ⟨0, by omega⟩]).1, (⊤ : B))) := by
    simp [auction]
  have hrej1 : ¬ (((auction 2 : SingleItemAuction B F).threshold
      ([] ++ [f ⟨0, by omega⟩]) : WithTop (Lex (F × B))) ≤
      ↑(toLex ((f ⟨1, by omega⟩).2, (f ⟨1, by omega⟩).1))) := by
    simp only [List.nil_append]
    rw [hthr1]
    intro hle
    rw [WithTop.coe_le_coe, Prod.Lex.le_iff] at hle
    simp only [ofLex_toLex] at hle
    rcases hle with hlt | ⟨_, hle⟩
    · have hmpf : (maxPairFold [f ⟨0, by omega⟩]).1 = M := by
        simp only [maxPairFold, List.foldl_cons, List.foldl_nil]
        have : (0 : F) < (f ⟨0, by omega⟩).2 := by rw [hv]; exact hM
        rw [if_pos (Or.inl this)]
        exact hv _
      rw [hmpf, hv] at hlt
      exact lt_irrefl M hlt
    · exact absurd hle (not_le.mpr (hg _))
  rw [welfareAux_reject _ f ([] ++ [f ⟨0, by omega⟩]) 1 (by omega) hrej1]
  exact welfareAux_done _ f _ 2 (by omega)

end StrictComparison

/-! ## Counterexample: Weak value comparison degrades to 1/n on the needle profile -/

namespace WeakComparison

variable {B F : Type*} [LinearOrder F] [LinearOrder B] [Zero F] [OrderBot B]

open SingleItemAuction SampleThenThreshold

/-- Sample-then-threshold auction with weak value comparison: identity
threshold = `⊥`, so acceptance degenerates to the weak inequality
`p ≤ v`. -/
def auction (n : ℕ) : SingleItemAuction B F where
  threshold h :=
    if h.length < n / 2 then ⊤
    else ↑(toLex ((maxPairFold h).1, (⊥ : B)))

/-- When all values in the history are `0`, the value component of
`maxPairFold` remains `0`. -/
lemma maxPairFold_fst_zero (h : List (B × F))
    (hzero : ∀ p ∈ h, p.2 = (0 : F)) :
    (maxPairFold h).1 = 0 := by
  suffices ∀ (b : B),
      (h.foldl (fun (acc : F × B) (p : B × F) =>
        if acc.1 < p.2 ∨ (acc.1 = p.2 ∧ acc.2 ≤ p.1) then (p.2, p.1) else acc)
        ((0 : F), b)).1 = 0 from
    this ⊥
  intro b
  induction h generalizing b with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have ha : a.2 = (0 : F) := hzero a (by simp)
    have ht : ∀ p ∈ t, p.2 = (0 : F) := fun p hp => hzero p (by simp [hp])
    by_cases hcond : (0 : F) < a.2 ∨ ((0 : F) = a.2 ∧ b ≤ a.1)
    · rw [if_pos hcond, ha]
      exact ih ht a.1
    · rw [if_neg hcond]
      exact ih ht b

variable [Field F] [IsStrictOrderedRing F]

/-- With `n = 3` and the needle profile (one bidder has value `M`, the
others value `0`), if the needle arrives last, the weak auction accepts a
haystack bidder (value `0`) and welfare `= 0`, while `max v = M > 0`. -/
theorem welfare_eq_zero_needle_last
    (g : Fin 3 → B) (M : F) (_hM : 0 < M) :
    let f : Fin 3 → B × F := fun i => (g i, if i.val = 2 then M else 0)
    (WeakComparison.auction 3 : SingleItemAuction B F).welfare f = 0 := by
  intro f
  unfold SingleItemAuction.welfare
  -- k = 0: observe phase (0 < 1 = 3/2), threshold = ⊤, rejected
  have hf0 : f ⟨0, by omega⟩ = (g 0, (0 : F)) := by simp [f]
  have hf1 : f ⟨1, by omega⟩ = (g 1, (0 : F)) := by simp [f]
  have hrej0 : ¬ (((WeakComparison.auction 3 : SingleItemAuction B F).threshold
      ([] : List (B × F)) : WithTop (Lex (F × B))) ≤
      ↑(toLex ((f ⟨0, by omega⟩).2, (f ⟨0, by omega⟩).1))) := by
    simp only [WeakComparison.auction, List.length_nil]
    exact not_le.mpr (WithTop.coe_lt_top _)
  rw [welfareAux_reject _ f [] 0 (by omega) hrej0]
  -- k = 1: threshold = ↑(toLex (0, ⊥)); bidder 1 (value 0) is accepted
  -- since toLex (0, ⊥) ≤ toLex (0, g 1) holds by bot_le
  have hthr1 : (WeakComparison.auction 3 : SingleItemAuction B F).threshold [f ⟨0, by omega⟩] =
      ↑(toLex ((maxPairFold [f ⟨0, by omega⟩]).1, (⊥ : B))) := by
    simp [WeakComparison.auction]
  have hacc1 : ((WeakComparison.auction 3 : SingleItemAuction B F).threshold
      ([] ++ [f ⟨0, by omega⟩]) : WithTop (Lex (F × B))) ≤
      ↑(toLex ((f ⟨1, by omega⟩).2, (f ⟨1, by omega⟩).1)) := by
    simp only [List.nil_append]
    rw [hthr1, hf0]
    have hmpf : (maxPairFold [(g 0, (0 : F))]).1 = 0 :=
      maxPairFold_fst_zero _ (fun p hp => by simp_all)
    rw [hmpf, hf1]
    rw [WithTop.coe_le_coe, Prod.Lex.le_iff]
    exact Or.inr ⟨rfl, bot_le⟩
  rw [welfareAux_accept _ f ([] ++ [f ⟨0, by omega⟩]) 1 (by omega) hacc1]
  -- welfare = (f 1).2 = 0
  simp [f]

end WeakComparison

end Online.Auction
