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

/-!
# Online Single-Item (Posted-Price) Auction

The **online single-item auction** sells one indivisible good to bidders
who arrive one at a time. At each step the system receives two pieces of
information: the bidder's **identity** `b : B` and their **value** `v : F`.
The auctioneer posts a take-it-or-leave-it price in `WithTop F` — the
price `⊤` rejects unconditionally (used in the secretary auction's observe
phase), and `↑p` accepts a bidder whose value meets `p`.

The pricing rule sees the full history of rejected `(identity, value)` pairs;
the "no future" constraint of online algorithms is built into the type.

## Main definitions

* `SingleItemAuction B F` — a pricing rule `List (B × F) → WithTop F`.
* `welfare` — social welfare under a given arrival sequence.
* `utility` — quasi-linear utility of a specific bidder.
* `Secretary.auction` — the secretary (sample-then-threshold) pricing rule.

## Main results

* `dsic` — truthful bidding is weakly dominant for every bidder (Problem 2.1(a)).
* `welfare_can_be_zero` — any auction with opening price `> 0` can be forced
  to welfare `0` (Problem 2.1(b)).
* `Secretary.competitive` — the secretary rule is 1/4-competitive under
  uniformly random arrival for distinct valuations (Problem 2.1(c)).
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

/-- An online single-item auction is a *pricing rule*: given the history
of rejected `(identity, value)` pairs, it posts the next price in
`WithTop F`. The price `⊤` rejects unconditionally; `↑p` accepts when
`p ≤ value`. -/
@[ext]
structure SingleItemAuction (B F : Type*) where
  price : List (B × F) → WithTop F

/-- Maximum of a valuation profile over `Fin n`. -/
noncomputable def maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) : F :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ v

lemma le_maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) (i : Fin n) :
    v i ≤ maxV hn v :=
  Finset.le_sup' v (Finset.mem_univ i)

namespace SingleItemAuction

variable [LinearOrder F] (A : SingleItemAuction B F)

/-- The auction as an `OnlineAlgorithm`. Each step receives an
`Option (B × F)` input — `some (bi, vi)` for a genuine bidder,
`none` for end-of-input. Output on sale is the posted price. -/
def online : OnlineAlgorithm (B × F) (AuctionState B F) F where
  init := .unsold []
  step
    | .unsold h, some (bi, vi) =>
        match A.price h with
        | none   => (.unsold (h ++ [(bi, vi)]), none)
        | some p => if p ≤ vi then (.sold h.length p, some p)
                    else (.unsold (h ++ [(bi, vi)]), none)
    | .unsold h, none => (.unsold h, none)
    | .sold w p, _    => (.sold w p, none)

/-- Run the auction on an input sequence, returning the sale price. -/
def run (inputs : List (B × F)) : Option F :=
  (A.online.run A.online.init inputs).2

/-! ### Welfare -/

/-- Welfare helper: process bidders from index `k` onward with
accumulated rejection history `h`. Returns the value of the first
bidder whose value clears the posted price, or `0`. -/
private def welfareAux [Zero F]
    (price : List (B × F) → WithTop F)
    {n : ℕ} (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) : F :=
  if hk : k < n then
    let entry := f ⟨k, hk⟩
    if price h ≤ (entry.2 : WithTop F) then entry.2
    else welfareAux price f (h ++ [entry]) (k + 1)
  else 0
termination_by n - k

/-- Social welfare: the value of the winning bidder (or `0`) under
arrival sequence `f : Fin n → B × F`. -/
def welfare [Zero F] {n : ℕ} (f : Fin n → B × F) : F :=
  welfareAux A.price f [] 0

@[simp] lemma welfareAux_done [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : ¬ k < n) :
    welfareAux A.price f h k = 0 := by
  rw [welfareAux, dif_neg hk]

lemma welfareAux_accept [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : k < n)
    (hacc : A.price h ≤ ((f ⟨k, hk⟩).2 : WithTop F)) :
    welfareAux A.price f h k = (f ⟨k, hk⟩).2 := by
  rw [welfareAux, dif_pos hk]
  simp only
  rw [if_pos hacc]

lemma welfareAux_reject [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ) (hk : k < n)
    (hrej : ¬ A.price h ≤ ((f ⟨k, hk⟩).2 : WithTop F)) :
    welfareAux A.price f h k =
      welfareAux A.price f (h ++ [f ⟨k, hk⟩]) (k + 1) := by
  rw [welfareAux, dif_pos hk]
  simp only
  rw [if_neg hrej]

lemma welfareAux_nonneg [Zero F] {n : ℕ}
    (f : Fin n → B × F) (hf : ∀ i, 0 ≤ (f i).2)
    (h : List (B × F)) (k : ℕ) :
    0 ≤ welfareAux A.price f h k := by
  by_cases hk : k < n
  · by_cases hacc : A.price h ≤ ((f ⟨k, hk⟩).2 : WithTop F)
    · rw [A.welfareAux_accept f h k hk hacc]; exact hf ⟨k, hk⟩
    · rw [A.welfareAux_reject f h k hk hacc]
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
      match A.price h with
      | none   => 0
      | some p => if p ≤ (f i).2 then v i - p else 0
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

/-- At a fixed price, truthful bidding weakly dominates any other bid. -/
private lemma local_dsic [Ring F] [IsStrictOrderedRing F] (p v bid : F) :
    (if p ≤ bid then v - p else 0) ≤
    (if p ≤ v then v - p else 0) := by
  by_cases hpv : p ≤ v
  · rw [if_pos hpv]
    by_cases hpb : p ≤ bid
    · rw [if_pos hpb]
    · rw [if_neg hpb]; exact sub_nonneg.mpr hpv
  · rw [if_neg hpv]
    by_cases hpb : p ≤ bid
    · rw [if_pos hpb]; exact sub_nonpos.mpr (not_le.mp hpv).le
    · rw [if_neg hpb]

/-- **Problem 2.1 (a): the online single-item auction is DSIC.**

For every arrival sequence `f`, every true-valuation profile `v`, and
every bidder `i`, replacing bidder `i`'s entry with `((f i).1, v i)` —
keeping their identity, switching to truthful bidding — weakly improves
their utility. -/
theorem dsic [Ring F] [IsStrictOrderedRing F] {n : ℕ}
    (f : Fin n → B × F) (v : Fin n → F) (i : Fin n) :
    A.utility f v i ≤ A.utility (update f i ((f i).1, v i)) v i := by
  simp only [utility, stateBeforeStep_update_self, update_self]
  split
  · split
    · exact le_refl _
    · next p _ => exact local_dsic p (v i) (f i).2
  · exact le_refl _

/-! ### (b) No constant competitive ratio against adversarial input -/

/-- If all remaining bidders have value `0`, welfare from position `k`
onward is `0`. -/
private lemma welfareAux_all_zero [Zero F] {n : ℕ}
    (f : Fin n → B × F) (h : List (B × F)) (k : ℕ)
    (hzero : ∀ j : Fin n, k ≤ j.val → (f j).2 = 0) :
    welfareAux A.price f h k = 0 := by
  if hk : k < n then
    rw [welfareAux, dif_pos hk]
    simp only
    have hv : (f ⟨k, hk⟩).2 = 0 := hzero ⟨k, hk⟩ le_rfl
    by_cases hacc : A.price h ≤ ((f ⟨k, hk⟩).2 : WithTop F)
    · rw [if_pos hacc, hv]
    · rw [if_neg hacc]
      exact welfareAux_all_zero f (h ++ [f ⟨k, hk⟩]) (k + 1) fun j hj => by
        exact hzero j (by omega)
  else
    rw [welfareAux, dif_neg hk]
termination_by n - k

/-- **Problem 2.1 (b).** Any auction whose opening price is positive
(in `WithTop F`) can be forced to welfare `0` while `max v > 0`. -/
theorem welfare_can_be_zero [Inhabited B] [Field F] [IsStrictOrderedRing F]
    (hn : 1 ≤ n)
    (hpos : (0 : WithTop F) < A.price []) :
    ∃ f : Fin n → B × F,
      (0 : F) < maxV hn (fun i => (f i).2) ∧ A.welfare f = 0 := by
  have h0n : (0 : ℕ) < n := by omega
  rcases hp : A.price [] with _ | p
  · -- A.price [] = ⊤: bidder 0 has value 1 (rejected), rest 0
    let f : Fin n → B × F := fun i => (default, if i.val = 0 then 1 else 0)
    have hrej : ¬ A.price [] ≤ ((f ⟨0, h0n⟩).2 : WithTop F) := by
      rw [hp]; exact not_le.mpr (WithTop.coe_lt_top _)
    refine ⟨f, ?_, ?_⟩
    · exact lt_of_lt_of_le one_pos (le_maxV hn (fun i => (f i).2) ⟨0, h0n⟩)
    · unfold welfare
      rw [A.welfareAux_reject f [] 0 h0n hrej]
      exact A.welfareAux_all_zero f _ 1 fun j hj => by
        show (if (j : Fin n).val = 0 then (1 : F) else 0) = 0
        exact if_neg (by omega)
  · -- A.price [] = ↑p with 0 < p: bidder 0 has value p/2 (rejected), rest 0
    have hp0 : (0 : F) < p := by rw [hp] at hpos; exact WithTop.coe_lt_coe.mp hpos
    let f : Fin n → B × F := fun i => (default, if i.val = 0 then p / 2 else 0)
    have hrej : ¬ A.price [] ≤ ((f ⟨0, h0n⟩).2 : WithTop F) := by
      rw [hp]; show ¬ (↑p : WithTop F) ≤ ↑(p / 2)
      rw [WithTop.coe_le_coe]; exact not_le.mpr (div_lt_self hp0 one_lt_two)
    refine ⟨f, ?_, ?_⟩
    · exact lt_of_lt_of_le (div_pos hp0 two_pos) (le_maxV hn (fun i => (f i).2) ⟨0, h0n⟩)
    · unfold welfare
      rw [A.welfareAux_reject f [] 0 h0n hrej]
      exact A.welfareAux_all_zero f _ 1 fun j hj => by
        show (if (j : Fin n).val = 0 then p / 2 else (0 : F)) = 0
        exact if_neg (by omega)

/-- **Corollary.** No deterministic online auction with positive opening
price achieves a constant competitive ratio. -/
theorem no_constant_competitive_ratio [Inhabited B] [Field F] [IsStrictOrderedRing F]
    (hn : 1 ≤ n) (hpos : (0 : WithTop F) < A.price []) (c : F)
    (hc : 0 < c) :
    ∃ f : Fin n → B × F,
      (0 : F) < maxV hn (fun i => (f i).2) ∧
      A.welfare f < c * maxV hn (fun i => (f i).2) := by
  obtain ⟨f, hmax, hw⟩ := A.welfare_can_be_zero hn hpos
  exact ⟨f, hmax, by rw [hw]; exact mul_pos hc hmax⟩

end SingleItemAuction

/-! ## Secretary auction -/

namespace Secretary

section AuctionDef
variable {B F : Type*} [LinearOrder F] [Zero F]

/-- The secretary (sample-then-threshold) pricing rule. The first
`⌊n/2⌋` arrivals face price `⊤` (rejected unconditionally); thereafter
the price is the maximum *value* seen so far. No bound `M` is needed:
`⊤` replaces the old `M + 1` observe-phase barrier. -/
def auction (n : ℕ) : SingleItemAuction B F where
  price h :=
    if h.length < n / 2 then ⊤
    else ↑(h.foldl (fun acc (p : B × F) => max acc p.2) 0)

end AuctionDef

/-! ### Competitive ratio (Problem 2.1(c)) -/

variable {B F : Type*} [LinearOrder F] [Field F] [IsStrictOrderedRing F]

open SingleItemAuction

/-- The favourable event: under permutation `σ`, the argmax bidder
arrives in the second half (position ≥ `n/2`) while the second-largest
bidder arrives in the first half (position `< n/2`). -/
structure Favorable {n : ℕ} (v : Fin n → F) (σ : Equiv.Perm (Fin n)) where
  max_pos : Fin n
  second_pos : Fin n
  v_is_max : ∀ j, v j ≤ v (σ max_pos)
  v_is_second : ∀ j, j ≠ σ max_pos → v j ≤ v (σ second_pos)
  v_second_lt_max : v (σ second_pos) < v (σ max_pos)
  max_in_second_half : n / 2 ≤ max_pos.val
  second_in_first_half : second_pos.val < n / 2

/-- Welfare is nonneg for the secretary auction with nonneg valuations. -/
lemma welfare_nonneg {n : ℕ} (g : Fin n → B) (v : Fin n → F)
    (hv_nn : ∀ i, 0 ≤ v i) :
    0 ≤ (auction n).welfare (fun i => (g i, v i)) :=
  (auction n).welfareAux_nonneg _ (fun i => hv_nn i) [] 0

private theorem welfareAux_favorable
    {n : ℕ} (hn : 2 ≤ n) (g : Fin n → B) (v : Fin n → F)
    (hv_inj : Function.Injective v) (hv_nn : ∀ i, 0 ≤ v i)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable v σ)
    (k : ℕ) (hk : k ≤ hσ.max_pos.val)
    (h : List (B × F)) (hlen : h.length = k)
    (hfold_ub : h.foldl (fun acc (p : B × F) => max acc p.2) 0 ≤ v (σ hσ.second_pos))
    (hfold_lb : hσ.second_pos.val < k →
      v (σ hσ.second_pos) ≤ h.foldl (fun acc (p : B × F) => max acc p.2) 0) :
    welfareAux (auction n).price (fun i => (g (σ i), v (σ i))) h k =
      v (σ hσ.max_pos) := by
  set f : Fin n → B × F := fun i => (g (σ i), v (σ i))
  have hk_lt_n : k < n := lt_of_le_of_lt hk hσ.max_pos.isLt
  have h_price_unfold : (auction n).price h =
      if h.length < n / 2 then (⊤ : WithTop F)
      else ↑(h.foldl (fun acc (p : B × F) => max acc p.2) 0) := rfl
  by_cases hk_eq : k = hσ.max_pos.val
  · -- *** ACCEPTANCE at k = max_pos ***
    have hfin_eq : (⟨k, hk_lt_n⟩ : Fin n) = hσ.max_pos := Fin.ext hk_eq
    have h_phase2 : ¬ h.length < n / 2 := by
      rw [hlen]; exact not_lt.mpr (hk_eq ▸ hσ.max_in_second_half)
    have h_accept : (auction n).price h ≤ ((f ⟨k, hk_lt_n⟩).2 : WithTop F) := by
      rw [h_price_unfold, if_neg h_phase2, show (f ⟨k, hk_lt_n⟩).2 = v (σ ⟨k, hk_lt_n⟩) from rfl,
          hfin_eq, WithTop.coe_le_coe]
      exact le_trans hfold_ub (le_of_lt hσ.v_second_lt_max)
    rw [(auction n).welfareAux_accept f h k hk_lt_n h_accept]
    exact congr_arg (v ∘ σ) hfin_eq
  · -- *** REJECTION at k < max_pos ***
    have hk_lt : k < hσ.max_pos.val := Nat.lt_of_le_of_ne hk hk_eq
    have hfin_ne : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.max_pos :=
      fun heq => hk_eq (congrArg Fin.val heq)
    have hσk_ne : σ ⟨k, hk_lt_n⟩ ≠ σ hσ.max_pos := σ.injective.ne hfin_ne
    have hv_k_le : v (σ ⟨k, hk_lt_n⟩) ≤ v (σ hσ.second_pos) := hσ.v_is_second _ hσk_ne
    have h_reject : ¬ (auction n).price h ≤ ((f ⟨k, hk_lt_n⟩).2 : WithTop F) := by
      rw [h_price_unfold, show (f ⟨k, hk_lt_n⟩).2 = v (σ ⟨k, hk_lt_n⟩) from rfl]
      by_cases h_obs : h.length < n / 2
      · rw [if_pos h_obs]; exact WithTop.not_top_le_coe _
      · rw [if_neg h_obs, WithTop.coe_le_coe, not_le]
        have hsv := hσ.second_in_first_half
        have h_sec_lt : hσ.second_pos.val < k := by omega
        have hk_ne_sec : k ≠ hσ.second_pos.val := by omega
        have hfin_ne_sec : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.second_pos :=
          fun heq => hk_ne_sec (congrArg Fin.val heq)
        calc h.foldl (fun acc (p : B × F) => max acc p.2) 0
            ≥ v (σ hσ.second_pos) := hfold_lb h_sec_lt
          _ > v (σ ⟨k, hk_lt_n⟩) :=
            lt_of_le_of_ne hv_k_le (hv_inj.ne (σ.injective.ne hfin_ne_sec))
    rw [(auction n).welfareAux_reject f h k hk_lt_n h_reject]
    have h_new_fold : (h ++ [f ⟨k, hk_lt_n⟩]).foldl
        (fun acc (p : B × F) => max acc p.2) 0 =
        max (h.foldl (fun acc (p : B × F) => max acc p.2) 0)
            (v (σ ⟨k, hk_lt_n⟩)) := by
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    exact welfareAux_favorable hn g v hv_inj hv_nn hσ (k + 1) (by omega)
      (h ++ [f ⟨k, hk_lt_n⟩]) (by simp [hlen])
      (by rw [h_new_fold]; exact max_le hfold_ub hv_k_le)
      (by intro h_sec; rw [h_new_fold]
          rcases Nat.lt_succ_iff_lt_or_eq.mp h_sec with h_lt | h_eq
          · exact le_max_of_le_left (hfold_lb h_lt)
          · have : (⟨k, hk_lt_n⟩ : Fin n) = hσ.second_pos := Fin.ext h_eq.symm
            rw [this]; exact le_max_right _ _)
termination_by hσ.max_pos.val - k
decreasing_by omega

/-- Under the favourable event, the secretary auction allocates to
the argmax bidder, yielding welfare = `maxV v`. -/
lemma welfare_eq_max_of_favorable
    {n : ℕ} (hn : 2 ≤ n) (g : Fin n → B) (v : Fin n → F)
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable v σ) :
    (auction n).welfare (fun i => (g (σ i), v (σ i))) =
      maxV (by omega) v := by
  unfold SingleItemAuction.welfare
  rw [welfareAux_favorable hn g v hv_inj hv_nn hσ 0 (by omega) [] rfl
    (by simp [List.foldl]; exact hv_nn _) (by omega)]
  exact le_antisymm (le_maxV _ v _) (Finset.sup'_le _ _ (fun j _ => hσ.v_is_max j))

/-- The set of permutations satisfying the favourable event. -/
noncomputable def favorableSet
    {n : ℕ} (v : Fin n → F) : Finset (Equiv.Perm (Fin n)) :=
  letI : DecidablePred (fun σ => Nonempty (Favorable v σ)) := Classical.decPred _
  Finset.univ.filter (fun σ => Nonempty (Favorable v σ))

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
private theorem favorableSet_card_lower {n : ℕ} (hn : 2 ≤ n) (v : Fin n → F)
    (hv_inj : Function.Injective v) :
    (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet v).card := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ v hne
  have ha' : ∀ j, v j ≤ v a := fun j => ha j (Finset.mem_univ _)
  have herase : (Finset.univ.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc_mem, hc⟩ := Finset.exists_max_image (Finset.univ.erase a) v herase
  have hca : c ≠ a := (Finset.mem_erase.1 hc_mem).1
  have hc' : ∀ j, j ≠ a → v j ≤ v c := fun j hj =>
    hc j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
  have hac : a ≠ c := fun h => hca h.symm
  have hcltA : v c < v a := by
    refine lt_of_le_of_ne (ha' c) ?_
    intro h
    exact hca (hv_inj h)
  have hchar : ∀ σ : Equiv.Perm (Fin n),
      Nonempty (Favorable v σ) ↔ (n / 2 ≤ (σ⁻¹ a).val ∧ (σ⁻¹ c).val < n / 2) := by
    intro σ
    constructor
    · rintro ⟨fav⟩
      have hmax : σ fav.max_pos = a := by
        apply hv_inj
        exact le_antisymm (ha' _) (fav.v_is_max a)
      have hsec : σ fav.second_pos = c := by
        apply hv_inj
        refine le_antisymm (hc' _ ?_) (fav.v_is_second c ?_)
        · rw [hmax.symm]
          intro h
          have := fav.v_second_lt_max
          rw [σ.injective h] at this
          exact lt_irrefl _ this
        · rw [hmax]
          exact hca
      have hmp : σ⁻¹ a = fav.max_pos := by
        rw [← hmax]; exact σ.symm_apply_apply _
      have hsp : σ⁻¹ c = fav.second_pos := by
        rw [← hsec]; exact σ.symm_apply_apply _
      rw [hmp, hsp]
      exact ⟨fav.max_in_second_half, fav.second_in_first_half⟩
    · rintro ⟨h1, h2⟩
      refine ⟨{
        max_pos := σ⁻¹ a
        second_pos := σ⁻¹ c
        v_is_max := ?_
        v_is_second := ?_
        v_second_lt_max := ?_
        max_in_second_half := h1
        second_in_first_half := h2 }⟩
      · intro j
        rw [show σ (σ⁻¹ a) = a from σ.apply_symm_apply a]
        exact ha' j
      · intro j hj
        rw [show σ (σ⁻¹ a) = a from σ.apply_symm_apply a] at hj
        rw [show σ (σ⁻¹ c) = c from σ.apply_symm_apply c]
        exact hc' j hj
      · rw [show σ (σ⁻¹ a) = a from σ.apply_symm_apply a,
          show σ (σ⁻¹ c) = c from σ.apply_symm_apply c]
        exact hcltA
  have hset_eq : favorableSet v
      = Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          n / 2 ≤ (σ⁻¹ a).val ∧ (σ⁻¹ c).val < n / 2) := by
    unfold favorableSet
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hchar σ
  rw [hset_eq]
  have hreindex : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        n / 2 ≤ (σ⁻¹ a).val ∧ (σ⁻¹ c).val < n / 2)).card
      = (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        n / 2 ≤ (π a).val ∧ (π c).val < n / 2)).card := by
    apply Finset.card_nbij' (fun σ => σ⁻¹) (fun π => π⁻¹)
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
      exact hσ
    · intro π hπ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
        inv_inv] at hπ ⊢
      exact hπ
    · intro σ _; simp
    · intro π _; simp
  rw [hreindex, count_Q hac]

/-- The favourable set has at least `n!/4` elements. -/
lemma favorableSet_card_ge {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → F) (hv_inj : Function.Injective v) :
    (n.factorial : F) ≤ 4 * ((favorableSet v).card : F) := by
  have hlow : (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet v).card :=
    favorableSet_card_lower hn v hv_inj
  have hnat : n.factorial ≤ 4 * (favorableSet v).card :=
    calc n.factorial ≤ 4 * (n - n / 2) * (n / 2) * (n - 2).factorial :=
            factorial_le_four_split n hn
      _ = 4 * ((n - n / 2) * (n / 2) * (n - 2).factorial) := by ring
      _ ≤ 4 * (favorableSet v).card := Nat.mul_le_mul_left _ hlow
  exact_mod_cast hnat

/-- **Problem 2.1 (c).** Under uniformly random arrival, the secretary
rule achieves expected welfare `≥ (1/4) · max v` for distinct valuations.
-/
theorem competitive [LinearOrder B]
    {n : ℕ} (hn : 2 ≤ n) (id : Fin n → B) (v : Fin n → F)
    (hid : Function.Injective id)
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i) :
    (1 / 4 : F) * maxV (by omega) v ≤
      (∑ σ : Equiv.Perm (Fin n),
        (auction n).welfare (fun i => (id (σ i), v (σ i)))) /
          (n.factorial : F) := by
  classical
  set MAX := maxV (show 1 ≤ n by omega) v with hMAX_def
  have hMAX_nn : 0 ≤ MAX :=
    le_trans (hv_nn ⟨0, by omega⟩) (le_maxV _ v _)
  have hwelfare_nn :
      ∀ σ : Equiv.Perm (Fin n),
        0 ≤ (auction n).welfare (fun i => (id (σ i), v (σ i))) :=
    fun σ => welfare_nonneg (id ∘ σ) (v ∘ σ) (fun i => hv_nn _)
  have hwelfare_FS :
      ∀ σ ∈ favorableSet v,
        (auction n).welfare (fun i => (id (σ i), v (σ i))) = MAX := by
    intro σ hσ
    obtain ⟨fav⟩ : Nonempty (Favorable v σ) := (Finset.mem_filter.mp hσ).2
    exact welfare_eq_max_of_favorable hn id v hv_inj hv_nn fav
  have step1 :
      ((favorableSet v).card : F) * MAX ≤
        ∑ σ : Equiv.Perm (Fin n),
          (auction n).welfare (fun i => (id (σ i), v (σ i))) := by
    calc ((favorableSet v).card : F) * MAX
        = ∑ _σ ∈ favorableSet v, MAX := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ favorableSet v,
            (auction n).welfare (fun i => (id (σ i), v (σ i))) :=
          Finset.sum_congr rfl (fun σ hσ => (hwelfare_FS σ hσ).symm)
      _ ≤ ∑ σ : Equiv.Perm (Fin n),
            (auction n).welfare (fun i => (id (σ i), v (σ i))) :=
          Finset.sum_le_univ_sum_of_nonneg (fun σ => hwelfare_nn σ)
  have step2 : (n.factorial : F) ≤ 4 * ((favorableSet v).card : F) :=
    favorableSet_card_ge hn v hv_inj
  have hfact_pos : (0 : F) < (n.factorial : F) := by positivity
  rw [le_div_iff₀ hfact_pos]
  calc (1 / 4 : F) * MAX * (n.factorial : F)
      = MAX * ((1 / 4 : F) * (n.factorial : F)) := by ring
    _ ≤ MAX * ((favorableSet v).card : F) := by
        apply mul_le_mul_of_nonneg_left _ hMAX_nn
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_of_le_mul₀ (by positivity) (by positivity) (by linarith)
    _ = ((favorableSet v).card : F) * MAX := by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
          (auction n).welfare (fun i => (id (σ i), v (σ i))) := step1

end Secretary

end Online.Auction
