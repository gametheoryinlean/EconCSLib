/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Algorithm.Online
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

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

variable {B F : Type*} [LinearOrder F] [Zero F]

/-- The secretary (sample-then-threshold) pricing rule. The first
`⌊n/2⌋` arrivals face price `⊤` (rejected unconditionally); thereafter
the price is the maximum *value* seen so far. No bound `M` is needed:
`⊤` replaces the old `M + 1` observe-phase barrier. -/
def auction (n : ℕ) : SingleItemAuction B F where
  price h :=
    if h.length < n / 2 then ⊤
    else ↑(h.foldl (fun acc (p : B × F) => max acc p.2) 0)

/-! ### Competitive ratio (Problem 2.1(c)) -/

variable [Field F] [IsStrictOrderedRing F]

-- Favorable, favorableSet, favorableSet_card_ge, welfare lemmas
-- will be filled in when porting part (c).

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
  sorry

end Secretary

end Online.Auction
