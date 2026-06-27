/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Algorithm.Online
import EconCSLib.MechanismDesign.Auction.Transfer
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.Examples.Online.SingleItemAuction

The **online single-item auction** of Roughgarden, *Twenty Lectures on
Algorithmic Game Theory*, Problem 2.1. Bidders arrive one at a time;
whenever the item is still unsold, the auctioneer posts a
take-it-or-leave-it price depending only on prior bids; the current bidder
either accepts (auction concludes) or departs.

We model the auction as a specialisation of the general
`OnlineAlgorithm` framework from `EconCSLib.Algorithm.Online`. The
"no future" constraint of online algorithms is built into the auction
state: a `.unsold history` state carries the rejection history, and the
pricing rule may only see this history — never the current or future
bids.

The numeric type `F` is any linearly ordered field; bids, prices,
valuations, and utilities all live in `F`. Utility is signed because
`vᵢ − pᵢ` can be negative when the alternate bid is above the
posted price.

## Main results

* `dsic` — truthful bidding is (weakly) dominant for every bidder under
  every valuation profile (Problem 2.1(a)).
* `welfare_can_be_zero` / `no_constant_competitive_ratio` — for every
  `n ≥ 1`, any deterministic online auction posting a positive opening
  price can be driven to welfare `0` (while the maximum valuation stays
  positive) by a single adversary, so it achieves no constant fraction of
  the highest valuation (Problem 2.1(b)).
* `Secretary.competitive` — under uniformly random arrival, the
  secretary-style threshold rule achieves expected welfare ≥ `(1/4) · max v`
  for **distinct** valuations (Problem 2.1(c)). Fully proved via the welfare
  characterisation under the favourable event and the exact favourable count.
* `Secretary.competitive_of_nonneg` — the same `(1/4) · max v` guarantee for
  **all** nonneg valuations (ties allowed) and every `n ≥ 1`, provided the
  auction compares bidders by an injective ranking that refines the value order
  (`b i ≤ b j → v i ≤ v j`). The ranking encodes a total order on bidders
  compatible with their valuations; `Secretary.surrogate v` (lexicographic
  `(value, index)`) is a canonical such ranking.
-/

-- The section variables (`A`, `Field`/`LinearOrder`/`IsStrictOrderedRing F`)
-- are deliberately broad; several order-only or list-only lemmas use a subset.
set_option linter.unusedSectionVars false

namespace Online.Auction

open Online Function

variable {F : Type*}

/-- State of an online single-item auction.

* `.unsold history` — item still available; `history` lists prior
  rejected bids in arrival order. This is exactly what an online
  auctioneer is allowed to see when posting the next price.
* `.sold winner price` — item already sold at `price` to bidder `winner`
  (zero-indexed); subsequent steps are no-ops. -/
inductive AuctionState (F : Type*) where
  | unsold (history : List F)
  | sold (winner : ℕ) (price : F)

/-- An online single-item auction is determined by a *pricing rule*: a
function from the history of prior rejected bids to the next posted
price. The "online" property is built into the type: `price`'s argument is
the rejection history alone, so the rule structurally cannot peek at the
current or any future bid. -/
@[ext]
structure SingleItemAuction (F : Type*) where
  /-- Price posted to the next arrival, given the prior rejection history. -/
  price : List F → F

/-- Maximum of a valuation profile: a small wrapper around `Finset.sup'`
that absorbs the nonempty proof so callers do not have to provide it.
Requires `n ≥ 1` to guarantee a witness. Auction-independent — it is the
offline optimum (give the item to the highest valuation) used as the
competitive-ratio benchmark. -/
noncomputable def maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) : F :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ v

lemma le_maxV {n : ℕ} [LinearOrder F] (hn : 1 ≤ n) (v : Fin n → F) (i : Fin n) :
    v i ≤ maxV hn v :=
  Finset.le_sup' v (Finset.mem_univ i)

namespace SingleItemAuction

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F] (A : SingleItemAuction F)

/-- The auction viewed as an `OnlineAlgorithm`. The initial state is the
empty (unsold) history; one step posts `A.price history` to the current
bidder and sells (`some price`, winner position `history.length`) when the
bid clears it, otherwise appends the bid to the history. The end-of-input
input `none` posts no price: an unsold auction stays unsold, a sold one
stays sold.

This single definition is the auction's whole embedding into the
`OnlineAlgorithm` framework — `A.online.run`, `A.online.runStatus`, and the
generic `run_cons_*` lemmas all flow from here. -/
def online : OnlineAlgorithm F (AuctionState F) F where
  init := .unsold []
  step
    | .unsold h, some b =>
        let p := A.price h
        if p ≤ b then (.sold h.length p, some p)
        else (.unsold (h ++ [b]), none)
    | .unsold h, none => (.unsold h, none)
    | .sold w p, _ => (.sold w p, none)

/-- Run `A` on a bid sequence, returning the sale price: `some p` if some
bidder cleared the posted price, `none` if every bidder was rejected. -/
def run (bids : List F) : Option F :=
  (A.online.run A.online.init bids).2

/-- The state immediately *before* bidder `i` is processed: the state
reached by running the bids `b 0, …, b (i.val − 1)` (no end-of-input
step — bidder `i` is the next genuine input). -/
def stateBeforeStep {n : ℕ} (b : Fin n → F) (i : Fin n) : AuctionState F :=
  A.online.runStatus (.unsold [])
    (List.ofFn (fun j : Fin i.val => b ⟨j.val, j.isLt.trans i.isLt⟩))

/-! ### Welfare via direct recursion

`welfare` is defined directly by recursion on the list of bidders (rather
than going through `OnlineAlgorithm.run`) so that small concrete profiles
reduce cleanly under `simp`. This is what makes the adversarial
construction in (b) tractable. -/

/-- Welfare from a starting rejection history `h`, for a list of bidders
given as (valuation, bid) pairs in arrival order: sell to the first
bidder whose bid meets the posted price (yielding their valuation),
otherwise `0`. -/
def welfareFrom (A : SingleItemAuction F) : List F → List (F × F) → F
  | _, []              => 0
  | h, (vi, bi) :: rest =>
      if A.price h ≤ bi then vi
      else welfareFrom A (h ++ [bi]) rest

/-- Social welfare under valuation profile `v` and bid profile `b`. -/
def welfare {n : ℕ} (v b : Fin n → F) : F :=
  A.welfareFrom [] (List.ofFn (fun i : Fin n => (v i, b i)))

@[simp] lemma welfareFrom_nil (h : List F) : A.welfareFrom h [] = 0 := rfl

lemma welfareFrom_cons_accept
    (h : List F) (vi bi : F) (rest : List (F × F))
    (hb : A.price h ≤ bi) :
    A.welfareFrom h ((vi, bi) :: rest) = vi := by
  simp [welfareFrom, hb]

lemma welfareFrom_cons_reject
    (h : List F) (vi bi : F) (rest : List (F × F))
    (hb : ¬ A.price h ≤ bi) :
    A.welfareFrom h ((vi, bi) :: rest) = A.welfareFrom (h ++ [bi]) rest := by
  simp [welfareFrom, hb]

/-- Welfare-from a starting history is nonnegative whenever every
valuation in the pair-list is nonnegative. The auction can only output
either `0` or one of the listed valuations, so the bound is structural. -/
lemma welfareFrom_nonneg (L : List (F × F)) (hL : ∀ p ∈ L, 0 ≤ p.1) :
    ∀ (h : List F), 0 ≤ A.welfareFrom h L := by
  induction L with
  | nil =>
      intro h
      rw [A.welfareFrom_nil]
  | cons p rest ih =>
      intro h
      rcases p with ⟨vi, bi⟩
      have hvi : 0 ≤ vi := hL (vi, bi) (List.mem_cons_self)
      have hrest : ∀ q ∈ rest, 0 ≤ q.1 :=
        fun q hq => hL q (List.mem_cons_of_mem _ hq)
      by_cases hcond : A.price h ≤ bi
      · rw [A.welfareFrom_cons_accept _ _ _ _ hcond]; exact hvi
      · rw [A.welfareFrom_cons_reject _ _ _ _ hcond]
        exact ih hrest (h ++ [bi])

/-- If every listed valuation is zero, the welfare-from is zero: the
auction can only ever output `0` or one of the listed valuations. -/
lemma welfareFrom_eq_zero (L : List (F × F)) (hL : ∀ p ∈ L, p.1 = 0) :
    ∀ (h : List F), A.welfareFrom h L = 0 := by
  induction L with
  | nil => intro h; rw [A.welfareFrom_nil]
  | cons p rest ih =>
      intro h
      rcases p with ⟨vi, bi⟩
      have hvi : vi = 0 := hL (vi, bi) List.mem_cons_self
      have hrest : ∀ q ∈ rest, q.1 = 0 :=
        fun q hq => hL q (List.mem_cons_of_mem _ hq)
      by_cases hcond : A.price h ≤ bi
      · rw [A.welfareFrom_cons_accept _ _ _ _ hcond]; exact hvi
      · rw [A.welfareFrom_cons_reject _ _ _ _ hcond]
        exact ih hrest (h ++ [bi])

/-- Welfare is nonnegative for any auction and any bid profile, whenever
all valuations are nonnegative. -/
lemma welfare_nonneg {n : ℕ} (v b : Fin n → F)
    (hv : ∀ i, 0 ≤ v i) :
    0 ≤ A.welfare v b := by
  unfold welfare
  apply A.welfareFrom_nonneg
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, hi⟩
  rw [← hi]
  exact hv i

/-- Utility of bidder `i` under valuation profile `v` and bid profile `b`:
`v i − p` if bidder `i` wins at price `p`, otherwise `0`. The definition
factors through `stateBeforeStep`, isolating bidder `i`'s view from the
global trajectory — this is what makes DSIC a local property. -/
def utility {n : ℕ} (v b : Fin n → F) (i : Fin n) : F :=
  match A.stateBeforeStep b i with
  | .unsold h => if A.price h ≤ b i then v i - A.price h else 0
  | .sold _ _ => 0

/-! ### (a) DSIC: truthful bidding is (weakly) dominant -/

/-- The state at bidder `i`'s arrival depends only on the bids of bidders
`j < i`, hence is unaffected by changing bidder `i`'s own bid. This
captures the structural reason why the posted price `pᵢ` is independent
of `bᵢ` — the heart of the DSIC argument. -/
lemma stateBeforeStep_update_self {n : ℕ} (b : Fin n → F) (i : Fin n) (x : F) :
    A.stateBeforeStep (update b i x) i = A.stateBeforeStep b i := by
  have hfun :
      (fun j : Fin i.val =>
        Function.update b i x ⟨j.val, j.isLt.trans i.isLt⟩) =
      (fun j : Fin i.val =>
        b ⟨j.val, j.isLt.trans i.isLt⟩) := by
    funext j
    apply Function.update_of_ne
    intro heq
    have hval : j.val = i.val := congrArg Fin.val heq
    exact absurd hval (Nat.ne_of_lt j.isLt)
  unfold stateBeforeStep
  rw [hfun]

/-- The pointwise DSIC step at an `unsold` state: bidding the true
valuation `v` weakly dominates any other bid `b`. The case split is on
whether the posted price (if any) is at most `v`, and whether `b`
clears the posted price. -/
lemma local_dsic_unsold (h : List F) (v b : F) :
    (if A.price h ≤ b then v - A.price h else 0) ≤
    (if A.price h ≤ v then v - A.price h else 0) := by
  by_cases hpv : A.price h ≤ v
  · rw [if_pos hpv]
    by_cases hpb : A.price h ≤ b
    · rw [if_pos hpb]
    · rw [if_neg hpb]; linarith
  · rw [if_neg hpv]
    by_cases hpb : A.price h ≤ b
    · rw [if_pos hpb]; linarith
    · rw [if_neg hpb]

/-- **Problem 2.1 (a): the online single-item auction is DSIC.**

For every pricing rule `A`, every valuation profile `v`, every bid
profile `b`, and every bidder `i`: replacing `b i` with the truthful bid
`v i` does not decrease bidder `i`'s utility. -/
theorem dsic {n : ℕ} (v b : Fin n → F) (i : Fin n) :
    A.utility v b i ≤ A.utility v (update b i (v i)) i := by
  unfold utility
  rw [A.stateBeforeStep_update_self b i (v i)]
  simp only [Function.update_self]
  match A.stateBeforeStep b i with
  | .unsold h => exact A.local_dsic_unsold h (v i) (b i)
  | .sold _ _ => exact le_refl _

/-! ### (a′) DSIC through the library `MechanismWithTransfers` interface

Part (a) above is the self-contained statement. Here we re-express it as
an instance of the library's dominant-strategy incentive-compatibility
predicate `MechanismWithTransfers.isDSIC` (the same one Vickrey's theorem
uses), so the online auction's truthfulness is certified by *exactly* the
general mechanism-design definition — not a bespoke restatement.

The online auction becomes a `MechanismWithTransfers` whose allocation
rule returns the winning position (`Option ℕ`) and whose payment rule
charges the winner the clearing price. The bridge lemma identifies the
induced quasi-linear utility with `utility`, and DSIC then follows from
`dsic` above. -/

/-- Structural dichotomy of the auction run from an arbitrary starting
history `h₀`: either no bidder clears (the run emits nothing and the final
history is `h₀ ++ L`), or some bidder clears at position `w` with
`h₀.length ≤ w < h₀.length + L.length` and the run halts in state
`sold w p`. This is the single fact the bridge needs about the global
trajectory. -/
private lemma auction_dichotomy :
    ∀ (L h₀ : List F),
      A.online.run (.unsold h₀) L = (.unsold (h₀ ++ L), none) ∨
      (∃ w p, A.online.run (.unsold h₀) L = (.sold w p, some p) ∧
         h₀.length ≤ w ∧ w < h₀.length + L.length) := by
  intro L
  induction L with
  | nil => intro h₀; left; rw [List.append_nil]; rfl
  | cons x xs ih =>
      intro h₀
      by_cases hc : A.price h₀ ≤ x
      · -- bidder clears at this step: winner = current history length
        right
        have hstep : A.online.step (.unsold h₀) (some x)
            = (.sold h₀.length (A.price h₀), some (A.price h₀)) := by
          simp [SingleItemAuction.online, hc]
        refine ⟨h₀.length, A.price h₀,
          by rw [OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep], le_refl _, ?_⟩
        simp only [List.length_cons]; omega
      · -- bidder rejected: recurse on the extended history
        have hstep : A.online.step (.unsold h₀) (some x)
            = (.unsold (h₀ ++ [x]), none) := by
          simp [SingleItemAuction.online, hc]
        rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep]
        rcases ih (h₀ ++ [x]) with hrun | ⟨w, p, hrun, hlb, hub⟩
        · left
          rw [hrun, List.append_assoc, List.cons_append, List.nil_append]
        · right
          refine ⟨w, p, hrun, ?_, ?_⟩
          · simp only [List.length_append, List.length_cons, List.length_nil] at hlb ⊢
            omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at hub ⊢
            omega

/-- The prefix `take i` of `List.ofFn b` is exactly the list of the first
`i` bids — the input that `stateBeforeStep b i` runs on. -/
private lemma take_ofFn_eq_pre {n : ℕ} (b : Fin n → F) (i : Fin n) :
    (List.ofFn b).take i.val
      = List.ofFn (fun j : Fin i.val => b ⟨j.val, j.isLt.trans i.isLt⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]

/-- The auction's **final outcome** on the truthful run of bid profile `b`:
`sold w p` if some bidder cleared (winner position `w`, price `p`), else
`unsold _`. This is the global allocation read by the mechanism wrapper. -/
def finalOutcome {n : ℕ} (b : Fin n → F) : AuctionState F :=
  A.online.runStatus (.unsold []) (List.ofFn b)

/-- The auction's end-of-input step preserves the state: it posts no price,
so an unsold auction stays unsold and a sold one stays sold. -/
private lemma step_none_fst (s : AuctionState F) :
    (A.online.step s none).1 = s := by cases s <;> rfl

/-- The auction's end-of-input step never commits a sale. -/
private lemma step_none_snd (s : AuctionState F) :
    (A.online.step s none).2 = none := by cases s <;> rfl

/-- If scanning `xs` from `s` commits **no** sale, the run on `xs ++ ys`
resumes from the state reached after `xs`. (Holds because the auction's
end-of-input step preserves the state, so the terminal state after `xs`
alone is the same resume point.) -/
private lemma run_append_of_result_none :
    ∀ (s : AuctionState F) (xs ys : List F),
      (A.online.run s xs).2 = none →
      A.online.run s (xs ++ ys)
        = A.online.run (A.online.run s xs).1 ys := by
  intro s xs
  induction xs generalizing s with
  | nil => intro ys _; simp only [List.nil_append, OnlineAlgorithm.run_nil, A.step_none_fst]
  | cons r rs ih =>
      intro ys h
      cases hstep : A.online.step s (some r) with
      | mk s' o =>
          cases o with
          | some o' =>
              rw [OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep] at h; simp at h
          | none =>
              rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep,
                  OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep]
              exact ih s' ys h

/-- If scanning `xs` from `s` **commits** a sale, appending more bids does
not change the run: it already halted within `xs`. (Holds because the
end-of-input step never sells, so the only emitting step is inside `xs`.) -/
private lemma run_append_of_result_isSome :
    ∀ (s : AuctionState F) (xs ys : List F),
      (A.online.run s xs).2.isSome →
      A.online.run s (xs ++ ys) = A.online.run s xs := by
  intro s xs
  induction xs generalizing s with
  | nil => intro ys h; rw [OnlineAlgorithm.run_nil, A.step_none_snd] at h; simp at h
  | cons r rs ih =>
      intro ys h
      cases hstep : A.online.step s (some r) with
      | mk s' o =>
          cases o with
          | some o' =>
              simp only [List.cons_append]
              rw [OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep,
                  OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep]
          | none =>
              rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep,
                  OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep]
              exact ih s' ys h

/-- **Bridge lemma.** The auction's global outcome, read at bidder `i`,
yields exactly bidder `i`'s `utility`. Concretely: the winner-and-price
read off `finalOutcome` produces `v i − p` when `i` is the winner and
`0` otherwise — matching the local `stateBeforeStep` definition of
`utility`. This is the key fact connecting the global mechanism view to
the local online one. -/
lemma mech_utility_bridge {n : ℕ} (b v : Fin n → F) (i : Fin n) :
    (match A.finalOutcome b with
     | .sold w p => if w = i.val then v i - p else 0
     | .unsold _ => 0)
    = A.utility v b i := by
  -- `pre` = first `i` bids = the list `stateBeforeStep b i` runs on.
  set pre := List.ofFn (fun j : Fin i.val => b ⟨j.val, j.isLt.trans i.isLt⟩)
    with hpre
  have hstate : A.stateBeforeStep b i
      = (A.online.run (.unsold []) pre).1 := rfl
  have hpre_len : pre.length = i.val := by rw [hpre, List.length_ofFn]
  have hfo : A.finalOutcome b = (A.online.run (.unsold []) (List.ofFn b)).1 := rfl
  rw [hfo]
  -- Split `ofFn b = pre ++ (b i :: drop (i+1))`.
  have hsplit : List.ofFn b = pre ++ (b i :: (List.ofFn b).drop (i.val + 1)) := by
    conv_lhs => rw [← List.take_append_drop i.val (List.ofFn b)]
    rw [take_ofFn_eq_pre, ← hpre]
    congr 1
    have hlen : i.val < (List.ofFn b).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.drop_eq_getElem_cons hlen]
    congr 1
    rw [List.getElem_ofFn]
  rw [hsplit]
  rcases A.auction_dichotomy pre [] with hpre_run | ⟨w, p, hpre_run, _, hub⟩
  · -- No bidder before `i` clears: resume the run from `unsold pre`.
    rw [List.nil_append] at hpre_run
    have hsb : A.stateBeforeStep b i = .unsold pre := by rw [hstate, hpre_run]
    have hnone : (A.online.run (.unsold []) pre).2 = none := by rw [hpre_run]
    rw [A.run_append_of_result_none _ _ _ hnone, hpre_run]
    by_cases hc : A.price pre ≤ b i
    · -- bidder `i` clears: run halts at `sold pre.length (price pre)`.
      have hstep : A.online.step (.unsold pre) (some (b i))
          = (.sold pre.length (A.price pre), some (A.price pre)) := by
        simp [SingleItemAuction.online, hc]
      rw [OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep]
      simp [SingleItemAuction.utility, hsb, hpre_len, hc]
    · -- bidder `i` rejected: any later winner is at position `> i`.
      have hstep : A.online.step (.unsold pre) (some (b i))
          = (.unsold (pre ++ [b i]), none) := by
        simp [SingleItemAuction.online, hc]
      rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep]
      rcases A.auction_dichotomy ((List.ofFn b).drop (i.val + 1)) (pre ++ [b i]) with
        hu | ⟨w, p, hs, hlb, _⟩
      · rw [hu]; simp [SingleItemAuction.utility, hsb, hc]
      · have hwi : i.val < w := by
          simp only [List.length_append, List.length_cons, List.length_nil, hpre_len] at hlb
          omega
        rw [hs]; simp [SingleItemAuction.utility, hsb, hc, show ¬ w = i.val by omega]
  · -- Some bidder before `i` clears: the run already halted within `pre`.
    have hsb : A.stateBeforeStep b i = .sold w p := by rw [hstate, hpre_run]
    have hsome : (A.online.run (.unsold []) pre).2.isSome := by rw [hpre_run]; rfl
    have hwi : w < i.val := by
      simp only [List.length_nil, Nat.zero_add, hpre_len] at hub
      omega
    rw [A.run_append_of_result_isSome _ _ _ hsome, hpre_run]
    simp [SingleItemAuction.utility, hsb, show ¬ w = i.val by omega]

/-! ### (b) No constant-factor competitive ratio against an adversary -/

/-- **Problem 2.1 (b): welfare can be forced to zero.**

For every `n ≥ 1` and every deterministic online auction `A` that posts a
positive opening price (`0 < A.price []`), there is an `n`-bidder valuation
profile on which the maximum valuation is strictly positive yet the
auction's welfare (under truthful bidding) is exactly `0`.

The adversary is a single construction: bidder `0` values the item at
`A.price [] / 2` — just under the posted price, so they are rejected — and
every other bidder values it at `0`. No positive valuation is ever
captured, so welfare is `0`, while the maximum valuation `A.price []/2`
stays positive.

Only the *opening* price needs to be positive; that already rules out the
degenerate giveaway (`A.price [] ≤ 0`, where a lone first bidder wins for
free) which is the sole obstruction at `n = 1`. -/
theorem welfare_can_be_zero (n : ℕ) (hn : 1 ≤ n) (hpos : 0 < A.price []) :
    ∃ v : Fin n → F, 0 < maxV hn v ∧ A.welfare v v = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨Fin.cons (A.price [] / 2) (fun _ => 0), ?_, ?_⟩
  · -- maxV > 0, since bidder 0's valuation is `A.price []/2 > 0`
    have key := le_maxV hn (Fin.cons (A.price [] / 2) (fun _ : Fin m => (0 : F))) 0
    rw [Fin.cons_zero] at key
    exact lt_of_lt_of_le (div_pos hpos two_pos) key
  · -- welfare = 0: bidder 0 is rejected, every later valuation is 0
    unfold welfare
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [A.welfareFrom_cons_reject _ _ _ _ (not_le.mpr (half_lt_self hpos))]
    refine A.welfareFrom_eq_zero _ ?_ _
    intro p hpmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpmem
    rfl

/-- **No constant competitive ratio** (corollary of `welfare_can_be_zero`).
For every `n ≥ 1`, every `c > 0`, and every deterministic online auction
`A` with positive opening price, some `n`-bidder profile has positive
maximum valuation yet welfare strictly below `c · maxV`. -/
theorem no_constant_competitive_ratio (n : ℕ) (hn : 1 ≤ n) (hpos : 0 < A.price [])
    (c : F) (hc : 0 < c) :
    ∃ v : Fin n → F, 0 < maxV hn v ∧ A.welfare v v < c * maxV hn v := by
  obtain ⟨v, hposv, hzero⟩ := A.welfare_can_be_zero n hn hpos
  exact ⟨v, hposv, by rw [hzero]; exact mul_pos hc hposv⟩

/-! ### (a) DSIC via the library mechanism predicate

The auction, packaged as a library `MechanismWithTransfers` (allocation =
winning position, payment = clearing price), satisfies the *general*
`MechanismWithTransfers.isDSIC` predicate — the very definition certifying
Vickrey's second-price auction. The proof reduces to the self-contained
`dsic` above through the `mech_utility_bridge`.

(The mechanism-design layer imported here defines a `scoped` deviation
notation `σ[i ↦ s']`, left unopened, so the many `… []` list literals
above keep their ordinary meaning.) -/

/-- The online single-item auction as a library `MechanismWithTransfers`:
reports are bids in `F`, the allocation is the winning position
(`Option ℕ`, `none` if unsold), and the payment charges the winner the
clearing price (everyone else pays `0`). -/
def mechanism (n : ℕ) : MechanismWithTransfers (Fin n) (fun _ => F) (Option ℕ) F where
  allocationRule b :=
    match A.finalOutcome b with
    | .sold w _ => some w
    | .unsold _ => none
  paymentRule b i :=
    match A.finalOutcome b with
    | .sold w p => if w = i.val then p else 0
    | .unsold _ => 0

/-- The "(value if winner) − payment" combinator, read off any outcome
state, equals the winner-price formula of `mech_utility_bridge`. Stated
over a free state `st` so the case split needs no dependent generalisation. -/
private lemma u_eq_of_state {n : ℕ} (st : AuctionState F) (v : Fin n → F) (i : Fin n) :
    (if (match st with | .sold w _ => some w | .unsold _ => none) = some i.val
        then v i else 0)
      - (match st with | .sold w p => if w = i.val then p else 0 | .unsold _ => 0)
    = (match st with | .sold w p => if w = i.val then v i - p else 0 | .unsold _ => 0) := by
  cases st with
  | sold w p => by_cases hw : w = i.val <;> simp [hw]
  | unsold h => simp

/-- The quasi-linear utility induced by the auction mechanism equals the
local `utility`: the winner gets `vᵢ − p`, everyone else `0`. Immediate
from `mech_utility_bridge` and `u_eq_of_state`. -/
private lemma mech_u_eq_utility {n : ℕ} (b v : Fin n → F) (i : Fin n) :
    (if (A.mechanism n).allocationRule b = some i.val then v i else 0)
      - (A.mechanism n).paymentRule b i = A.utility v b i := by
  rw [← A.mech_utility_bridge b v i]
  exact u_eq_of_state (A.finalOutcome b) v i

/-- **Problem 2.1 (a), library form: the online auction is DSIC.**

This is the *general* `MechanismWithTransfers.isDSIC` predicate — the same
definition certifying Vickrey's second-price auction — instantiated for
the online single-item auction. Truthful bidding `v i` weakly dominates
every alternative report, under the quasi-linear utility
`(value if winner) − payment`. The proof reduces to `dsic` via the
`mech_u_eq_utility` bridge. -/
theorem mechanism_isDSIC {n : ℕ} :
    (A.mechanism n).isDSIC
      (fun (alloc : Option ℕ) (pay : Fin n → F) (v : Fin n → F) (i : Fin n) =>
        (if alloc = some i.val then v i else 0) - pay i) := by
  intro v i s' σ
  simp only [MechanismWithTransfers.toStrategicGame, StrategicGame.deviate]
  rw [A.mech_u_eq_utility, A.mech_u_eq_utility]
  have hd := A.dsic v (Function.update σ i s') i
  rwa [Function.update_idem] at hd

end SingleItemAuction

/-! ### (c) Random arrival: secretary-style guarantee

Under uniformly random arrival there is a constant `c > 0` and a
deterministic online auction whose expected welfare is at least
`c · max v`. The witness is the secretary-style threshold rule:

* in the first `⌊n/2⌋` rounds (the "observe" phase), post a price strictly
  above every legal bid (hence every bidder is rejected and the maximum
  observed bid is recorded);
* in the remaining rounds, post the maximum observed bid as the threshold.

Under truthful bidding the first bidder in the second phase whose
valuation exceeds the recorded threshold wins. With `c = 1/4`, the event
"the argmax bidder arrives in the second half AND the second-largest
bidder arrives in the first half" has probability ≥ 1/4 (a clean
counting argument), and under that event the algorithm precisely
allocates to the argmax bidder, yielding welfare = `max v`.

Because `F` is an ordered field without a top element, the observe phase
requires a known upper bound `M ≥ vᵢ` to post a guaranteed-rejecting
price `M + 1`. The bound is provided as a side input to the auction
family `Secretary.auction n M`; the theorem then holds for every
valuation profile dominated by `M`.

The expectation is modelled as an elementary finite average over
permutations of `Fin n`, avoiding measure-theoretic overhead.
-/

namespace Secretary

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open SingleItemAuction

/-- The secretary-style online auction for `n` bidders, parameterised by
an upper bound `M ≥ vᵢ` on the valuations.

* While the rejection history is shorter than `⌊n/2⌋`, post `M + 1`
  (strictly above every legal bid, so every bidder in this phase is
  rejected and gets appended to history).
* Once at least `⌊n/2⌋` bidders have been seen, post the maximum bid
  observed so far (`h.foldr max 0`).

Sale price ≤ bid is the winning rule of the underlying `SingleItemAuction`. -/
def auction (n : ℕ) (M : F) : SingleItemAuction F where
  price h :=
    if h.length < n / 2 then M + 1
    else h.foldr max 0

/-- The favourable event: under permutation `σ`, the argmax bidder
arrives in the second half (position ≥ `n/2`) while the second-largest
bidder arrives in the first half (position `< n/2`).

`max_pos` is the position of the argmax bidder, `second_pos` the
position of the second-largest. The conditions
`v_is_max` / `v_is_second` pin down `σ max_pos` and `σ second_pos` as
the argmax and second-largest entries, respectively. -/
structure Favorable {n : ℕ} (v : Fin n → F) (σ : Equiv.Perm (Fin n)) where
  /-- Position at which the argmax bidder arrives. -/
  max_pos : Fin n
  /-- Position at which the second-largest bidder arrives. -/
  second_pos : Fin n
  /-- `σ max_pos` is the argmax bidder. -/
  v_is_max : ∀ j, v j ≤ v (σ max_pos)
  /-- `σ second_pos` is the second-largest bidder. -/
  v_is_second : ∀ j, j ≠ σ max_pos → v j ≤ v (σ second_pos)
  /-- The second-largest is strictly smaller than the maximum. -/
  v_second_lt_max : v (σ second_pos) < v (σ max_pos)
  /-- The argmax bidder arrives in the second half. -/
  max_in_second_half : n / 2 ≤ max_pos.val
  /-- The second-largest bidder arrives in the first half. -/
  second_in_first_half : second_pos.val < n / 2

/-- Welfare of the secretary auction is always nonnegative, given
nonnegative valuations. -/
lemma welfare_nonneg {n : ℕ} (M : F) (v b : Fin n → F)
    (hv : ∀ i, 0 ≤ v i) :
    0 ≤ (auction n M).welfare v b :=
  SingleItemAuction.welfare_nonneg (auction n M) v b hv

/-- The price posted in the *observe* phase: `M + 1`, by construction.
This is what guarantees rejection of every first-phase bidder under the
bound `v i ≤ M`. -/
private lemma auction_price_phase1
    {n : ℕ} (M : F) (h : List F) (hh : h.length < n / 2) :
    (auction n M).price h = M + 1 := by
  show (if h.length < n / 2 then M + 1 else h.foldr max 0) = M + 1
  simp [hh]

/-- The price posted in the *threshold* phase: maximum bid seen. -/
private lemma auction_price_phase2
    {n : ℕ} (M : F) (h : List F) (hh : ¬ h.length < n / 2) :
    (auction n M).price h = h.foldr max 0 := by
  show (if h.length < n / 2 then M + 1 else h.foldr max 0) = h.foldr max 0
  simp [hh]

/-- **Phase 1: all bidders rejected.** Processing a list of bids whose
combined length keeps the history strictly below `⌊n/2⌋`, with every bid
bounded by `M`, simply accumulates them into the history without selling.
The continuation `rest` is processed from the extended history. -/
private lemma welfareFrom_phase1
    {n : ℕ} (M : F) (h : List F) (bs : List F) (rest : List (F × F))
    (hbs_le : ∀ b ∈ bs, b ≤ M)
    (hlen : h.length + bs.length ≤ n / 2) :
    (auction n M).welfareFrom h (bs.map (fun b => (b, b)) ++ rest) =
      (auction n M).welfareFrom (h ++ bs) rest := by
  induction bs generalizing h with
  | nil => simp
  | cons b bs ih =>
      have hh_lt : h.length < n / 2 := by
        simp only [List.length_cons] at hlen
        omega
      have hprice : (auction n M).price h = M + 1 :=
        auction_price_phase1 M h hh_lt
      have hb_le_M : b ≤ M := hbs_le b List.mem_cons_self
      have hrej : ¬ (auction n M).price h ≤ b := by
        rw [hprice]; linarith
      simp only [List.map_cons, List.cons_append]
      rw [(auction n M).welfareFrom_cons_reject _ _ _ _ hrej]
      have hbs_le' : ∀ b' ∈ bs, b' ≤ M :=
        fun b' hb' => hbs_le b' (List.mem_cons_of_mem _ hb')
      have hlen' : (h ++ [b]).length + bs.length ≤ n / 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_cons] at *
        omega
      rw [ih _ hbs_le' hlen']
      congr 1
      simp

/-- Helper: `foldr max 0` is bounded by `T` when starting from `0 ≤ T`
and every element is `≤ T`. -/
private lemma foldr_max_le_of_all_le
    (l : List F) (T : F) (hT : 0 ≤ T) (hl : ∀ x ∈ l, x ≤ T) :
    l.foldr max 0 ≤ T := by
  induction l with
  | nil => simpa using hT
  | cons a rest ih =>
      have ha : a ≤ T := hl a List.mem_cons_self
      have hrest : ∀ x ∈ rest, x ≤ T :=
        fun x hx => hl x (List.mem_cons_of_mem _ hx)
      simpa using max_le ha (ih hrest)

/-- Folding `max` from `0` is always nonneg (the seed `0` is a lower
bound and `max` can only go up). -/
private lemma zero_le_foldr_max (l : List F) : (0 : F) ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a rest ih => simpa using le_max_of_le_right ih

/-- Every element of a list is `≤` its `foldr max 0`. -/
private lemma le_foldr_max_of_mem
    (l : List F) (x : F) (hx : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons a rest ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [List.foldr_cons]; exact le_max_left _ _
      · exact (ih hx').trans (by rw [List.foldr_cons]; exact le_max_right _ _)

/-- Algebraic identity: `foldr max 0` distributes over list concatenation. -/
private lemma foldr_max_append
    (l₁ l₂ : List F) :
    (l₁ ++ l₂).foldr max 0 = max (l₁.foldr max 0) (l₂.foldr max 0) := by
  induction l₁ with
  | nil =>
      simp only [List.nil_append, List.foldr_nil]
      exact (max_eq_right (zero_le_foldr_max l₂)).symm
  | cons a rest ih =>
      simp only [List.cons_append, List.foldr_cons, ih, max_assoc]

/-- Appending values bounded by an already-attained max keeps the max. -/
private lemma foldr_max_append_le
    (h bs : List F) (T : F) (hT : 0 ≤ T)
    (hh_eq : h.foldr max 0 = T) (hbs_le : ∀ b ∈ bs, b ≤ T) :
    (h ++ bs).foldr max 0 = T := by
  rw [foldr_max_append, hh_eq]
  exact max_eq_left (foldr_max_le_of_all_le _ _ hT hbs_le)

/-- **Phase 2 reject prefix.** Once the history has reached size at
least `⌊n/2⌋`, any further bid strictly below the current threshold is
rejected and does not raise the threshold, so welfare is unchanged. -/
private lemma welfareFrom_phase2_reject
    {n : ℕ} (M : F) (h : List F) (T : F) (rest : List (F × F))
    (hh_len : ¬ h.length < n / 2)
    (hh_max : h.foldr max 0 = T) (hT_nn : 0 ≤ T)
    (bs : List F) (hbs_lt_T : ∀ b ∈ bs, b < T) :
    (auction n M).welfareFrom h (bs.map (fun b => (b, b)) ++ rest) =
      (auction n M).welfareFrom (h ++ bs) rest := by
  induction bs generalizing h with
  | nil => simp
  | cons b bs ih =>
      have hprice : (auction n M).price h = T := by
        rw [auction_price_phase2 _ _ hh_len, hh_max]
      have hb_lt_T : b < T := hbs_lt_T b List.mem_cons_self
      have hrej : ¬ (auction n M).price h ≤ b := by
        rw [hprice]; linarith
      simp only [List.map_cons, List.cons_append]
      rw [(auction n M).welfareFrom_cons_reject _ _ _ _ hrej]
      have hh'_len : ¬ (h ++ [b]).length < n / 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hh'_max : (h ++ [b]).foldr max 0 = T := by
        have hb_le_T : b ≤ T := le_of_lt hb_lt_T
        apply foldr_max_append_le _ _ _ hT_nn hh_max
        intro x hx
        rcases List.mem_singleton.mp hx with rfl
        exact hb_le_T
      have hbs'_lt : ∀ b' ∈ bs, b' < T :=
        fun b' hb' => hbs_lt_T b' (List.mem_cons_of_mem _ hb')
      rw [ih _ hh'_len hh'_max hbs'_lt]
      congr 1
      simp

/-- Helper: the max bid seen in the first `k` positions is at most `T`
when `T` is an upper bound on every valuation other than the argmax,
and `k ≤ max_pos.val`. -/
private lemma foldr_max_take_le_T
    {n : ℕ} (v : Fin n → F) (σ : Equiv.Perm (Fin n))
    (_hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hσ : Favorable v σ)
    (k : ℕ) (hk : k ≤ hσ.max_pos.val) :
    ((List.ofFn (v ∘ σ)).take k).foldr max 0 ≤ v (σ hσ.second_pos) := by
  apply foldr_max_le_of_all_le _ _ (hv_nn _)
  intro x hx
  rcases List.mem_take_iff_getElem.mp hx with ⟨i, hi_lt, hi_eq⟩
  -- hi_lt : i < min k (List.ofFn _).length
  -- hi_eq : (List.ofFn _)[i] = x
  -- So x = v (σ ⟨i, _⟩)
  rw [List.length_ofFn] at hi_lt
  have hi_lt_n : i < n := by
    have := min_le_right k n
    omega
  rw [← hi_eq, List.getElem_ofFn]
  -- Goal: v (σ ⟨i, hi_lt_n⟩) ≤ v (σ second_pos)
  -- Use: ⟨i, hi_lt_n⟩ ≠ max_pos (since i < k ≤ max_pos.val).
  apply hσ.v_is_second
  intro hcontra
  -- hcontra : σ ⟨i, hi_lt_n⟩ = σ max_pos
  have hi_eq_max : (⟨i, hi_lt_n⟩ : Fin n) = hσ.max_pos := σ.injective hcontra
  have hi_eq_val : i = hσ.max_pos.val := congrArg Fin.val hi_eq_max
  have hi_lt_max : i < hσ.max_pos.val := by
    have := min_le_left k n
    omega
  omega

/-- Helper: when `k > second_pos.val`, the second-largest bid `T` is in
`bids.take k`, so `T ≤ max`. -/
private lemma T_le_foldr_max_take
    {n : ℕ} (v : Fin n → F) (σ : Equiv.Perm (Fin n))
    (hσ : Favorable v σ)
    (k : ℕ) (hk_gt : hσ.second_pos.val < k) (_hk_le : k ≤ n) :
    v (σ hσ.second_pos) ≤ ((List.ofFn (v ∘ σ)).take k).foldr max 0 := by
  apply le_foldr_max_of_mem
  rw [List.mem_take_iff_getElem]
  refine ⟨hσ.second_pos.val, ?_, ?_⟩
  · rw [List.length_ofFn]
    exact lt_min hk_gt hσ.second_pos.isLt
  · rw [List.getElem_ofFn]
    rfl

/-- Helper: the bid at position `k` in the truthful arrival sequence
under permutation `σ`. -/
private lemma bid_at {n : ℕ} (v : Fin n → F) (σ : Equiv.Perm (Fin n))
    (k : ℕ) (hk : k < n) :
    (List.ofFn (v ∘ σ))[k]'(by rw [List.length_ofFn]; exact hk) = v (σ ⟨k, hk⟩) := by
  rw [List.getElem_ofFn]
  rfl

/-- The recursive core of `welfare_eq_max_of_favorable`, generalised to a
*separate* accumulated valuation `w` and compared bid `b`. The auction's
price/threshold/acceptance only ever look at the bid `b`; the value
returned on the winning step is the valuation `w` of that bidder. The
favourable event is on the *bid* profile `b` (which must be injective,
nonnegative, bounded by `M`). For every position `k ≤ max_pos.val`,
processing the auction from a history equal to the first `k` *bids* yields
welfare = `w (σ max_pos)`. Proved by induction on `d = max_pos.val − k`.

The original (`w = b = v`) instance recovers `welfare_eq_max_of_favorable`
for distinct valuations; using a separate `b` that refines `v` powers the
non-injective `competitive_of_nonneg`. -/
private theorem welfareFrom_aux
    {n : ℕ} (M : F) (w b : Fin n → F) (σ : Equiv.Perm (Fin n))
    (hb_inj : Function.Injective b)
    (hb_nn : ∀ i, 0 ≤ b i)
    (hb_le : ∀ i, b i ≤ M)
    (hσ : Favorable b σ) (_hn : 2 ≤ n) :
    ∀ (d k : ℕ), k + d = hσ.max_pos.val →
    (auction n M).welfareFrom
      ((List.ofFn (b ∘ σ)).take k)
      ((List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop k)
    = w (σ hσ.max_pos) := by
  -- The pair list `List.ofFn (fun i => (w (σ i), b (σ i)))` at index `k`.
  have pair_at : ∀ (k : ℕ) (hk : k < n),
      (List.ofFn (fun i : Fin n => (w (σ i), b (σ i))))[k]'(by
        rw [List.length_ofFn]; exact hk)
        = (w (σ ⟨k, hk⟩), b (σ ⟨k, hk⟩)) := by
    intro k hk
    rw [List.getElem_ofFn]
  intro d
  induction d with
  | zero =>
      intro k hk
      have hk_eq : k = hσ.max_pos.val := by omega
      -- We have k = max_pos.val and need to process the accepting bid.
      have hk_lt_n : k < n := by rw [hk_eq]; exact hσ.max_pos.isLt
      -- Split pairs.drop k = (w,b)[k] :: pairs.drop (k+1)
      have hdrop_cons :
          (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop k
            = (w (σ ⟨k, hk_lt_n⟩), b (σ ⟨k, hk_lt_n⟩)) ::
              (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop (k + 1) := by
        have hlen : k < (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        exact pair_at k hk_lt_n
      rw [hdrop_cons]
      -- Now apply welfareFrom_cons_accept with bid = b(σ ⟨k,_⟩)
      have h_phase2 : ¬ ((List.ofFn (b ∘ σ)).take k).length < n / 2 := by
        rw [List.length_take, List.length_ofFn]
        have := hσ.max_in_second_half
        omega
      have h_price :
          (auction n M).price ((List.ofFn (b ∘ σ)).take k) =
          ((List.ofFn (b ∘ σ)).take k).foldr max 0 :=
        auction_price_phase2 M _ h_phase2
      have h_max_le_T :
          ((List.ofFn (b ∘ σ)).take k).foldr max 0 ≤ b (σ hσ.second_pos) :=
        foldr_max_take_le_T b σ hb_inj hb_nn hσ k (hk_eq.le)
      have hfin_eq : (⟨k, hk_lt_n⟩ : Fin n) = hσ.max_pos := Fin.ext hk_eq
      have h_bid_eq : b (σ ⟨k, hk_lt_n⟩) = b (σ hσ.max_pos) := by
        rw [hfin_eq]
      have h_w_eq : w (σ ⟨k, hk_lt_n⟩) = w (σ hσ.max_pos) := by
        rw [hfin_eq]
      have h_accept :
          (auction n M).price ((List.ofFn (b ∘ σ)).take k) ≤ b (σ ⟨k, hk_lt_n⟩) := by
        rw [h_price, h_bid_eq]
        linarith [hσ.v_second_lt_max]
      rw [SingleItemAuction.welfareFrom_cons_accept _ _ _ _ _ h_accept]
      exact h_w_eq
  | succ d ih =>
      intro k hk
      have hk_lt_max : k < hσ.max_pos.val := by omega
      have hk_lt_n : k < n := lt_of_lt_of_le hk_lt_max hσ.max_pos.isLt.le
      have hk_succ_le : (k + 1) + d = hσ.max_pos.val := by omega
      -- Split pairs.drop k = (w,b)[k] :: pairs.drop (k+1)
      have hdrop_cons :
          (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop k
            = (w (σ ⟨k, hk_lt_n⟩), b (σ ⟨k, hk_lt_n⟩)) ::
              (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop (k + 1) := by
        have hlen : k < (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        exact pair_at k hk_lt_n
      rw [hdrop_cons]
      -- Show the current bid is rejected.
      have hk_ne_max : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.max_pos := by
        intro h
        have : k = hσ.max_pos.val := congrArg Fin.val h
        omega
      have h_bid_le_T :
          b (σ ⟨k, hk_lt_n⟩) ≤ b (σ hσ.second_pos) := by
        apply hσ.v_is_second
        intro h
        exact hk_ne_max (σ.injective h)
      have h_reject : ¬ (auction n M).price ((List.ofFn (b ∘ σ)).take k) ≤
                      b (σ ⟨k, hk_lt_n⟩) := by
        by_cases hphase1 : k < n / 2
        · have hphase1_len : ((List.ofFn (b ∘ σ)).take k).length < n / 2 := by
            rw [List.length_take, List.length_ofFn]; omega
          rw [auction_price_phase1 M _ hphase1_len]
          have h_bid_le_M : b (σ ⟨k, hk_lt_n⟩) ≤ M := hb_le _
          linarith
        · push Not at hphase1
          have h_phase2_len : ¬ ((List.ofFn (b ∘ σ)).take k).length < n / 2 := by
            rw [List.length_take, List.length_ofFn]; omega
          rw [auction_price_phase2 M _ h_phase2_len]
          -- price = (take k).foldr max 0. We need to show this > bid.
          -- Since k ≥ n/2 > second_pos.val, we have second_pos.val < k,
          -- so T = b(σ second_pos) is in (take k), so T ≤ max.
          have h_sec_lt_k : hσ.second_pos.val < k := by
            have := hσ.second_in_first_half
            omega
          have hT_le_max :
              b (σ hσ.second_pos) ≤ ((List.ofFn (b ∘ σ)).take k).foldr max 0 :=
            T_le_foldr_max_take b σ hσ k h_sec_lt_k (le_of_lt hk_lt_n)
          -- And bid < T strictly (since k ≠ max_pos and k ≠ second_pos)
          have hk_ne_sec : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.second_pos := by
            intro h
            have : k = hσ.second_pos.val := congrArg Fin.val h
            omega
          have h_bid_lt_T : b (σ ⟨k, hk_lt_n⟩) < b (σ hσ.second_pos) := by
            apply lt_of_le_of_ne h_bid_le_T
            intro h
            have hσ_eq : b (σ ⟨k, hk_lt_n⟩) = b (σ hσ.second_pos) := h
            have : (⟨k, hk_lt_n⟩ : Fin n) = hσ.second_pos :=
              σ.injective (hb_inj hσ_eq)
            exact hk_ne_sec this
          linarith
      rw [SingleItemAuction.welfareFrom_cons_reject _ _ _ _ _ h_reject]
      -- Now history = take k ++ [bid] = take (k+1). Apply IH.
      have htake_succ :
          (List.ofFn (b ∘ σ)).take k ++ [b (σ ⟨k, hk_lt_n⟩)] =
          (List.ofFn (b ∘ σ)).take (k + 1) := by
        have hlen : k < (List.ofFn (b ∘ σ)).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.take_add_one, List.getElem?_eq_getElem hlen,
            bid_at b σ k hk_lt_n]
        rfl
      rw [htake_succ]
      exact ih (k + 1) hk_succ_le

/-- **Generalised key lemma.** Under the favourable event *of the bid
profile `b`*, the secretary auction allocates the item to the
bid-argmax bidder `σ max_pos`, yielding welfare equal to that bidder's
*valuation* `w (σ max_pos)` — even when `w` and `b` differ. The original
lemma is the diagonal `w = b = v`; using a separate `b` that refines
`v` (e.g. `b = surrogate v`, `w = v`) drives the non-injective
competitive bound. -/
lemma welfare_eq_argmax_of_favorable
    {n : ℕ} (hn : 2 ≤ n) (M : F) (w b : Fin n → F)
    (hb_inj : Function.Injective b)
    (hb_nn : ∀ i, 0 ≤ b i)
    (hb_le : ∀ i, b i ≤ M)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable b σ) :
    (auction n M).welfare (w ∘ σ) (b ∘ σ) = w (σ hσ.max_pos) := by
  -- Apply the recursive core at `k = 0`, `d = max_pos.val`.
  unfold SingleItemAuction.welfare
  have hpair : (fun i : Fin n => ((w ∘ σ) i, (b ∘ σ) i))
            = (fun i : Fin n => (w (σ i), b (σ i))) := rfl
  rw [hpair]
  -- welfareFrom [] = welfareFrom ((bids).take 0) ((pairs).drop 0)
  have htake0 : (List.ofFn (b ∘ σ)).take 0 = [] := List.take_zero
  have hdrop0 : (List.ofFn (fun i : Fin n => (w (σ i), b (σ i)))).drop 0
              = List.ofFn (fun i : Fin n => (w (σ i), b (σ i))) := List.drop_zero
  rw [show ([] : List F) = (List.ofFn (b ∘ σ)).take 0 from htake0.symm,
      ← hdrop0]
  exact welfareFrom_aux M w b σ hb_inj hb_nn hb_le hσ hn hσ.max_pos.val 0
    (by omega)

/-- **Key combinatorial lemma.** Under the favourable event the
secretary auction allocates the item to the argmax bidder, yielding
welfare equal to the maximum valuation. The diagonal (`w = b = v`)
instance of `welfare_eq_argmax_of_favorable`. -/
lemma welfare_eq_max_of_favorable
    {n : ℕ} (hn : 2 ≤ n) (M : F) (v : Fin n → F)
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hv_le : ∀ i, v i ≤ M)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable v σ) :
    (auction n M).welfare (v ∘ σ) (v ∘ σ) = maxV (by omega) v := by
  -- First reduce `maxV v` to the argmax bidder's valuation.
  have hmaxV_eq : maxV (show 1 ≤ n by omega) v = v (σ hσ.max_pos) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _
      exact hσ.v_is_max j
    · exact le_maxV _ v (σ hσ.max_pos)
  rw [hmaxV_eq]
  exact welfare_eq_argmax_of_favorable hn M v v hv_inj hv_nn hv_le hσ

/-- The set of permutations satisfying the favourable event. -/
noncomputable def favorableSet
    {n : ℕ} (v : Fin n → F) : Finset (Equiv.Perm (Fin n)) :=
  letI : DecidablePred (fun σ => Nonempty (Favorable v σ)) := Classical.decPred _
  Finset.univ.filter (fun σ => Nonempty (Favorable v σ))

/-- The elementary natural-number inequality at the heart of
`favorableSet_card_ge`: for every `n ≥ 2`,
`n! ≤ 4 · (n − ⌊n/2⌋) · ⌊n/2⌋ · (n − 2)!`. Proved by `omega` after
expanding the factorial. -/
private lemma factorial_le_four_split (n : ℕ) (hn : 2 ≤ n) :
    n.factorial ≤ 4 * (n - n / 2) * (n / 2) * (n - 2).factorial := by
  have hfac : n.factorial = n * (n - 1) * (n - 2).factorial := by
    rcases n with _ | _ | n
    · omega
    · omega
    · simp [Nat.factorial_succ]
      ring
  rw [hfac]
  -- Goal: n * (n - 1) * (n - 2)! ≤ 4 * (n - n/2) * (n/2) * (n - 2)!
  have hk : 4 * (n - n / 2) * (n / 2) ≥ n * (n - 1) := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = m + m, m ≥ 1
      have hm_ge : 1 ≤ m := by omega
      have hn2 : n / 2 = m := by omega
      have hsub : n - n / 2 = m := by omega
      have hn_eq : n = 2 * m := by omega
      rw [hsub, hn2, hn_eq]
      -- Goal: 4 * m * m ≥ 2 * m * (2 * m - 1)
      have hsub' : 2 * m - 1 + 1 = 2 * m := by omega
      nlinarith [hm_ge, hsub']
    · -- n = 2m + 1
      have hn2 : n / 2 = m := by omega
      have hsub : n - n / 2 = m + 1 := by omega
      have hn_eq : n = 2 * m + 1 := hm
      rw [hsub, hn2, hn_eq]
      -- Goal: 4 * (m + 1) * m ≥ (2 * m + 1) * (2 * m + 1 - 1)
      have hsub' : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hsub']
      nlinarith
  exact Nat.mul_le_mul_right _ hk

/-! #### Cardinality of the favourable set

The favourable set has exactly `(n - n/2) · (n/2) · (n-2)!` permutations;
we prove the `≤` direction, which is what the competitive bound needs. -/

/-- For distinct `a ≠ c` and distinct `x ≠ y` in any type with decidable
equality, there is a permutation sending `a ↦ x` and `c ↦ y`. -/
private lemma exists_perm_two {α : Type*} [DecidableEq α] {a c x y : α}
    (hac : a ≠ c) (hxy : x ≠ y) :
    ∃ ρ : Equiv.Perm α, ρ a = x ∧ ρ c = y := by
  classical
  -- t sends a ↦ x; let c' = t c, then swap c' y fixes x and sends c' ↦ y.
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
  -- The filter card equals the card of the subtype {f // ∀ z, ¬p z → f z = z}.
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
  -- Now: (Fintype.card (Subtype p))! = (n - 2)!
  congr 1
  rw [Fintype.card_subtype]
  -- #{z | z ≠ a ∧ z ≠ c} = n - 2
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
  -- Partition Q over the pair (π a, π c) ∈ SH ×ˢ FH.
  have hmaps : (↑(Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      n / 2 ≤ (π a).val ∧ (π c).val < n / 2)) : Set (Equiv.Perm (Fin n))).MapsTo
        (fun π => (π a, π c)) (↑(SH ×ˢ FH)) := by
    intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hSH, hFH,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hπ.1, hπ.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  -- Each fiber over (x, y) with x ∈ SH, y ∈ FH has card (n-2)!.
  have hfib : ∀ p ∈ SH ×ˢ FH,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
          n / 2 ≤ (π a).val ∧ (π c).val < n / 2) |>.filter
          (fun π => (π a, π c) = p)).card = (n - 2).factorial := by
    rintro ⟨x, y⟩ hp
    simp only [hSH, hFH, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    have hxy : x ≠ y := by
      intro h; rw [h] at hp; omega
    -- The double filter equals the single fiber filter π a = x ∧ π c = y.
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

/-- **Target.** The favourable set has at least `(n - n/2) · (n/2) · (n-2)!`
permutations. (Equality in fact holds; a lower bound is all we need.) -/
theorem favorableSet_card_lower {n : ℕ} (hn : 2 ≤ n) (v : Fin n → F)
    (hv_inj : Function.Injective v) :
    (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet v).card := by
  classical
  -- Step 1: argmax a and second-largest c.
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
  -- Step 2: characterize favourability by inverse positions.
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
  -- Step 3: rewrite favorableSet as a filter on inverse positions.
  have hset_eq : favorableSet v
      = Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          n / 2 ≤ (σ⁻¹ a).val ∧ (σ⁻¹ c).val < n / 2) := by
    unfold favorableSet
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hchar σ
  rw [hset_eq]
  -- Step 4: reindex by σ ↦ σ⁻¹.
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


/-- **Key combinatorial lemma (deferred).** The favourable event has
probability at least `1/4`: equivalently, four times its cardinality is
at least `n!`.

Proof sketch (deferred):
* Each `σ` in the favourable set is uniquely determined by:
  - its image of the `argmax` bidder (some `r ∈ secondHalf`),
  - its image of the `secondargmax` bidder (some `s ∈ firstHalf`),
  - and the way it permutes the remaining `n − 2` positions.
* So `|Favorable| = (n − ⌊n/2⌋) · ⌊n/2⌋ · (n − 2)!`. The above
  `factorial_le_four_split` then gives `4 · |Favorable| ≥ n!`.

The counting step is standard combinatorics but its Lean formalisation
requires either:
* constructing the explicit equivalence
  `favorableSet ≃ secondHalf × firstHalf × Perm (Fin (n − 2))`, or
* invoking a Mathlib lemma on the cardinality of permutations with
  prescribed images (e.g. via `Equiv.Perm.viaFintypeEmbedding` /
  `Finset.card_filter_eq_sum`).

Either route is a self-contained 80–120-line proof; the `welfare`
side of (c) is fully proved above, so this combinatorial counting is
the only remaining piece. -/
lemma favorableSet_card_ge {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → F) (hv_inj : Function.Injective v) :
    (n.factorial : F) ≤ 4 * ((favorableSet v).card : F) := by
  -- `n! ≤ 4·(n−n/2)·(n/2)·(n−2)!` (arithmetic) and
  -- `(n−n/2)·(n/2)·(n−2)! ≤ |favorableSet|` (counting), combined over ℕ then cast.
  have hlow : (n - n / 2) * (n / 2) * (n - 2).factorial ≤ (favorableSet v).card :=
    favorableSet_card_lower hn v hv_inj
  have hnat : n.factorial ≤ 4 * (favorableSet v).card :=
    calc n.factorial ≤ 4 * (n - n / 2) * (n / 2) * (n - 2).factorial :=
            factorial_le_four_split n hn
      _ = 4 * ((n - n / 2) * (n / 2) * (n - 2).factorial) := by ring
      _ ≤ 4 * (favorableSet v).card := Nat.mul_le_mul_left _ hlow
  exact_mod_cast hnat

/-! #### Tie-breaking surrogate

To remove the injectivity hypothesis we replace the real-valued bids by a
*rank surrogate* that breaks value ties by bidder index. The surrogate is
injective and refines `v`'s order, so the favourable-event counting and
welfare characterisation (which need an injective bid profile) apply
verbatim, while on the favourable event the captured bidder is a true
`v`-argmax. -/

/-- The strict tie-broken order on bidders: `v i < v j`, or equal values
with a smaller index. This is the lexicographic order on `(v ·, ·)`,
written out to avoid `Prod.Lex` typeclass plumbing. -/
private def slt {n : ℕ} (v : Fin n → F) (i j : Fin n) : Prop :=
  v i < v j ∨ (v i = v j ∧ i.val < j.val)

instance decidableSlt {n : ℕ} (v : Fin n → F) (i j : Fin n) :
    Decidable (slt v i j) := by
  unfold slt; infer_instance

private lemma slt_irrefl {n : ℕ} (v : Fin n → F) (i : Fin n) : ¬ slt v i i := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

private lemma slt_trans {n : ℕ} (v : Fin n → F) {i j k : Fin n}
    (hij : slt v i j) (hjk : slt v j k) : slt v i k := by
  rcases hij with h1 | ⟨h1, h1'⟩ <;> rcases hjk with h2 | ⟨h2, h2'⟩
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, lt_trans h1' h2'⟩

/-- Tie-broken order is total: any two distinct bidders are comparable. -/
private lemma slt_total {n : ℕ} (v : Fin n → F) (i j : Fin n) :
    slt v i j ∨ i = j ∨ slt v j i := by
  rcases lt_trichotomy (v i) (v j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy i.val j.val with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Fin.ext h'))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- `slt` implies `≤` on values: a smaller tie-broken key has no larger value. -/
private lemma slt_le_v {n : ℕ} (v : Fin n → F) {i j : Fin n}
    (h : slt v i j) : v i ≤ v j := by
  rcases h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- The rank surrogate: number of bidders strictly below `i` in the
tie-broken order, cast into `F`. Ranks are `0, …, n-1`. -/
noncomputable def surrogate {n : ℕ} (v : Fin n → F) (i : Fin n) : F :=
  ((Finset.univ.filter (fun j => slt v j i)).card : F)

/-- `surrogate` is strictly monotone for the tie-broken order. -/
private lemma surrogate_lt_of_slt {n : ℕ} (v : Fin n → F) {i j : Fin n}
    (h : slt v i j) : surrogate v i < surrogate v j := by
  unfold surrogate
  have hsub : Finset.univ.filter (fun k => slt v k i)
      ⊆ Finset.univ.filter (fun k => slt v k j) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact slt_trans v hk h
  have hi_mem : i ∈ Finset.univ.filter (fun k => slt v k j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  have hi_not : i ∉ Finset.univ.filter (fun k => slt v k i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact slt_irrefl v i
  have hcard : (Finset.univ.filter (fun k => slt v k i)).card
      < (Finset.univ.filter (fun k => slt v k j)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨i, hi_mem, hi_not⟩)
  exact_mod_cast hcard

/-- The surrogate refines `v`: `surrogate v i ≤ surrogate v j → v i ≤ v j`. -/
lemma surrogate_refines {n : ℕ} (v : Fin n → F) {i j : Fin n}
    (h : surrogate v i ≤ surrogate v j) : v i ≤ v j := by
  rcases slt_total v i j with hlt | heq | hgt
  · exact slt_le_v v hlt
  · rw [heq]
  · exact absurd (surrogate_lt_of_slt v hgt) (not_lt.2 h)

/-- The surrogate is injective. -/
lemma surrogate_injective {n : ℕ} (v : Fin n → F) :
    Function.Injective (surrogate v) := by
  intro i j h
  rcases slt_total v i j with hlt | heq | hgt
  · exact absurd h.ge (not_le.2 (surrogate_lt_of_slt v hlt))
  · exact heq
  · exact absurd h.le (not_le.2 (surrogate_lt_of_slt v hgt))

/-- The surrogate is nonnegative. -/
lemma surrogate_nonneg {n : ℕ} (v : Fin n → F) (i : Fin n) :
    0 ≤ surrogate v i := by
  unfold surrogate; exact Nat.cast_nonneg _

/-- Every surrogate value is strictly below `(n : F)`, hence the auction
run with bound `M' = (n : F)` rejects every phase-1 bidder. -/
lemma surrogate_lt_n {n : ℕ} (v : Fin n → F) (i : Fin n) :
    surrogate v i < (n : F) := by
  unfold surrogate
  have hsub : Finset.univ.filter (fun j => slt v j i) ⊆ Finset.univ.erase i := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Finset.mem_erase]
    exact ⟨fun hki => slt_irrefl v i (hki ▸ hk), Finset.mem_univ _⟩
  have hcard : (Finset.univ.filter (fun j => slt v j i)).card ≤ n - 1 := by
    calc (Finset.univ.filter (fun j => slt v j i)).card
        ≤ (Finset.univ.erase i).card := Finset.card_le_card hsub
      _ = n - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin]
  have hn1 : (n : ℕ) ≥ 1 := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have : ((Finset.univ.filter (fun j => slt v j i)).card : F) ≤ ((n - 1 : ℕ) : F) := by
    exact_mod_cast hcard
  have hcast : ((n - 1 : ℕ) : F) < (n : F) := by
    have : ((n - 1 : ℕ) : F) = (n : F) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [this]; linarith
  linarith

/-- On a favourable event for a bid profile `b` that refines `v`
(`b i ≤ b j → v i ≤ v j`), the captured bidder has the maximum
`v`-valuation: `v (σ max_pos) = maxV v`. -/
private lemma v_argmax_of_favorable_refinement
    {n : ℕ} (_hn : 2 ≤ n) (v b : Fin n → F)
    (hb_refines : ∀ i j, b i ≤ b j → v i ≤ v j)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable b σ) :
    v (σ hσ.max_pos) = maxV (show 1 ≤ n by omega) v := by
  apply le_antisymm
  · exact le_maxV _ v (σ hσ.max_pos)
  · apply Finset.sup'_le
    intro j _
    exact hb_refines j (σ hσ.max_pos) (hσ.v_is_max j)

/-- **Problem 2.1 (c′) core: 1/4-competitive for `n ≥ 2` with any
compatible bid ranking.**

The secretary auction with bid profile `b` and bound `M = n` achieves
expected welfare `≥ (1/4) · max v`, provided `b` is injective, nonneg,
bounded by `n`, and refines `v`'s order. -/
private lemma competitive_of_nonneg_ge_two
    {n : ℕ} (hn : 2 ≤ n) (v b : Fin n → F)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hb_inj : Function.Injective b)
    (hb_nn : ∀ i, 0 ≤ b i)
    (hb_le : ∀ i, b i ≤ (n : F))
    (hb_refines : ∀ i j, b i ≤ b j → v i ≤ v j) :
    (1 / 4 : F) * maxV (by omega) v ≤
      (∑ σ : Equiv.Perm (Fin n),
        (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ)) /
          (n.factorial : F) := by
  classical
  set MAX := maxV (show 1 ≤ n by omega) v with hMAX_def
  have hMAX_nn : 0 ≤ MAX :=
    le_trans (hv_nn ⟨0, by omega⟩) (le_maxV _ v _)
  -- Welfare is nonneg pointwise (valuations are nonneg).
  have hwelfare_nn :
      ∀ σ : Equiv.Perm (Fin n), 0 ≤ (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) :=
    fun σ => SingleItemAuction.welfare_nonneg (auction n (n : F)) (v ∘ σ) (b ∘ σ)
                (fun i => hv_nn _)
  -- Welfare equals MAX on the surrogate's favourable set.
  have hwelfare_FS :
      ∀ σ ∈ favorableSet b, (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) = MAX := by
    intro σ hσ
    obtain ⟨fav⟩ : Nonempty (Favorable b σ) := (Finset.mem_filter.mp hσ).2
    rw [welfare_eq_argmax_of_favorable hn (n : F) v b hb_inj hb_nn hb_le fav]
    rw [hMAX_def]
    exact v_argmax_of_favorable_refinement hn v b hb_refines fav
  -- Step 1: Σ welfare ≥ |FS| * MAX.
  have step1 :
      ((favorableSet b).card : F) * MAX ≤
      ∑ σ : Equiv.Perm (Fin n), (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) := by
    calc ((favorableSet b).card : F) * MAX
        = ∑ _σ ∈ favorableSet b, MAX := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ favorableSet b, (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) :=
            Finset.sum_congr rfl (fun σ hσ => (hwelfare_FS σ hσ).symm)
      _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intros σ _ _; exact hwelfare_nn σ
  -- Step 2: n! ≤ 4 * |FS| (favourable count, b is injective).
  have step2 : (n.factorial : F) ≤ 4 * ((favorableSet b).card : F) :=
    favorableSet_card_ge hn b hb_inj
  -- Combine and divide.
  have hfact_pos : (0 : F) < (n.factorial : F) := by
    exact_mod_cast Nat.factorial_pos n
  rw [le_div_iff₀ hfact_pos]
  calc (1 / 4 : F) * MAX * (n.factorial : F)
      = MAX * ((1 / 4 : F) * (n.factorial : F)) := by ring
    _ ≤ MAX * ((favorableSet b).card : F) := by
          apply mul_le_mul_of_nonneg_left _ hMAX_nn
          linarith
    _ = ((favorableSet b).card : F) * MAX := by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ) := step1

/-- **Problem 2.1 (c′): the 1/4 guarantee for all nonneg `v` with a
compatible tiebreak, down to a single bidder.**

For any nonneg valuation profile `v` and any bid profile `b` that is
injective, nonneg, bounded by the number of bidders, and *refines*
`v`'s order (`b i ≤ b j → v i ≤ v j`), the secretary auction
`Secretary.auction n n` achieves expected welfare `≥ (1/4) · max v`.

The bid profile `b` encodes a total order on bidders compatible with
their valuations — e.g. the lexicographic `(value, index)` ranking
given by `Secretary.surrogate v`. The theorem is agnostic to *which*
compatible order is used. -/
theorem competitive_of_nonneg
    {n : ℕ} (hn : 1 ≤ n) (v b : Fin n → F)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hb_inj : Function.Injective b)
    (hb_nn : ∀ i, 0 ≤ b i)
    (hb_lt : ∀ i, b i < (n : F))
    (hb_refines : ∀ i j, b i ≤ b j → v i ≤ v j) :
    (1 / 4 : F) * maxV hn v ≤
      (∑ σ : Equiv.Perm (Fin n),
        (auction n (n : F)).welfare (v ∘ σ) (b ∘ σ)) /
          (n.factorial : F) := by
  rcases eq_or_lt_of_le hn with rfl | h2
  · -- n = 1: the single bidder clears the zero opening price.
    simp only [Nat.cast_one]
    have hprice0 : (auction 1 (1 : F)).price [] = 0 := by simp [Secretary.auction]
    have hcond : (auction 1 (1 : F)).price [] ≤ b 0 := by rw [hprice0]; exact hb_nn 0
    have hwf : (auction 1 (1 : F)).welfare v b = v 0 := by
      simp only [SingleItemAuction.welfare, List.ofFn_succ, List.ofFn_zero]
      rw [SingleItemAuction.welfareFrom_cons_accept _ _ _ _ _ hcond]
    have hmax : maxV hn v = v 0 := by
      apply le_antisymm
      · apply Finset.sup'_le; intro j _; rw [Subsingleton.elim j (0 : Fin 1)]
      · exact le_maxV _ v 0
    have hsum : (∑ σ : Equiv.Perm (Fin 1),
          (auction 1 (1 : F)).welfare (v ∘ σ) (b ∘ σ)) = v 0 := by
      have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
        ext σ; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim σ 1
      rw [huniv, Finset.sum_singleton]
      simp only [Equiv.Perm.coe_one, Function.comp_id]
      exact hwf
    have hf1 : (Nat.factorial 1 : F) = 1 := by norm_num
    rw [hsum, hmax, hf1, div_one]
    linarith [hv_nn (0 : Fin 1)]
  · exact competitive_of_nonneg_ge_two h2 v b hv_nn hb_inj hb_nn
      (fun i => le_of_lt (hb_lt i)) hb_refines

/-- **Problem 2.1 (c): a 1/4-competitive deterministic online auction
under uniformly random arrival.**

For every `n ≥ 2`, every bound `M`, and every nonnegative pairwise
distinct valuation profile `v` bounded by `M`, the secretary auction
`Secretary.auction n M` achieves expected welfare at least
`(1/4) · max v`, where the expectation is the elementary average over
permutations of `Fin n`.

The proof combines two lemmas — the cardinality lower bound on the
favourable event and the welfare characterisation under that event —
each of which is currently deferred. -/
theorem competitive
    {n : ℕ} (hn : 2 ≤ n) (M : F) (v : Fin n → F)
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hv_le : ∀ i, v i ≤ M) :
    (1 / 4 : F) * maxV (by omega) v ≤
      (∑ σ : Equiv.Perm (Fin n),
        (auction n M).welfare (v ∘ σ) (v ∘ σ)) /
          (n.factorial : F) := by
  -- Set up: MAX = maxV, and its non-negativity from nonneg valuations.
  set MAX := maxV (show 1 ≤ n by omega) v with hMAX_def
  have hMAX_nn : 0 ≤ MAX :=
    le_trans (hv_nn ⟨0, by omega⟩) (le_maxV _ v _)
  -- Welfare is nonneg pointwise.
  have hwelfare_nn :
      ∀ σ : Equiv.Perm (Fin n), 0 ≤ (auction n M).welfare (v ∘ σ) (v ∘ σ) :=
    fun σ => SingleItemAuction.welfare_nonneg (auction n M) (v ∘ σ) (v ∘ σ)
                (fun i => hv_nn _)
  -- Welfare equals MAX on the favourable set.
  have hwelfare_FS :
      ∀ σ ∈ favorableSet v, (auction n M).welfare (v ∘ σ) (v ∘ σ) = MAX := by
    classical
    intro σ hσ
    obtain ⟨F⟩ : Nonempty (Favorable v σ) := (Finset.mem_filter.mp hσ).2
    simpa [hMAX_def]
      using welfare_eq_max_of_favorable hn M v hv_inj hv_nn hv_le F
  -- Step 1: Σ welfare ≥ |FS| * MAX.
  have step1 :
      ((favorableSet v).card : F) * MAX ≤
      ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare (v ∘ σ) (v ∘ σ) := by
    calc ((favorableSet v).card : F) * MAX
        = ∑ _σ ∈ favorableSet v, MAX := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ favorableSet v, (auction n M).welfare (v ∘ σ) (v ∘ σ) :=
            Finset.sum_congr rfl (fun σ hσ => (hwelfare_FS σ hσ).symm)
      _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare (v ∘ σ) (v ∘ σ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intros σ _ _; exact hwelfare_nn σ
  -- Step 2: n! ≤ 4 * |FS| (from `favorableSet_card_ge`).
  have step2 : (n.factorial : F) ≤ 4 * ((favorableSet v).card : F) :=
    favorableSet_card_ge hn v hv_inj
  -- Combine: (1/4) * MAX * n! ≤ |FS| * MAX ≤ Σ. Then divide.
  have hfact_pos : (0 : F) < (n.factorial : F) := by
    exact_mod_cast Nat.factorial_pos n
  rw [le_div_iff₀ hfact_pos]
  calc (1 / 4 : F) * MAX * (n.factorial : F)
      = MAX * ((1 / 4 : F) * (n.factorial : F)) := by ring
    _ ≤ MAX * ((favorableSet v).card : F) := by
          apply mul_le_mul_of_nonneg_left _ hMAX_nn
          have : (1 / 4 : F) * (n.factorial : F) ≤ (favorableSet v).card :=
            by linarith
          linarith
    _ = ((favorableSet v).card : F) * MAX := by ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare (v ∘ σ) (v ∘ σ) := step1

end Secretary

end Online.Auction
