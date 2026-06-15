/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Algorithm.Online
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
* `no_constant_competitive_ratio` — for adversarial valuations, no
  deterministic online auction achieves a constant fraction of the
  highest valuation: a two-bidder adversary suffices (Problem 2.1(b)).
* `Secretary.competitive` — under uniformly random arrival, the
  secretary-style threshold rule achieves expected welfare ≥ `(1/4) · max v`
  (Problem 2.1(c)). The main combinatorial sub-lemmas are stated and the
  high-level proof is laid out; some sub-lemmas are deferred via `sorry`.
-/

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

namespace SingleItemAuction

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F] (A : SingleItemAuction F)

/-- One step of the auction: given the current state and the current input,
produce the next state and the answer for this bidder (`some p` =
bidder wins at price `p`, `none` = bidder rejected, item already sold, or
end of input). The current bidder's 0-indexed position equals
`history.length` in the `.unsold` case. The end-of-input input `none`
posts no price: an unsold auction simply stays unsold. -/
def step : AuctionState F → Option F → AuctionState F × Option F
  | .unsold h, some b =>
      let p := A.price h
      if p ≤ b then (.sold h.length p, some p)
      else (.unsold (h ++ [b]), none)
  | .unsold h, none => (.unsold h, none)
  | .sold w p, _ => (.sold w p, none)

/-- Embed `A` as a generic `OnlineAlgorithm`. The per-step output is the
sale price `F`: `step` emits `some p` exactly when the current bidder
wins (halting the run), and `none` otherwise. -/
def toOnlineAlgorithm : OnlineAlgorithm F (AuctionState F) F where
  init := .unsold []
  step := A.step

/-- Run `A` on a bid sequence, returning the sale price: `some p` if some
bidder cleared the posted price, `none` if every bidder was rejected. -/
def run (bids : List F) : Option F :=
  A.toOnlineAlgorithm.run A.toOnlineAlgorithm.init bids

/-- The state immediately *before* bidder `i` is processed: the state
reached by running the bids `b 0, …, b (i.val − 1)` (no end-of-input
step — bidder `i` is the next genuine input). -/
def stateBeforeStep {n : ℕ} (b : Fin n → F) (i : Fin n) : AuctionState F :=
  A.toOnlineAlgorithm.runState (.unsold [])
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
      (A.toOnlineAlgorithm.run (.unsold h₀) L = none ∧
         A.toOnlineAlgorithm.runState (.unsold h₀) L = .unsold (h₀ ++ L)) ∨
      (∃ w p, A.toOnlineAlgorithm.run (.unsold h₀) L = some p ∧
         A.toOnlineAlgorithm.runState (.unsold h₀) L = .sold w p ∧
         h₀.length ≤ w ∧ w < h₀.length + L.length) := by
  intro L
  induction L with
  | nil => intro h₀; exact Or.inl ⟨rfl, by simp⟩
  | cons x xs ih =>
      intro h₀
      by_cases hc : A.price h₀ ≤ x
      · -- bidder clears at this step: winner = current history length
        right
        have hstep : A.toOnlineAlgorithm.step (.unsold h₀) (some x)
            = (.sold h₀.length (A.price h₀), some (A.price h₀)) := by
          show A.step (.unsold h₀) (some x) = _
          simp [SingleItemAuction.step, hc]
        refine ⟨h₀.length, A.price h₀, ?_, ?_, le_refl _, ?_⟩
        · rw [OnlineAlgorithm.run_cons_some _ _ _ _ _ _ hstep]
        · rw [OnlineAlgorithm.runState_cons_some _ _ _ _ _ _ hstep]
        · simp
      · -- bidder rejected: recurse on the extended history
        have hstep : A.toOnlineAlgorithm.step (.unsold h₀) (some x)
            = (.unsold (h₀ ++ [x]), none) := by
          show A.step (.unsold h₀) (some x) = _
          simp [SingleItemAuction.step, hc]
        rcases ih (h₀ ++ [x]) with ⟨hn, hs⟩ | ⟨w, p, hrun, hs, hlb, hub⟩
        · left
          rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep,
              OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep]
          refine ⟨hn, ?_⟩
          rw [hs, List.append_assoc, List.cons_append, List.nil_append]
        · right
          refine ⟨w, p, ?_, ?_, ?_, ?_⟩
          · rw [OnlineAlgorithm.run_cons_none _ _ _ _ _ hstep]; exact hrun
          · rw [OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep]; exact hs
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
  A.toOnlineAlgorithm.runState (.unsold []) (List.ofFn b)

/-- A `sold` state is absorbing: once the item is sold, every later bid
leaves the state unchanged. -/
private lemma runState_from_sold (w : ℕ) (p : F) :
    ∀ (L : List F), A.toOnlineAlgorithm.runState (.sold w p) L = .sold w p := by
  intro L
  induction L with
  | nil => rfl
  | cons x xs ih =>
      have hstep : A.toOnlineAlgorithm.step (.sold w p) (some x) = (.sold w p, none) := rfl
      rw [OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep]; exact ih

/-- If the run on `xs` already halts in `sold w p`, appending more bids
keeps the halting state at `sold w p` (`sold` absorbs). This replaces the
generic "halt freezes state" lemma, which no longer holds once `run` takes
an end-of-input step. -/
private lemma runState_append_eq_self_of_sold (w : ℕ) (p : F) :
    ∀ (s : AuctionState F) (xs ys : List F),
      A.toOnlineAlgorithm.runState s xs = .sold w p →
      A.toOnlineAlgorithm.runState s (xs ++ ys) = .sold w p := by
  intro s xs
  induction xs generalizing s with
  | nil =>
      intro ys h
      simp only [List.nil_append]
      rw [OnlineAlgorithm.runState_nil] at h
      rw [h]; exact A.runState_from_sold w p ys
  | cons r rs ih =>
      intro ys h
      cases hstep : A.toOnlineAlgorithm.step s (some r) with
      | mk s' o =>
          cases o with
          | some o' =>
              rw [OnlineAlgorithm.runState_cons_some _ _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [OnlineAlgorithm.runState_cons_some _ _ _ _ _ _ hstep]; exact h
          | none =>
              rw [OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep] at h
              simp only [List.cons_append]
              rw [OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep]
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
  unfold finalOutcome
  -- `pre` = first `i` bids = the list `stateBeforeStep b i` runs on.
  set pre := List.ofFn (fun j : Fin i.val => b ⟨j.val, j.isLt.trans i.isLt⟩)
    with hpre
  have hstate : A.stateBeforeStep b i
      = A.toOnlineAlgorithm.runState (.unsold []) pre := rfl
  have hpre_len : pre.length = i.val := by rw [hpre, List.length_ofFn]
  -- Split `ofFn b = pre ++ (b i :: drop (i+1))`.
  have hsplit : List.ofFn b = pre ++ (b i :: (List.ofFn b).drop (i.val + 1)) := by
    conv_lhs => rw [← List.take_append_drop i.val (List.ofFn b)]
    rw [take_ofFn_eq_pre, ← hpre]
    congr 1
    have hlen : i.val < (List.ofFn b).length := by rw [List.length_ofFn]; exact i.isLt
    rw [List.drop_eq_getElem_cons hlen]
    congr 1
    rw [List.getElem_ofFn]
  rcases A.auction_dichotomy pre [] with ⟨hnone, hunsold⟩ | ⟨w, p, hrun, hsold, _, hub⟩
  · -- No bidder before `i` clears: continue the run from `unsold pre`.
    rw [List.nil_append] at hunsold
    have hsb : A.stateBeforeStep b i = .unsold pre := by rw [hstate, hunsold]
    rw [hsplit, A.toOnlineAlgorithm.runState_append_of_forall_none _ _ _ hnone, hunsold]
    unfold SingleItemAuction.utility
    by_cases hc : A.price pre ≤ b i
    · -- bidder `i` clears: run halts at `sold pre.length (price pre)`.
      have hstep : A.toOnlineAlgorithm.step (.unsold pre) (some (b i))
          = (.sold pre.length (A.price pre), some (A.price pre)) := by
        show A.step (.unsold pre) (some (b i)) = _
        simp [SingleItemAuction.step, hc]
      simp only [OnlineAlgorithm.runState_cons_some _ _ _ _ _ _ hstep, hsb, hpre_len,
        if_pos rfl, hc, if_true]
    · -- bidder `i` rejected: any later winner is at position `> i`.
      have hstep : A.toOnlineAlgorithm.step (.unsold pre) (some (b i))
          = (.unsold (pre ++ [b i]), none) := by
        show A.step (.unsold pre) (some (b i)) = _
        simp [SingleItemAuction.step, hc]
      rw [OnlineAlgorithm.runState_cons_none _ _ _ _ _ hstep]
      rcases A.auction_dichotomy ((List.ofFn b).drop (i.val + 1)) (pre ++ [b i]) with
        ⟨_, hu⟩ | ⟨w, p, _, hs, hlb, _⟩
      · simp only [hu, hsb, hc, if_false]
      · have hwi : i.val < w := by
          simp only [List.length_append, List.length_cons, List.length_nil, hpre_len] at hlb
          omega
        simp only [hs, hsb, hc, if_false, if_neg (show ¬ w = i.val by omega)]
  · -- Some bidder before `i` clears: `sold` absorbs, so later bids don't move it.
    have hsb : A.stateBeforeStep b i = .sold w p := by rw [hstate, hsold]
    have hwi : w < i.val := by
      simp only [List.length_nil, Nat.zero_add, hpre_len] at hub
      omega
    rw [hsplit, A.runState_append_eq_self_of_sold w p (.unsold []) pre _ hsold]
    unfold SingleItemAuction.utility
    simp only [hsb, if_neg (show ¬ w = i.val by omega)]

/-! ### (b) No constant-factor competitive ratio against an adversary -/

/-- Welfare on a two-bidder profile, fully expanded. The branch structure
mirrors the auction's two-step behaviour: bidder 0 wins iff their bid
clears the initial posted price `A.price []`; otherwise bidder 1 wins iff
their bid clears the price posted given the history `[b 0]`. -/
private lemma welfare_two (v b : Fin 2 → F) :
    A.welfare v b =
      (if A.price [] ≤ b 0 then v 0
       else if A.price [b 0] ≤ b 1 then v 1
       else 0) := by
  unfold welfare
  have hlist :
      List.ofFn (fun i : Fin 2 => (v i, b i)) = [(v 0, b 0), (v 1, b 1)] := rfl
  rw [hlist]
  by_cases h0 : A.price [] ≤ b 0
  · rw [A.welfareFrom_cons_accept _ _ _ _ h0, if_pos h0]
  · rw [A.welfareFrom_cons_reject _ _ _ _ h0, if_neg h0]
    simp only [List.nil_append]
    by_cases h1 : A.price [b 0] ≤ b 1
    · rw [A.welfareFrom_cons_accept _ _ _ _ h1, if_pos h1]
    · rw [A.welfareFrom_cons_reject _ _ _ _ h1, if_neg h1]
      rfl

/-- **Problem 2.1 (b): no constant-factor competitive ratio is achievable.**

For every constant `c > 0` and every deterministic online auction `A`,
there exists a two-bidder valuation profile on which the maximum
valuation is strictly positive yet the auction's welfare (under truthful
bidding) is strictly less than `c · max v`.

The adversary splits on the sign of `A.price []`. If positive, the first
bidder underbids it (and bidder 2 has valuation zero), so nobody whose
valuation matters wins. If non-positive, the first bidder is given
valuation zero and wins immediately at a non-positive price, locking out
a unit valuation in slot two. -/
theorem no_constant_competitive_ratio (c : F) (hc : 0 < c)
    (A : SingleItemAuction F) :
    ∃ v : Fin 2 → F, 0 < max (v 0) (v 1) ∧
      A.welfare v v < c * max (v 0) (v 1) := by
  by_cases hp : 0 < A.price []
  · -- Adversary: v 0 = (A.price [])/2, v 1 = 0.
    refine ⟨![A.price [] / 2, 0], ?_, ?_⟩
    · -- 0 < max (A.price []/2) 0
      have hhalf : (0 : F) < A.price [] / 2 := div_pos hp two_pos
      have e0 : (![A.price [] / 2, 0] : Fin 2 → F) 0 = A.price [] / 2 := by simp
      have e1 : (![A.price [] / 2, 0] : Fin 2 → F) 1 = 0 := by simp
      rw [e0, e1, max_eq_left hhalf.le]
      exact hhalf
    · -- welfare < c * max
      have hhalf : (0 : F) < A.price [] / 2 := div_pos hp two_pos
      have e0 : (![A.price [] / 2, 0] : Fin 2 → F) 0 = A.price [] / 2 := by simp
      have e1 : (![A.price [] / 2, 0] : Fin 2 → F) 1 = 0 := by simp
      rw [A.welfare_two, e0, e1, max_eq_left hhalf.le]
      have hbid0 : ¬ A.price [] ≤ A.price [] / 2 := not_le.mpr (half_lt_self hp)
      rw [if_neg hbid0]
      have hzero :
          (if A.price [A.price [] / 2] ≤ (0 : F) then (0 : F) else 0) = 0 := by
        split_ifs <;> rfl
      rw [hzero]
      exact mul_pos hc hhalf
  · -- A.price [] ≤ 0. Adversary: v 0 = 0, v 1 = 1.
    push Not at hp
    refine ⟨![0, 1], ?_, ?_⟩
    · have e0 : (![0, 1] : Fin 2 → F) 0 = 0 := by simp
      have e1 : (![0, 1] : Fin 2 → F) 1 = 1 := by simp
      rw [e0, e1, max_eq_right zero_le_one]
      exact one_pos
    · have e0 : (![0, 1] : Fin 2 → F) 0 = 0 := by simp
      have e1 : (![0, 1] : Fin 2 → F) 1 = 1 := by simp
      rw [A.welfare_two, e0, e1, max_eq_right zero_le_one]
      rw [if_pos hp, mul_one]
      exact hc

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

/-- Maximum of the valuations: a small wrapper around `Finset.sup'`
that absorbs the nonempty proof so callers do not have to provide it.
Requires `n ≥ 1` to guarantee a witness. -/
noncomputable def maxV {n : ℕ} (hn : 1 ≤ n) (v : Fin n → F) : F :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ v

lemma le_maxV {n : ℕ} (hn : 1 ≤ n) (v : Fin n → F) (i : Fin n) :
    v i ≤ maxV hn v :=
  Finset.le_sup' v (Finset.mem_univ i)

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
      · simpa using le_max_left _ _
      · exact (ih hx').trans (by simpa using le_max_right _ _)

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
    (hv_inj : Function.Injective v)
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
    (k : ℕ) (hk_gt : hσ.second_pos.val < k) (hk_le : k ≤ n) :
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

/-- The recursive core of `welfare_eq_max_of_favorable`. For every
position `k ≤ max_pos.val`, processing the auction from a history
equal to the first `k` bids yields welfare = `v (σ max_pos)`. Proved by
induction on `d = max_pos.val − k`. -/
private theorem welfareFrom_aux
    {n : ℕ} (M : F) (v : Fin n → F) (σ : Equiv.Perm (Fin n))
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hv_le : ∀ i, v i ≤ M)
    (hσ : Favorable v σ) (hn : 2 ≤ n) :
    ∀ (d k : ℕ), k + d = hσ.max_pos.val →
    (auction n M).welfareFrom
      ((List.ofFn (v ∘ σ)).take k)
      (((List.ofFn (v ∘ σ)).drop k).map (fun b => (b, b)))
    = v (σ hσ.max_pos) := by
  intro d
  induction d with
  | zero =>
      intro k hk
      have hk_eq : k = hσ.max_pos.val := by omega
      -- We have k = max_pos.val and need to process the accepting bid.
      have hk_lt_n : k < n := by rw [hk_eq]; exact hσ.max_pos.isLt
      -- Split bids.drop k = bids[k] :: bids.drop (k+1)
      have hdrop_cons :
          (List.ofFn (v ∘ σ)).drop k = v (σ ⟨k, hk_lt_n⟩) ::
            (List.ofFn (v ∘ σ)).drop (k + 1) := by
        have hlen : k < (List.ofFn (v ∘ σ)).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        exact bid_at v σ k hk_lt_n
      rw [hdrop_cons]
      simp only [List.map_cons]
      -- Now apply welfareFrom_cons_accept with bid = v(σ ⟨k,_⟩)
      have h_phase2 : ¬ ((List.ofFn (v ∘ σ)).take k).length < n / 2 := by
        rw [List.length_take, List.length_ofFn]
        have := hσ.max_in_second_half
        omega
      have h_price :
          (auction n M).price ((List.ofFn (v ∘ σ)).take k) =
          ((List.ofFn (v ∘ σ)).take k).foldr max 0 :=
        auction_price_phase2 M _ h_phase2
      have h_max_le_T :
          ((List.ofFn (v ∘ σ)).take k).foldr max 0 ≤ v (σ hσ.second_pos) :=
        foldr_max_take_le_T v σ hv_inj hv_nn hσ k (hk_eq.le)
      have hfin_eq : (⟨k, hk_lt_n⟩ : Fin n) = hσ.max_pos := Fin.ext hk_eq
      have h_bid_eq : v (σ ⟨k, hk_lt_n⟩) = v (σ hσ.max_pos) := by
        rw [hfin_eq]
      have h_accept :
          (auction n M).price ((List.ofFn (v ∘ σ)).take k) ≤ v (σ ⟨k, hk_lt_n⟩) := by
        rw [h_price, h_bid_eq]
        linarith [hσ.v_second_lt_max]
      rw [SingleItemAuction.welfareFrom_cons_accept _ _ _ _ _ h_accept]
      exact h_bid_eq
  | succ d ih =>
      intro k hk
      have hk_lt_max : k < hσ.max_pos.val := by omega
      have hk_lt_n : k < n := lt_of_lt_of_le hk_lt_max hσ.max_pos.isLt.le
      have hk_succ_le : (k + 1) + d = hσ.max_pos.val := by omega
      -- Split bids.drop k = bids[k] :: bids.drop (k+1)
      have hdrop_cons :
          (List.ofFn (v ∘ σ)).drop k = v (σ ⟨k, hk_lt_n⟩) ::
            (List.ofFn (v ∘ σ)).drop (k + 1) := by
        have hlen : k < (List.ofFn (v ∘ σ)).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        exact bid_at v σ k hk_lt_n
      rw [hdrop_cons]
      simp only [List.map_cons]
      -- Show the current bid is rejected.
      have hk_ne_max : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.max_pos := by
        intro h
        have : k = hσ.max_pos.val := congrArg Fin.val h
        omega
      have h_bid_le_T :
          v (σ ⟨k, hk_lt_n⟩) ≤ v (σ hσ.second_pos) := by
        apply hσ.v_is_second
        intro h
        exact hk_ne_max (σ.injective h)
      have h_reject : ¬ (auction n M).price ((List.ofFn (v ∘ σ)).take k) ≤
                      v (σ ⟨k, hk_lt_n⟩) := by
        by_cases hphase1 : k < n / 2
        · have hphase1_len : ((List.ofFn (v ∘ σ)).take k).length < n / 2 := by
            rw [List.length_take, List.length_ofFn]; omega
          rw [auction_price_phase1 M _ hphase1_len]
          have h_bid_le_M : v (σ ⟨k, hk_lt_n⟩) ≤ M := hv_le _
          linarith
        · push Not at hphase1
          have h_phase2_len : ¬ ((List.ofFn (v ∘ σ)).take k).length < n / 2 := by
            rw [List.length_take, List.length_ofFn]; omega
          rw [auction_price_phase2 M _ h_phase2_len]
          -- price = (take k).foldr max 0. We need to show this > bid.
          -- Since k ≥ n/2 > second_pos.val, we have second_pos.val < k,
          -- so T = v(σ second_pos) is in (take k), so T ≤ max.
          have h_sec_lt_k : hσ.second_pos.val < k := by
            have := hσ.second_in_first_half
            omega
          have hT_le_max :
              v (σ hσ.second_pos) ≤ ((List.ofFn (v ∘ σ)).take k).foldr max 0 :=
            T_le_foldr_max_take v σ hσ k h_sec_lt_k (le_of_lt hk_lt_n)
          -- And bid < T strictly (since k ≠ max_pos and k ≠ second_pos)
          have hk_ne_sec : (⟨k, hk_lt_n⟩ : Fin n) ≠ hσ.second_pos := by
            intro h
            have : k = hσ.second_pos.val := congrArg Fin.val h
            omega
          have h_bid_lt_T : v (σ ⟨k, hk_lt_n⟩) < v (σ hσ.second_pos) := by
            apply lt_of_le_of_ne h_bid_le_T
            intro h
            have hσ_eq : σ ⟨k, hk_lt_n⟩ = σ hσ.second_pos := hv_inj h
            have : (⟨k, hk_lt_n⟩ : Fin n) = hσ.second_pos := σ.injective hσ_eq
            exact hk_ne_sec this
          linarith
      rw [SingleItemAuction.welfareFrom_cons_reject _ _ _ _ _ h_reject]
      -- Now history = take k ++ [bid] = take (k+1). Apply IH.
      have htake_succ :
          (List.ofFn (v ∘ σ)).take k ++ [v (σ ⟨k, hk_lt_n⟩)] =
          (List.ofFn (v ∘ σ)).take (k + 1) := by
        have hlen : k < (List.ofFn (v ∘ σ)).length := by
          rw [List.length_ofFn]; exact hk_lt_n
        rw [List.take_add_one, List.getElem?_eq_getElem hlen,
            bid_at v σ k hk_lt_n]
        rfl
      rw [htake_succ]
      exact ih (k + 1) hk_succ_le

/-- **Key combinatorial lemma.** Under the favourable event the
secretary auction allocates the item to the argmax bidder, yielding
welfare equal to the maximum valuation.

Proof outline:
1. First phase (positions `< n/2`): every bidder is rejected by
   `welfareFrom_phase1` (price `M + 1` strictly above every bid).
2. After the first phase the history contains the first `n/2` bids of
   `v ∘ σ`. Because the favourable event places `σ max_pos` in the
   second half, the maximum first-phase bid equals `v (σ second_pos)`.
3. Second phase: the threshold stays equal to `v (σ second_pos)` since
   any further rejected bid is strictly smaller.
4. The first second-phase bidder clearing the threshold is `σ max_pos`,
   so welfare is `v (σ max_pos)`, which equals `maxV v`. -/
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
  -- Apply the recursive core at `k = 0`, `d = max_pos.val`.
  unfold SingleItemAuction.welfare
  have hmap : List.ofFn (fun i : Fin n => ((v ∘ σ) i, (v ∘ σ) i))
            = (List.ofFn (v ∘ σ)).map (fun b => (b, b)) := by
    rw [List.map_ofFn]; rfl
  rw [hmap]
  -- welfareFrom [] = welfareFrom (take 0) ((drop 0).map …)
  have htake0 : (List.ofFn (v ∘ σ)).take 0 = [] := List.take_zero
  have hdrop0 : (List.ofFn (v ∘ σ)).drop 0 = List.ofFn (v ∘ σ) := List.drop_zero
  rw [show ([] : List F) = (List.ofFn (v ∘ σ)).take 0 from htake0.symm]
  rw [show (List.ofFn (v ∘ σ)).map (fun b => (b, b))
        = ((List.ofFn (v ∘ σ)).drop 0).map (fun b => (b, b)) from by rw [hdrop0]]
  exact welfareFrom_aux M v σ hv_inj hv_nn hv_le hσ hn hσ.max_pos.val 0
    (by omega)

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
    · simp [Nat.factorial_succ, Nat.succ_sub_one]
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
  sorry

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
