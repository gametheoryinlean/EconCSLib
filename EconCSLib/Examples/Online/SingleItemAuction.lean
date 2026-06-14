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

/-- One step of the auction: given the current state and the current bid,
produce the next state and the answer for this bidder (`some p` =
bidder wins at price `p`, `none` = bidder rejected or item already sold).
The current bidder's 0-indexed position equals `history.length` in the
`.unsold` case. -/
def step : AuctionState F → F → AuctionState F × Option F
  | .unsold h, b =>
      let p := A.price h
      if p ≤ b then (.sold h.length p, some p)
      else (.unsold (h ++ [b]), none)
  | .sold w p, _ => (.sold w p, none)

/-- Embed `A` as a generic `OnlineAlgorithm`. -/
def toOnlineAlgorithm : OnlineAlgorithm F (AuctionState F) (Option F) where
  init := .unsold []
  step := A.step

/-- Run `A` on a bid sequence: `(final state, answers in arrival order)`. -/
def run (bids : List F) : AuctionState F × List (Option F) :=
  A.toOnlineAlgorithm.run A.toOnlineAlgorithm.init bids

/-- The state immediately *before* bidder `i` is processed: the result of
driving the state machine on bids `b 0, …, b (i.val − 1)`. -/
def stateBeforeStep {n : ℕ} (b : Fin n → F) (i : Fin n) : AuctionState F :=
  (A.toOnlineAlgorithm.run (.unsold [])
    (List.ofFn (fun j : Fin i.val => b ⟨j.val, j.isLt.trans i.isLt⟩))).1

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
    push_neg at hp
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

/-- **Key combinatorial lemma (deferred).** Under the favourable event the
secretary auction allocates the item to the argmax bidder, yielding
welfare equal to the maximum valuation.

Proof sketch:
1. In the first phase (positions `< n/2`) the posted price is `M + 1`,
   strictly above every bid `vᵢ ≤ M`, so every first-phase bidder is
   rejected and their bid joins the history.
2. After the first phase the history contains the first-half bids; by
   the favourable event the maximum first-half bid equals
   `v (σ second_pos)` (the second-largest valuation overall) because the
   argmax is in the second half.
3. In the second phase the posted price stays equal to that maximum: any
   rejected bid is `< v (σ second_pos)` so does not raise the max.
4. The first second-phase bidder whose bid clears the threshold is the
   argmax bidder, by injectivity of `v` and the strict gap
   `v (σ second_pos) < v (σ max_pos)`. The auction sells to them at
   price `v (σ second_pos)`, but welfare is the *valuation* of the
   winner, so the welfare equals `v (σ max_pos) = max v`. -/
lemma welfare_eq_max_of_favorable
    {n : ℕ} (hn : 2 ≤ n) (M : F) (v : Fin n → F)
    (hv_inj : Function.Injective v)
    (hv_nn : ∀ i, 0 ≤ v i)
    (hv_le : ∀ i, v i ≤ M)
    {σ : Equiv.Perm (Fin n)} (hσ : Favorable v σ) :
    (auction n M).welfare v (v ∘ σ) = maxV (by omega) v := by
  sorry

/-- The set of permutations satisfying the favourable event. -/
noncomputable def favorableSet
    {n : ℕ} (v : Fin n → F) : Finset (Equiv.Perm (Fin n)) :=
  letI : DecidablePred (fun σ => Nonempty (Favorable v σ)) := Classical.decPred _
  Finset.univ.filter (fun σ => Nonempty (Favorable v σ))

/-- **Key combinatorial lemma (deferred).** The favourable event has
probability at least `1/4`: equivalently, four times its cardinality is
at least `n!`.

Proof sketch: count `|Favorable|` by fixing
`(σ max_pos, σ second_pos)` to range over `(secondHalf × firstHalf)`
and permuting the remaining `n − 2` positions freely. This yields
`|Favorable| = (n − n/2) · (n/2) · (n − 2)!`, and the inequality
`4 · (n − n/2) · (n/2) · (n − 2)! ≥ n!` holds for every `n ≥ 2` by an
elementary case split on the parity of `n`. -/
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
        (auction n M).welfare v (v ∘ σ)) /
          (n.factorial : F) := by
  -- Set up: MAX = maxV, and its non-negativity from nonneg valuations.
  set MAX := maxV (show 1 ≤ n by omega) v with hMAX_def
  have hMAX_nn : 0 ≤ MAX :=
    le_trans (hv_nn ⟨0, by omega⟩) (le_maxV _ v _)
  -- Welfare is nonneg pointwise.
  have hwelfare_nn :
      ∀ σ : Equiv.Perm (Fin n), 0 ≤ (auction n M).welfare v (v ∘ σ) :=
    fun σ => SingleItemAuction.welfare_nonneg (auction n M) v (v ∘ σ) hv_nn
  -- Welfare equals MAX on the favourable set.
  have hwelfare_FS :
      ∀ σ ∈ favorableSet v, (auction n M).welfare v (v ∘ σ) = MAX := by
    classical
    intro σ hσ
    obtain ⟨F⟩ : Nonempty (Favorable v σ) := (Finset.mem_filter.mp hσ).2
    simpa [hMAX_def]
      using welfare_eq_max_of_favorable hn M v hv_inj hv_nn hv_le F
  -- Step 1: Σ welfare ≥ |FS| * MAX.
  have step1 :
      ((favorableSet v).card : F) * MAX ≤
      ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare v (v ∘ σ) := by
    calc ((favorableSet v).card : F) * MAX
        = ∑ _σ ∈ favorableSet v, MAX := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ favorableSet v, (auction n M).welfare v (v ∘ σ) :=
            Finset.sum_congr rfl (fun σ hσ => (hwelfare_FS σ hσ).symm)
      _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare v (v ∘ σ) := by
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
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (auction n M).welfare v (v ∘ σ) := step1

end Secretary

end Online.Auction
