/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Vickrey

/-!
# EconCSLib.MechanismDesign.Auction.ReserveVickrey

Reserve Vickrey auction, formalized as a second-price auction with a reserve
price.

## Position in the hierarchy

```
MechanismWithTransfers I (fun _ => U) (Option I) U
  └─ ReserveSecondPrice.mechanism reserve         -- reserve allocation + clearing-price payments
       └─ ReserveSecondPrice.game reserve v       -- induced StrategicGame at true values v

SecondPrice.winner / SecondPrice.secondPrice      -- reused Vickrey primitives
  └─ ReserveSecondPrice.allocation reserve
```

This file follows the organization of `Auction.Vickrey` and reuses its
second-price primitives. The difference is that the item may be withheld: the
allocation type is `Option I`, where `none` means that the highest bid does not
meet the reserve.

As in `Auction.Vickrey`, the file name records the standard Vickrey terminology,
while the declarations use the descriptive namespace `ReserveSecondPrice`.

The winner, when the reserve is met, is the highest bidder selected by
`SecondPrice.winner`; the winner pays the maximum of the reserve and
`SecondPrice.secondPrice`.

## Main definitions

* `Auction.SecondPrice.winner` - reused highest-bidder rule
* `Auction.SecondPrice.secondPrice` - reused second-price rule
* `Auction.ReserveSecondPrice.clearingPrice` - `max reserve secondPrice`
* `Auction.ReserveSecondPrice.allocation` - `some winner` if the reserve is met,
  otherwise `none`
* `Auction.ReserveSecondPrice.mechanism` - the reserve second-price auction as a
  `MechanismWithTransfers`
* `Auction.ReserveSecondPrice.utility`
* `Auction.ReserveSecondPrice.game`

## Main results

* `Auction.ReserveSecondPrice.allocation_eq_some_iff`
* `Auction.ReserveSecondPrice.allocation_eq_none_iff`
* `Auction.ReserveSecondPrice.allocation_ne_some_of_ne_winner`
* `Auction.ReserveSecondPrice.clearingPrice_le_bid_of_allocation_eq_some`
* `Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some`
* `Auction.ReserveSecondPrice.mechanism_payment_of_allocation_ne_some`
* `Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_ne_winner`
* `Auction.ReserveSecondPrice.mechanism_payment_le_bid_of_allocation_eq_some`
* `Auction.ReserveSecondPrice.mechanism_payment_abs_le_max_reserve_bid`
* `Auction.ReserveSecondPrice.mechanism_payment_update_self_zero_of_nonneg_reserve`
* `Auction.ReserveSecondPrice.game_eq_toStrategicGame`
* `Auction.ReserveSecondPrice.mechanism_isDSIC`
* `Auction.ReserveSecondPrice.utility_nonneg`
* `Auction.ReserveSecondPrice.valuation_is_dominant`
* `Auction.ReserveSecondPrice.truthful_weakly_dominant`

## References

* [Nisan et al., *Algorithmic Game Theory*, Ch. 9]
* [Roughgarden, *Twenty Lectures on Algorithmic Game Theory*, Lecture 3]
-/

variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I]
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U]

namespace Auction

namespace ReserveSecondPrice

/-! ### Reserve and payment -/

/-- The price paid by the winner: the maximum of the reserve and the second price. -/
noncomputable def clearingPrice (reserve : U) (b : I → U) : U :=
  max reserve (SecondPrice.secondPrice b)

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The clearing price is at least the reserve. -/
lemma reserve_le_clearingPrice (reserve : U) (b : I → U) :
    reserve ≤ clearingPrice reserve b :=
  le_max_left reserve (SecondPrice.secondPrice b)

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The clearing price is at least the second price. -/
lemma secondPrice_le_clearingPrice (reserve : U) (b : I → U) :
    SecondPrice.secondPrice b ≤ clearingPrice reserve b :=
  le_max_right reserve (SecondPrice.secondPrice b)

/-- The item is sold exactly when the winning bid meets the reserve. -/
noncomputable def allocation (reserve : U) (b : I → U) : Option I :=
  if reserve ≤ b (SecondPrice.winner b) then some (SecondPrice.winner b) else none

/-! #### Reserve bridge lemmas -/

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- If bidder `i` is allocated the item, then `i` is the second-price winner. -/
lemma winner_eq_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    SecondPrice.winner b = i := by
  unfold allocation at halloc
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · simpa [h] using halloc
  · simp [h] at halloc

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- If the item is allocated, then the winning bid meets the reserve. -/
lemma reserve_le_bid_winner_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    reserve ≤ b (SecondPrice.winner b) := by
  unfold allocation at halloc
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · exact h
  · simp [h] at halloc

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The allocation is `some i` exactly when the reserve is met and `i` is the
second-price winner. -/
lemma allocation_eq_some_iff {reserve : U} {b : I → U} {i : I} :
    allocation reserve b = some i ↔
      reserve ≤ b (SecondPrice.winner b) ∧ SecondPrice.winner b = i := by
  unfold allocation
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · simp [h]
  · simp [h]

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- A bidder who is not the second-price winner is not allocated the item. -/
lemma allocation_ne_some_of_ne_winner {reserve : U} {b : I → U} {i : I}
    (hi : i ≠ SecondPrice.winner b) :
    allocation reserve b ≠ some i := by
  intro halloc
  exact hi (winner_eq_of_allocation_eq_some halloc).symm

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The allocation is the second-price winner exactly when the winner's bid
meets the reserve. -/
lemma allocation_eq_some_winner_iff {reserve : U} {b : I → U} :
    allocation reserve b = some (SecondPrice.winner b) ↔
      reserve ≤ b (SecondPrice.winner b) := by
  unfold allocation
  by_cases h : reserve ≤ b (SecondPrice.winner b) <;> simp [h]

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The item is withheld exactly when the winning bid is below the reserve. -/
lemma allocation_eq_none_iff {reserve : U} {b : I → U} :
    allocation reserve b = none ↔ b (SecondPrice.winner b) < reserve := by
  unfold allocation
  by_cases h : reserve ≤ b (SecondPrice.winner b)
  · simp [h, not_lt_of_ge h]
  · have hlt : b (SecondPrice.winner b) < reserve := lt_of_not_ge h
    simp [h, hlt]

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- When the item is sold, the clearing price is no more than the allocated
bidder's bid. -/
lemma clearingPrice_le_bid_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    clearingPrice reserve b ≤ b i := by
  have hwinner : SecondPrice.winner b = i := winner_eq_of_allocation_eq_some halloc
  have hreserve : reserve ≤ b i := by
    have h := reserve_le_bid_winner_of_allocation_eq_some halloc
    simpa [hwinner] using h
  have hsecond : SecondPrice.secondPrice b ≤ b i := by
    simpa [hwinner] using SecondPrice.secondPrice_le_bid_winner (b := b)
  exact max_le hreserve hsecond

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- When bidder `i` receives the item, the clearing price is the maximum of the
reserve and the highest bid excluding `i`. -/
lemma clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some
    {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) := by
  have hwinner : SecondPrice.winner b = i := winner_eq_of_allocation_eq_some halloc
  simp [clearingPrice, SecondPrice.secondPrice, hwinner]

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
private lemma bid_le_clearing_threshold_of_not_allocation_update_self
    (reserve : U) (b : I → U) (i : I) (bi : U)
    (hnot : allocation reserve (Function.update b i bi) ≠ some i) :
    bi ≤ max reserve (Auction.maxBidExcluding b i) := by
  let b' := Function.update b i bi
  by_cases hsell : reserve ≤ b' (SecondPrice.winner b')
  · have halloc : allocation reserve b' = some (SecondPrice.winner b') := by
      simp [allocation, hsell]
    have hwin_ne : SecondPrice.winner b' ≠ i := by
      intro h
      exact hnot (by simpa [b', h] using halloc)
    have hb_le_winner : b' i ≤ b' (SecondPrice.winner b') := by
      exact SecondPrice.bid_le_bid_winner b' i
    have hmax_eq : Auction.maxBidExcluding b' i = Auction.maxBid b' := by
      exact SecondPrice.maxBidExcluding_eq_maxBid_if_loser hwin_ne.symm
    have hle_excluding' : bi ≤ Auction.maxBidExcluding b' i := by
      have hbid_winner_eq_max : b' (SecondPrice.winner b') = Auction.maxBid b' := by
        exact SecondPrice.bid_winner_eq_maxBid b'
      rw [hmax_eq, ← hbid_winner_eq_max]
      simpa [b'] using hb_le_winner
    have hupdate : Auction.maxBidExcluding b' i = Auction.maxBidExcluding b i := by
      simpa [b'] using Auction.maxBidExcluding_update_self b i bi
    have hle_excluding : bi ≤ Auction.maxBidExcluding b i := by
      simpa [hupdate] using hle_excluding'
    exact le_trans hle_excluding (le_max_right reserve (Auction.maxBidExcluding b i))
  · have hbid_le_reserve : bi ≤ reserve := by
      have hb_le_winner : b' i ≤ b' (SecondPrice.winner b') := by
        exact SecondPrice.bid_le_bid_winner b' i
      have hwinner_le_reserve : b' (SecondPrice.winner b') ≤ reserve :=
        le_of_lt (lt_of_not_ge hsell)
      simpa [b'] using le_trans hb_le_winner hwinner_le_reserve
    exact le_trans hbid_le_reserve (le_max_left reserve (Auction.maxBidExcluding b i))

/-! ### Utility and strategic-game formulation -/

/-- Utility of bidder `i`:
the allocated bidder receives value minus the clearing price; all others receive `0`. -/
noncomputable def utility (reserve : U) (v b : I → U) (i : I) : U :=
  if allocation reserve b = some i then v i - clearingPrice reserve b else 0

variable {reserve : U} {v : I → U}

omit [IsOrderedAddMonoid U] in
/-- If bidder `i` is allocated, her utility is value minus the reserve
second-price clearing price. -/
lemma utility_winner {b : I → U} {i : I} (h : allocation reserve b = some i) :
    utility reserve v b i = v i - clearingPrice reserve b := if_pos h

omit [IsOrderedAddMonoid U] in
/-- If bidder `i` is not allocated, her utility is zero. -/
lemma utility_loser {b : I → U} {i : I} (h : allocation reserve b ≠ some i) :
    utility reserve v b i = 0 := if_neg h

/-- Truthful bidding yields nonnegative utility. -/
lemma utility_nonneg {b : I → U} {i : I} (htruth : b i = v i) :
    0 ≤ utility reserve v b i := by
  by_cases halloc : allocation reserve b = some i
  · rw [utility_winner halloc, sub_nonneg, ← htruth]
    exact clearingPrice_le_bid_of_allocation_eq_some halloc
  · simp [utility_loser halloc]

/-- Truthful bidding dominates any other bid in the reserve second-price auction. -/
theorem valuation_is_dominant (reserve : U) (v : I → U) (i : I) (b : I → U) :
    utility reserve v b i ≤ utility reserve v (Function.update b i (v i)) i := by
  let bTruth := Function.update b i (v i)
  by_cases hcurrent : allocation reserve b = some i
  · rw [utility_winner hcurrent]
    by_cases htruth : allocation reserve bTruth = some i
    · rw [utility_winner htruth]
      have hcurrent_price :
          clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) :=
        clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some hcurrent
      have htruth_price :
          clearingPrice reserve bTruth = max reserve (Auction.maxBidExcluding b i) := by
        calc
          clearingPrice reserve bTruth
              = max reserve (Auction.maxBidExcluding bTruth i) :=
                clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some htruth
          _ = max reserve (Auction.maxBidExcluding b i) := by
                simp [bTruth, Auction.maxBidExcluding_update_self]
      rw [hcurrent_price, htruth_price]
    · rw [utility_loser htruth]
      have hthreshold :
          v i ≤ clearingPrice reserve b := by
        have hprice :
            clearingPrice reserve b = max reserve (Auction.maxBidExcluding b i) :=
          clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some hcurrent
        have hle :
            v i ≤ max reserve (Auction.maxBidExcluding b i) := by
          simpa [bTruth] using
            bid_le_clearing_threshold_of_not_allocation_update_self reserve b i (v i) htruth
        simpa [hprice] using hle
      exact sub_nonpos.mpr hthreshold
  · rw [utility_loser hcurrent]
    exact utility_nonneg (reserve := reserve) (v := v)
      (b := Function.update b i (v i)) (i := i) (by simp)

/-- Reserve second-price auction as a strategic game. -/
noncomputable def game (reserve : U) (v : I → U) : StrategicGame I U where
  strategy := fun _ => U
  payoff b i := utility reserve v b i

/-- Truthful bidding is a weakly dominant strategy in the reserve second-price auction. -/
theorem truthful_weakly_dominant (reserve : U) (v : I → U) (i : I) :
    IsWeaklyDominant (game reserve v) i (v i) := by
  intro s' b
  simpa [game, StrategicGame.deviate, Function.update_idem] using
    valuation_is_dominant reserve v i (StrategicGame.deviate b i s')

/-! ### Mechanism design formulation -/

/-- The reserve second-price auction as a `MechanismWithTransfers`.

Agents report bids in `U`.  The allocation is `none` when the reserve is not
met, and `some i` when bidder `i` receives the item. -/
noncomputable def mechanism (reserve : U) :
    MechanismWithTransfers I (fun _ => U) (Option I) U where
  allocationRule b := allocation reserve b
  paymentRule b i := if allocation reserve b = some i then clearingPrice reserve b else 0

omit [IsOrderedAddMonoid U] in
/-- The mechanism allocation rule is the reserve second-price allocation rule. -/
@[simp] lemma mechanism_allocationRule (reserve : U) (b : I → U) :
    (mechanism reserve).allocationRule b = allocation reserve b :=
  rfl

omit [IsOrderedAddMonoid U] in
/-- The mechanism payment rule charges the clearing price exactly to the allocated bidder. -/
@[simp] lemma mechanism_paymentRule (reserve : U) (b : I → U) (i : I) :
    (mechanism reserve).paymentRule b i =
      if allocation reserve b = some i then clearingPrice reserve b else 0 :=
  rfl

omit [IsOrderedAddMonoid U] in
/-- The allocated bidder pays the clearing price. -/
lemma mechanism_payment_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    (mechanism reserve).paymentRule b i = clearingPrice reserve b := by
  rw [mechanism_paymentRule, if_pos halloc]

omit [IsOrderedAddMonoid U] in
/-- A bidder who is not allocated the item pays zero. -/
lemma mechanism_payment_of_allocation_ne_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b ≠ some i) :
    (mechanism reserve).paymentRule b i = 0 := by
  rw [mechanism_paymentRule, if_neg halloc]

omit [IsOrderedAddMonoid U] in
/-- If the item is withheld, every bidder pays zero. -/
lemma mechanism_payment_eq_zero_of_allocation_eq_none {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = none) :
    (mechanism reserve).paymentRule b i = 0 := by
  exact mechanism_payment_of_allocation_ne_some (by intro h; simp [halloc] at h)

omit [IsOrderedAddMonoid U] in
/-- A non-winner pays zero. -/
lemma mechanism_payment_eq_zero_of_ne_winner {reserve : U} {b : I → U} {i : I}
    (hi : i ≠ SecondPrice.winner b) :
    (mechanism reserve).paymentRule b i = 0 := by
  exact mechanism_payment_of_allocation_ne_some
    (allocation_ne_some_of_ne_winner hi)

omit [IsOrderedAddMonoid U] in
/-- The allocated bidder never pays more than her reported bid. -/
lemma mechanism_payment_le_bid_of_allocation_eq_some {reserve : U} {b : I → U} {i : I}
    (halloc : allocation reserve b = some i) :
    (mechanism reserve).paymentRule b i ≤ b i := by
  rw [mechanism_payment_of_allocation_eq_some halloc]
  exact clearingPrice_le_bid_of_allocation_eq_some halloc

/-- A reserve second-price payment is bounded by the reserve/bid scale. -/
lemma mechanism_payment_abs_le_max_reserve_bid {reserve : U} {b : I → U} {i : I} :
    |(mechanism reserve).paymentRule b i| ≤ max |reserve| |b i| := by
  by_cases halloc : allocation reserve b = some i
  · rw [mechanism_payment_of_allocation_eq_some halloc]
    have hle : clearingPrice reserve b ≤ b i :=
      clearingPrice_le_bid_of_allocation_eq_some halloc
    have hge : reserve ≤ clearingPrice reserve b :=
      reserve_le_clearingPrice reserve b
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_trans
        (le_trans (neg_le_neg (le_max_left |reserve| |b i|)) (neg_abs_le reserve)) hge
    · exact le_trans hle (le_trans (le_abs_self (b i)) (le_max_right |reserve| |b i|))
  · rw [mechanism_payment_of_allocation_ne_some halloc]
    simp

omit [IsOrderedAddMonoid U] in
/-- With a nonnegative reserve, a bidder reporting zero pays zero when the
other bids are held fixed. -/
lemma mechanism_payment_update_self_zero_of_nonneg_reserve {reserve : U}
    (hreserve : 0 ≤ reserve) (i : I) (b : I → U) :
    (mechanism reserve).paymentRule (Function.update b i 0) i = 0 := by
  by_cases halloc : allocation reserve (Function.update b i 0) = some i
  · have hpay_le :
        (mechanism reserve).paymentRule (Function.update b i 0) i ≤ 0 := by
      simpa [Function.update_self] using
        mechanism_payment_le_bid_of_allocation_eq_some halloc
    have hpay_eq :
        (mechanism reserve).paymentRule (Function.update b i 0) i =
          clearingPrice reserve (Function.update b i 0) :=
      mechanism_payment_of_allocation_eq_some halloc
    have hpay_nonneg :
        0 ≤ (mechanism reserve).paymentRule (Function.update b i 0) i := by
      rw [hpay_eq]
      exact le_trans hreserve (reserve_le_clearingPrice reserve (Function.update b i 0))
    exact le_antisymm hpay_le hpay_nonneg
  · exact mechanism_payment_of_allocation_ne_some halloc

omit [IsOrderedAddMonoid U] in
/-- `game reserve v` equals the strategic game induced by `mechanism reserve`. -/
lemma game_eq_toStrategicGame (reserve : U) (v : I → U) :
    game reserve v =
      (mechanism reserve).toStrategicGame
        (fun (w : Option I) (pay : I → U) (vals : I → U) (i : I) =>
          if w = some i then vals i - pay i else 0)
        v := by
  unfold game mechanism MechanismWithTransfers.toStrategicGame
  congr 1
  funext b i
  simp [utility]
  split_ifs <;> rfl

/-- The reserve second-price auction satisfies dominant-strategy incentive compatibility. -/
theorem mechanism_isDSIC (reserve : U) :
    (mechanism reserve).isDSIC
      (fun (w : Option I) (pay : I → U) (vals : I → U) (i : I) =>
        if w = some i then vals i - pay i else 0) := by
  intro v i
  convert truthful_weakly_dominant reserve v i using 1
  exact (game_eq_toStrategicGame reserve v).symm

end ReserveSecondPrice

end Auction
