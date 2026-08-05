/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.AuctionBasic
import EconCSLib.Foundation.OrderedGroup

/-!
# EconCSLib.MechanismDesign.Auction.Vickrey

Second-price (Vickrey) auction: the winner pays the second-highest bid.

## Position in the hierarchy

```
MechanismWithTransfers I (fun _ => U) I U        -- scalar bids, winner allocation, scalar payments
  └─ SecondPrice.mechanism                       -- winner + second-price payment rule
       └─ SecondPrice.game v                     -- induced StrategicGame at true values v
```

The auction is formalized as a `MechanismWithTransfers` (from `MechanismDesign.Auction.Transfer`).
DSIC is stated as `mechanism.isDSIC auctionUtility`, inheriting the general definition.

## Typeclass design

The bid/utility type `U` requires (following Mathlib's unbundled style):
- `[AddCommGroup U]` — subtraction for utility = valuation − payment
- `[LinearOrder U]` — comparing bids, selecting winner
- `[IsOrderedAddMonoid U]` — compatibility: `a ≤ b → a + c ≤ b + c`, `sub_nonneg`, etc.

This is the unbundled equivalent of the former `LinearOrderedAddCommGroup`.
No multiplication is needed — Vickrey payoff is `v_i − price`, pure additive.
Satisfied by `ℤ`, `ℚ`, `ℝ`, and any `LinearOrderedField`.

## Main definitions

* `Auction.SecondPrice.bidProfile` - the named bid-profile wrapper
* `Auction.SecondPrice.winner` - the highest bidder (uses `Auction.BidProfile.argmaxBid`)
* `Auction.SecondPrice.secondPrice` - highest bid excluding the winner
* `Auction.SecondPrice.bid_winner_eq_maxBid`
* `Auction.SecondPrice.bid_le_bid_winner`
* `Auction.SecondPrice.eq_winner_of_strict_max`
* `Auction.SecondPrice.maxBidExcluding_eq_maxBid_if_loser`
* `Auction.SecondPrice.mechanism` - second-price auction as a `MechanismWithTransfers`
* `Auction.SecondPrice.utility` — concrete utility formula (winner gets `v i − secondPrice`,
  losers get `0`)
* `Auction.SecondPrice.game` — second-price auction as a `StrategicGame`, equal to
  `mechanism.toStrategicGame (fun w pay v i => if i = w then v i - pay i else 0) v`

## Main results

* `Auction.SecondPrice.game_eq_toStrategicGame` — `game v` equals the mechanism-induced game
* `Auction.SecondPrice.mechanism_isDSIC` — DSIC at the `MechanismWithTransfers` level
* `Auction.SecondPrice.utility_nonneg` — truthful bidding yields nonneg utility
* `Auction.SecondPrice.valuation_is_dominant` — truthful bidding dominates any other bid
* `Auction.SecondPrice.truthful_weakly_dominant` — `IsWeaklyDominant` wrapper

## References

* [Roughgarden, *Twenty Lectures on Algorithmic Game Theory*, Lecture 3]
* [Vickrey, *Counterspeculation, Auctions, and Competitive Sealed Tenders*, 1961]
* Ma Jiajun, Wang Haocheng — original formalization in math-xmum/gametheory
-/

variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I]
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U]

namespace Auction

namespace SecondPrice

/-! ### Winner and second price

In the second-price auction, the winner is the highest bidder
(`Auction.BidProfile.argmaxBid`).
The price paid by the winner is the second-highest bid (highest bid excluding the winner). -/

/-- The named bid-profile wrapper for second-price reports. -/
def bidProfile (b : I → U) : Auction.BidProfile I U :=
  Auction.BidProfile.ofFunction b

/-- The winner of the second-price auction: the bidder with the highest bid.
  Uses `Auction.BidProfile.argmaxBid` from `MechanismDesign.Auction.AuctionBasic`. -/
noncomputable def winner (b : I → U) : I := (bidProfile b).argmaxBid

/-- The second price: the highest bid among all bidders other than the winner. -/
noncomputable def secondPrice (b : I → U) : U := (bidProfile b).maxBidExcluding (winner b)

/-! #### Bridge lemmas

These restate key facts about `winner` and `secondPrice` using local names,
so the proofs below do not need to spell out `Auction.argmaxBid` everywhere. -/

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The selected second-price winner's bid is the profile maximum. -/
lemma bid_winner_eq_maxBid (b : I → U) : b (winner b) = Auction.maxBid b :=
  Auction.argmaxBid_eq_maxBid b

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- Every bid is at most the selected second-price winner's bid. -/
lemma bid_le_bid_winner (b : I → U) (j : I) : b j ≤ b (winner b) :=
  Auction.bid_le_maxBid b j

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- A bidder who strictly outbids everyone else is the selected second-price winner. -/
lemma eq_winner_of_strict_max {b : I → U} (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = winner b :=
  Auction.eq_argmaxBid_of_strict_max b i h

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- Excluding a non-winner does not change the maximum bid. -/
lemma maxBidExcluding_eq_maxBid_if_loser {b : I → U} {i : I} (h : i ≠ winner b) :
    Auction.maxBidExcluding b i = Auction.maxBid b :=
  Auction.maxBidExcluding_eq_maxBid_of_not_argmax b h

omit [AddCommGroup U] [IsOrderedAddMonoid U] in
/-- The winner's bid is at least the second price. -/
lemma secondPrice_le_bid_winner (b : I → U) : secondPrice b ≤ b (winner b) := by
  unfold secondPrice winner
  calc Auction.maxBidExcluding b (Auction.argmaxBid b)
      ≤ Auction.maxBid b := Auction.maxBidExcluding_le_maxBid b _
    _ = b (Auction.argmaxBid b) := (Auction.argmaxBid_eq_maxBid b).symm

/-- Utility of bidder `i` in a second-price auction:
  winner gets `v i − secondPrice b`, losers get `0`. -/
noncomputable def utility (v b : I → U) (i : I) : U :=
  if i = winner b then v i - secondPrice b else 0

variable {v : I → U}

omit [IsOrderedAddMonoid U] in
/-- If `i` is the winner, utility is `v i − secondPrice b`. -/
lemma utility_winner {b : I → U} {i : I} (h : i = winner b) :
    utility v b i = v i - secondPrice b := if_pos h

omit [IsOrderedAddMonoid U] in
/-- If `i` is not the winner, utility is `0`. -/
lemma utility_loser {b : I → U} {i : I} (h : i ≠ winner b) :
    utility v b i = 0 := if_neg h

/-- Truthful bidding yields nonneg utility. -/
lemma utility_nonneg {b : I → U} {i : I} (htruth : b i = v i) :
    0 ≤ utility v b i := by
  rcases eq_or_ne i (winner b) with rfl | hne
  · rw [utility_winner rfl, sub_nonneg, ← htruth]
    exact secondPrice_le_bid_winner b
  · simp [utility_loser hne]

/-- **Vickrey's Theorem** (core form): Truthful bidding dominates any other bid.

  For any bid profile `b`, replacing `i`'s bid with `v i` does not decrease `i`'s utility. -/
theorem valuation_is_dominant (v : I → U) (i : I) (b : I → U) :
    utility v b i ≤ utility v (Function.update b i (v i)) i := by
  -- Key: maxBidExcluding is unchanged by updating i's bid
  have key : maxBidExcluding (Function.update b i (v i)) i = maxBidExcluding b i :=
    maxBidExcluding_update_self b i (v i)
  by_cases h1 : i = winner b
  · -- Case 1: i wins with current bid b
    rw [utility_winner h1]
    by_cases h2 : i = winner (Function.update b i (v i))
    · -- Case 1a: i also wins with truthful bid — same maxBidExcluding, same payoff
      rw [utility_winner h2, sub_le_sub_iff_left]
      show secondPrice (Function.update b i (v i)) ≤ secondPrice b
      have key' :
          (bidProfile (Function.update b i (v i))).maxBidExcluding i =
            (bidProfile b).maxBidExcluding i := by
        simpa [bidProfile] using key
      simpa [secondPrice, ← h1, ← h2] using le_of_eq key'
    · -- Case 1b: i loses with truthful bid — utility becomes 0
      rw [utility_loser h2, sub_nonpos]
      -- Goal: v i ≤ secondPrice b = maxBidExcluding b (winner b) = maxBidExcluding b i
      show v i ≤ secondPrice b
      rw [secondPrice, ← h1]
      -- Goal: v i ≤ maxBidExcluding b i
      set b' := Function.update b i (v i)
      have hle := bid_le_bid_winner b' i
      have hmbe := maxBidExcluding_eq_maxBid_if_loser (b := b') h2
      rw [bid_winner_eq_maxBid b', ← hmbe, key] at hle
      rwa [show b' i = v i from Function.update_self i (v i) b] at hle
  · -- Case 2: i loses with current bid b — utility = 0
    rw [utility_loser h1]
    -- Truthful bid gives nonneg utility
    exact utility_nonneg (Function.update_self i (v i) b)

/-- Second-price auction as a strategic game.

  This is also the game induced by `mechanism` via `MechanismWithTransfers.toStrategicGame`;
  see `game_eq_toStrategicGame`. -/
noncomputable def game (v : I → U) : StrategicGame I U where
  strategy := fun _ => U
  payoff b i := utility v b i

/-- **Vickrey's Theorem** (strategic game form):
  Truthful bidding is a weakly dominant strategy in the second-price auction. -/
theorem truthful_weakly_dominant (v : I → U) (i : I) :
    IsWeaklyDominant (game v) i (v i) := by
  intro s' b
  simpa [game, StrategicGame.deviate, Function.update_idem] using
    valuation_is_dominant v i (StrategicGame.deviate b i s')

/-! ### Mechanism design formulation -/

/-- The second-price auction as a `MechanismWithTransfers`.

  Agents report bids in `U` (their type space is homogeneous: `T i = U`).
  - Allocation: the winner index (element of `I`)
  - Payments: the winner pays `secondPrice b`; all losers pay `0`.

  This is the canonical `MechanismWithTransfers` instance from which the strategic
  game and DSIC statement are derived. [AGT Ch. 9] -/
noncomputable def mechanism : MechanismWithTransfers I (fun _ => U) I U where
  allocationRule b := winner b
  paymentRule b i := if i = winner b then secondPrice b else 0

omit [IsOrderedAddMonoid U] in
/-- `game v` equals the strategic game induced by `mechanism`.

  The payoffs agree because `paymentRule b i = if i = winner b then secondPrice b else 0`,
  so `(fun w pay v i => if i = w then v i - pay i else 0) (winner b) (paymentRule b) v i = utility v b i`. -/
lemma game_eq_toStrategicGame (v : I → U) :
    game v = mechanism.toStrategicGame
      (fun (w : I) (pay : I → U) (vals : I → U) (i : I) => if i = w then vals i - pay i else 0)
      v := by
  unfold game mechanism MechanismWithTransfers.toStrategicGame
  congr 1
  funext b i
  simp [utility, winner, secondPrice]
  split_ifs <;> rfl

/-- **Vickrey's Theorem** (mechanism design form):
  The second-price auction satisfies dominant-strategy incentive compatibility.

  This is `mechanism.isDSIC (fun w pay v i => if i = w then v i - pay i else 0)`,
  the general DSIC predicate from `MechanismDesign.Auction.Transfer` applied to the second-price
  mechanism. Proof follows from `truthful_weakly_dominant` via `game_eq_toStrategicGame`. -/
theorem mechanism_isDSIC :
    mechanism.isDSIC
      (fun (w : I) (pay : I → U) (vals : I → U) (i : I) => if i = w then vals i - pay i else 0) := by
  intro v i
  convert truthful_weakly_dominant v i using 1
  exact (game_eq_toStrategicGame v).symm

end SecondPrice

end Auction
