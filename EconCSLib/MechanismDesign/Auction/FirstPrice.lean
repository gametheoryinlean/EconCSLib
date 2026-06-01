/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.AuctionBasic
import EconCSLib.Foundation.OrderedGroup

/-!
# EconCSLib.MechanismDesign.Auction.FirstPrice

First-price auction: the winner pays their own bid.

## Position in the hierarchy

```
MechanismWithTransfers I (fun _ => U) I U        -- scalar bids, winner allocation, scalar payments
  └─ FirstPrice.mechanism                        -- winner + own-bid payment rule
       └─ FirstPrice.game v                      -- induced StrategicGame at true values v
```

The auction is formalized as a `MechanismWithTransfers` (from `MechanismDesign.Auction.Transfer`).
The absence of DSIC is stated as `¬ mechanism.isDSIC auctionUtility`.

## Typeclass design

Same as `Auction.Vickrey`:
- `[AddCommGroup U]` — subtraction for utility
- `[LinearOrder U]` — comparing bids
- `[IsOrderedAddMonoid U]` — ordered group compatibility

Additionally, `mechanism_not_isDSIC` requires the existence of a positive
element `a : U` (to construct distinct bid levels for the counterexample).

## Main definitions

* `Auction.FirstPrice.winner` — the highest bidder (uses `Auction.argmaxBid` from `Basic`)
* `Auction.FirstPrice.mechanism` — first-price auction as a `MechanismWithTransfers`
* `Auction.FirstPrice.utility` — concrete utility formula (winner pays own bid)
* `Auction.FirstPrice.game` — first-price auction as a `StrategicGame`, equal to
  `mechanism.toStrategicGame (fun w pay v i => if i = w then v i - pay i else 0) v`

## Main results

* `Auction.FirstPrice.game_eq_toStrategicGame` — `game v` equals the mechanism-induced game
* `Auction.FirstPrice.mechanism_not_isDSIC` — first-price auction fails DSIC
* `Auction.FirstPrice.no_dominant_strategy` — no strategy is weakly dominant (game form)

## References

* [Roughgarden, *Twenty Lectures on Algorithmic Game Theory*, Lecture 3]
* Ma Jiajun, Wang Haocheng — original formalization in math-xmum/gametheory
-/

variable {I : Type*} [Fintype I] [Nontrivial I] [DecidableEq I]
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U]

namespace Auction

namespace FirstPrice

/-! ### Winner

In the first-price auction, the winner is the highest bidder (`Auction.argmaxBid`). -/

/-- The winner of the first-price auction: the bidder with the highest bid.
  Uses `Auction.argmaxBid` from `MechanismDesign.Auction.AuctionBasic`. -/
noncomputable def winner (b : I → U) : I := Auction.argmaxBid b

/-! #### Bridge lemma -/

omit [DecidableEq I] [AddCommGroup U] [IsOrderedAddMonoid U] in
private lemma eq_winner_of_bid_gt {b : I → U} (i : I) (h : ∀ j, j ≠ i → b j < b i) :
    i = winner b :=
  Auction.eq_argmaxBid_of_strict_max b i h

/-- Utility of bidder `i` in a first-price auction:
  winner gets `v i − b i` (pays own bid), losers get `0`. -/
noncomputable def utility (v b : I → U) (i : I) : U :=
  if i = winner b then v i - b i else 0

variable {v : I → U}

omit [IsOrderedAddMonoid U] in
/-- If `i` is the winner, utility is `v i − b i`. -/
lemma utility_winner {b : I → U} {i : I} (h : i = winner b) :
    utility v b i = v i - b i := if_pos h

omit [IsOrderedAddMonoid U] in
/-- If `i` is not the winner, utility is `0`. -/
lemma utility_loser {b : I → U} {i : I} (h : i ≠ winner b) :
    utility v b i = 0 := if_neg h

/-- First-price auction as a strategic game.

  This is also the game induced by `mechanism` via `MechanismWithTransfers.toStrategicGame`;
  see `game_eq_toStrategicGame`. -/
noncomputable def game (v : I → U) : StrategicGame I U where
  strategy := fun _ => U
  payoff b i := utility v b i

/-- **No dominant strategy exists in first-price auctions.**

  For any bidder `i` and any bid `bi`, there exists a profile where
  bidding `bi` is not optimal for `i`.

  Counterexample (from xmum/gametheory): set all opponents to bid `bi − a`
  for some `a > 0`, then `i` wins with both `bi` and `bi − a` but pays less
  with `bi − a`. -/
theorem no_dominant_strategy (v : I → U) (i : I) (bi : U)
    (ha : ∃ a : U, 0 < a) :
    ¬ IsWeaklyDominant (game v) i bi := by
  obtain ⟨a, ha⟩ := ha
  intro hdom
  -- Counterexample: others bid (bi - 2a), i bids (bi - a) vs bi.
  -- i wins both ways, but pays less with (bi - a), contradicting dominance of bi.
  set b : I → U := Function.update (fun _ => bi - a - a) i (bi - a)
  have hwd := hdom (bi - a) b
  have hb_other : ∀ j, j ≠ i → b j = bi - a - a := by
    intro j hj; exact Function.update_of_ne hj _ _
  have hb_self : b i = bi - a := by simp [b, Function.update_self]
  -- bi - a - a < bi - a since a > 0
  have hlt_a : bi - a - a < bi - a := sub_lt_self _ ha
  have hi_wins_b : i = winner b := by
    apply eq_winner_of_bid_gt
    intro j hj
    rw [hb_other j hj, hb_self]
    exact hlt_a
  -- bi - a - a < bi since a > 0
  have hlt_bi : bi - a - a < bi := lt_trans hlt_a (sub_lt_self _ ha)
  have hi_wins_bi : i = winner (Function.update b i bi) := by
    apply eq_winner_of_bid_gt
    intro j hj
    rw [Function.update_of_ne hj, hb_other j hj, Function.update_self]
    exact hlt_bi
  -- Compute both payoffs
  have h1 : (game v).payoff (Function.update b i (bi - a)) i = v i - (bi - a) := by
    show utility v (Function.update b i (bi - a)) i = _
    rw [show Function.update b i (bi - a) = b from by
      simp [b, Function.update_idem]]
    rw [utility_winner hi_wins_b]
    simp [b, Function.update_self]
  have h2 : (game v).payoff (Function.update b i bi) i = v i - bi := by
    show utility v (Function.update b i bi) i = _
    rw [utility_winner hi_wins_bi]
    simp [Function.update_self]
  rw [h1, h2] at hwd
  -- hwd : v i - (bi - a) ≤ v i - bi
  -- i.e. v i - bi + a ≤ v i - bi, i.e. a ≤ 0, contradicting ha
  have : v i - bi < v i - (bi - a) := by
    rw [show v i - (bi - a) = v i - bi + a from by abel]
    exact lt_add_of_pos_right _ ha
  exact absurd hwd (not_le.mpr this)

/-! ### Mechanism design formulation -/

/-- The first-price auction as a `MechanismWithTransfers`.

  Agents report bids in `U` (their type space is homogeneous: `T i = U`).
  - Allocation: the winner index (element of `I`)
  - Payments: the winner pays their own bid `b i`; all losers pay `0`. -/
noncomputable def mechanism : MechanismWithTransfers I (fun _ => U) I U where
  allocationRule b := winner b
  paymentRule b i := if i = winner b then b i else 0

omit [IsOrderedAddMonoid U] in
/-- `game v` equals the strategic game induced by `mechanism`.

  The payoffs agree because `paymentRule b i = if i = winner b then b i else 0`,
  so the utility is `v i - b i` for the winner and `0` for losers. -/
lemma game_eq_toStrategicGame (v : I → U) :
    game v = mechanism.toStrategicGame
      (fun (w : I) (pay : I → U) (vals : I → U) (i : I) => if i = w then vals i - pay i else 0)
      v := by
  unfold game mechanism MechanismWithTransfers.toStrategicGame
  congr 1
  funext b i
  simp [utility, winner]
  split_ifs <;> rfl

/-- **No dominant strategy in first-price auctions** (mechanism design form).

  The first-price auction does not satisfy DSIC: truthful bidding is not a weakly
  dominant strategy. This follows from `no_dominant_strategy` via `game_eq_toStrategicGame`.

  Requires a positive element `a : U` to construct the counterexample profile. -/
theorem mechanism_not_isDSIC (ha : ∃ a : U, 0 < a) :
    ¬ mechanism.isDSIC
        (fun (w : I) (pay : I → U) (vals : I → U) (i : I) => if i = w then vals i - pay i else 0) := by
  intro hDSIC
  obtain ⟨i, _, _⟩ := exists_pair_ne I
  have key : ∀ (b : I → U) (j : I),
      (mechanism.toStrategicGame (fun w pay vals i => if i = w then vals i - pay i else 0)
          (fun _ => (0 : U))).payoff b j =
      (game (fun _ => (0 : U))).payoff b j := by
    intro b j
    simp only [MechanismWithTransfers.toStrategicGame, mechanism, game, utility, winner]
    split_ifs <;> rfl
  apply no_dominant_strategy (fun _ => (0 : U)) i (0 : U) ha
  unfold IsWeaklyDominant WeaklyDominates
  intro s' b
  simp only [← key]
  exact hDSIC (fun _ => (0 : U)) i s' b

end FirstPrice

end Auction
