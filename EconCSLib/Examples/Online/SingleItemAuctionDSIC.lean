/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.Online.SingleItemAuction
import EconCSLib.MechanismDesign.Auction.Transfer

/-!
# EconCSLib.Examples.Online.SingleItemAuctionDSIC

The online single-item auction (Problem 2.1(a)) certified DSIC through the
**library's** dominant-strategy incentive-compatibility predicate
`MechanismWithTransfers.isDSIC` — the very definition used for Vickrey's
second-price auction.

This is kept in a separate file from `SingleItemAuction` on purpose: the
mechanism-design layer transitively imports `StrategicGame.Basic`, whose
deviation notation `σ[i ↦ s']` claims the postfix `[…]` bracket and would
collide with the many `… []` empty-list literals in the online-auction
development. Isolating the import keeps both halves clean.

## Main result

* `SingleItemAuction.mechanism_isDSIC` — the online auction, viewed as a
  `MechanismWithTransfers` (allocation = winning position, payment =
  clearing price), satisfies the general `isDSIC` predicate. The proof is
  a one-line reduction to the self-contained `dsic` via the
  `mech_utility_bridge`.
-/

namespace Online.Auction

open Online Function

variable {F : Type*}

namespace SingleItemAuction

variable [Field F] [LinearOrder F] [IsStrictOrderedRing F] (A : SingleItemAuction F)

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

end Online.Auction
