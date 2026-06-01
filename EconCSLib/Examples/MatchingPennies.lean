/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
import Mathlib.Data.Fintype.Pi

/-!
# EconCSLib.Examples.MatchingPennies

The classic Matching Pennies game: two players simultaneously place a penny
showing Heads or Tails. Player 0 wins if the two coins match; player 1 wins
otherwise.

Payoff matrix (row = player 0, column = player 1):
```
            Heads     Tails
Heads      +1, −1    −1, +1
Tails      −1, +1    +1, −1
```

This is the canonical small two-player zero-sum game (`MSZ` Example 4.40).

## Main results

* `mp_isZeroSum` — by `decide`, witnessing the `IsZeroSum.decidable` instance.

Payoffs are `ℤ`-valued (entries are ±1); `ℤ` has decidable equality, enabling
`decide` to evaluate the zero-sum predicate against the four-profile finite case.
-/

/-- The two coin faces. -/
inductive Coin | Heads | Tails
  deriving DecidableEq, Repr

instance : Fintype Coin :=
  ⟨⟨[Coin.Heads, Coin.Tails], by decide⟩, fun x => by cases x <;> decide⟩

namespace MatchingPennies

open Coin
open StrategicGame

/-- Matching Pennies as a strategic game with integer payoffs.

Marked `@[reducible]` so that `MP.strategy i` (which beta-reduces to `Coin`)
unfolds during typeclass search, letting the `Fintype Coin` instance satisfy
the `[∀ i, Fintype (MP.strategy i)]` premise of `IsZeroSum.decidable`. -/
@[reducible] def MP : StrategicGame (Fin 2) ℤ where
  strategy := fun _ => Coin
  payoff σ i :=
    if σ 0 = σ 1 then
      if i = 0 then 1 else -1
    else
      if i = 0 then -1 else 1

/-- Matching Pennies is zero-sum, verified by the decidable instance for
    `IsZeroSum` on finite-strategy games. -/
theorem mp_isZeroSum : IsZeroSum MP := by decide

end MatchingPennies
