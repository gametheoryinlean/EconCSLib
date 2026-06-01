/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium

/-!
# EconCSLib.GameTheory.StrategicGame.CorrelatedEq

Correlated equilibrium: a distribution over strategy profiles where
no player benefits from deviating from the recommendation.

## Main definitions

* `IsDegenerateCorrelatedEq` — a degenerate correlated equilibrium supported on one profile

## Main results

* `nash_iff_degenerate_ce` — a point-mass correlated equilibrium is exactly a Nash equilibrium

## References

* [MSZ] Chapter 8
-/

namespace StrategicGame

variable {N U : Type*} [DecidableEq N] [Preorder U]

open StrategicGame

-- The general correlated-equilibrium interface will require distributions on
-- profiles and expected-utility obedience constraints.

/-- A degenerate correlated equilibrium supported on a single profile.

    This is the only honest correlated-equilibrium notion currently formalized
    in this file: the mediator recommends one fixed profile with probability 1.
    In that case, obedience is exactly the Nash condition. -/
def IsDegenerateCorrelatedEq (G : StrategicGame N U) (σ : G.Profile) : Prop :=
  IsNashEquilibrium G σ

/-- A profile is a "degenerate" correlated equilibrium (point mass on one profile)
    if and only if it is a Nash equilibrium. -/
theorem nash_iff_degenerate_ce (G : StrategicGame N U) (σ : G.Profile) :
    IsNashEquilibrium G σ ↔ IsDegenerateCorrelatedEq G σ := by
  exact Iff.rfl

end StrategicGame
