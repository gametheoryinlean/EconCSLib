/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Dominance

/-!
# EconCSLib.GameTheory.StrategicGame.NashEquilibrium

A profile is a pure Nash equilibrium if every player is playing a best response.

## Main definitions

* `IsNashEquilibrium` — every player is a best responder

## Main results

* T3: `IsNashEquilibrium.of_dominant` — a dominant profile is Nash
-/

variable {N U : Type*} [DecidableEq N] [Preorder U]

open StrategicGame

/-- A profile `σ` is a pure Nash equilibrium of game `G` if every player is playing
    a best response: no player can profitably deviate. -/
def IsNashEquilibrium (G : StrategicGame N U) (σ : G.Profile) : Prop :=
  ∀ i : N, IsBestResponse G σ i

namespace IsNashEquilibrium

/-- T3: If every player has a weakly dominant strategy and `σ` assigns each player
    their dominant strategy, then `σ` is a Nash equilibrium. -/
theorem of_dominant {G : StrategicGame N U} {σ : G.Profile}
    (h : ∀ i : N, IsWeaklyDominant G i (σ i)) : IsNashEquilibrium G σ :=
  fun i => (h i).isBestResponse σ rfl

end IsNashEquilibrium
