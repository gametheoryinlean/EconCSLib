/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Basic

/-!
# EconCSLib.GameTheory.StrategicGame.BestResponse

Defines `IsBestResponse`: player `i` is playing a best response to profile `σ` if
no unilateral deviation improves their payoff.

Key lemma:
- T1 (`IsBestResponse.congr_payoff`): best response depends only on player `i`'s payoff column.
-/

variable {N U : Type*} [DecidableEq N] [Preorder U]

open StrategicGame

/-- Player `i` is playing a best response to profile `σ` in game `G` if no unilateral
    deviation to any strategy `s'` yields a higher payoff. -/
def IsBestResponse (G : StrategicGame N U) (σ : G.Profile) (i : N) : Prop :=
  ∀ s' : G.strategy i, G.payoff (deviate σ i s') i ≤ G.payoff σ i

namespace IsBestResponse

/-- T1: Best response depends only on player `i`'s payoff column. -/
theorem congr_payoff (G : StrategicGame N U) (σ : G.Profile) (i : N)
    {payoff' : G.Profile → N → U}
    (h : ∀ τ : G.Profile, payoff' τ i = G.payoff τ i) :
    IsBestResponse G σ i ↔
    IsBestResponse { G with payoff := payoff' } σ i := by
  simp [IsBestResponse, h]

end IsBestResponse
