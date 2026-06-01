/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Strategy

Strategies for extensive-form games built on the Arena framework.

## Main definitions

* `Strategy G i` — a strategy for player `i`: choose an action at each state they control
* `StrategyProfile G` — strategies for all players
* `completeProfile` — fill in a strategy profile with an action-selection function
-/

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- A strategy for player `i`: at each state where `i` is the mover,
    specify which action to take. -/
def Strategy (G : ExtensiveGame N U) (i : N) :=
  (s : G.State) → G.mover s = some i → G.Action s

/-- A strategy profile: a strategy for each player. -/
def StrategyProfile (G : ExtensiveGame N U) :=
  (i : N) → G.Strategy i

/-- Given a strategy profile, extract the action at a non-chance state.
    Returns `none` at chance states (mover = none). -/
def StrategyProfile.actionAt [DecidableEq N] {G : ExtensiveGame N U}
    (σ : StrategyProfile G) (s : G.State) :
    Option (Σ i : N, G.Action s) :=
  match h : G.mover s with
  | some i => some ⟨i, σ i s h⟩
  | none => none

end ExtensiveGame
