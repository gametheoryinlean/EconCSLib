/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# EconCSLib.GameTheory.StrategicGame.Basic

Defines `StrategicGame`, the central structure of the library.

## Main definitions

* `StrategicGame` — a strategic-form (normal-form) game
* `StrategicGame.Profile` — the type of strategy profiles for a game
* `StrategicGame.deviate` — unilateral deviation on a game-bound profile
* `welfare` — social welfare (sum of payoffs)

## Design choices

- `N` (player type) and `U` (utility type) are unconstrained in the structure.
- `strategy` is a dependent family, so players may have different strategy spaces.
- `Profile G` = `∀ i, G.strategy i` (a choice of strategy for each player).
- `deviate σ i s'` is owned by `StrategicGame`, not by a standalone core profile abstraction.
-/

/-- A strategic game (normal-form game) with players `N` and utilities in `U`.

The structure records only the bare data: strategy spaces and a payoff function.
All assumptions (finiteness, ordering, computability) are added at usage sites. -/
structure StrategicGame (N : Type*) (U : Type*) where
  /-- The strategy space of each player. -/
  strategy : N → Type*
  /-- The payoff function: maps a strategy profile to each player's utility. -/
  payoff : (∀ i, strategy i) → N → U

namespace StrategicGame

variable {N U : Type*}

/-! ### Profile -/

/-- The type of strategy profiles for game `G`: each player picks a strategy.

    This is a dependent function `∀ i, G.strategy i`. The profile type is bound to
    the game, making it explicit that a profile belongs to a specific strategic game. -/
abbrev Profile (G : StrategicGame N U) := ∀ i, G.strategy i

/-- Unilateral deviation in a game-bound profile: player `i` switches to `s'`,
    while all other players keep their current strategies. -/
abbrev deviate {G : StrategicGame N U} [DecidableEq N]
    (σ : G.Profile) (i : N) (s' : G.strategy i) : G.Profile :=
  Function.update σ i s'

/-- `σ[i ↦ s']` is the profile where player `i` switches to `s'`. -/
notation:max σ "[" i " ↦ " s "]" => StrategicGame.deviate σ i s

namespace Profile

variable {G : StrategicGame N U} [DecidableEq N]

/-- Deviating to the same strategy is the identity. -/
@[simp]
theorem deviate_self (σ : G.Profile) (i : N) :
    deviate σ i (σ i) = σ := by
  simp [StrategicGame.deviate]

/-- At the deviated player, the updated profile returns the new strategy. -/
@[simp]
theorem deviate_same (σ : G.Profile) (i : N) (s' : G.strategy i) :
    deviate σ i s' i = s' := by
  simp [StrategicGame.deviate]

/-- At every other player, the updated profile is unchanged. -/
@[simp]
theorem deviate_of_ne (σ : G.Profile) (i : N) (s' : G.strategy i) {j : N} (h : j ≠ i) :
    deviate σ i s' j = σ j := by
  simp [StrategicGame.deviate, h]

end Profile

/-! ### Welfare -/

/-- The social welfare of a profile: the sum of all players' payoffs.
    Requires `[Fintype N]` and `[AddCommMonoid U]`. -/
noncomputable def welfare [Fintype N] [AddCommMonoid U]
    (G : StrategicGame N U) (σ : G.Profile) : U :=
  ∑ i, G.payoff σ i

end StrategicGame
