/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeNE
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium

/-!
# EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm

Strategic-form extraction for finite perfect-information `GameTree` games.

The extracted normal-form game gives every player a complete contingent plan:
at each node context `(mover, head, tail)`, choose one of the available
children.  During play, the node's mover selects which player's plan is used.

## Main definitions

* `GameTree.PlayerStrategy` — one player's contingent plan on a `GameTree`.
* `GameTree.profileStrategy` — combine a normal-form profile into a global tree
  strategy.
* `GameTree.toStrategicGame` — extracted pure normal-form game.

## Main results

* `toStrategicGame_nash_iff_isNashAt` — pure Nash in the extracted game is
  exactly root-scoped Nash in the original tree.
-/

namespace GameTree

variable {N U : Type*}
variable [DecidableEq N]

/-- A single player's pure strategy in the normal form of a `GameTree`:
    a complete contingent plan choosing a child at every possible node. -/
def PlayerStrategy (N U : Type*) : Type _ :=
  (m : N) → (h : GameTree N U) → (t : List (GameTree N U)) →
    { c : GameTree N U // c ∈ h :: t }

/-- Combine a normal-form profile into the global `GameTree.Strategy` used by
    the game-tree evaluator.  At each node, the mover's contingent plan is used. -/
def profileStrategy (σ : N → PlayerStrategy N U) : Strategy N U :=
  fun m h t => σ m m h t

/-- The strategic-form extraction of a finite perfect-information tree. -/
noncomputable def toStrategicGame (g : GameTree N U) : StrategicGame N U where
  strategy := fun _ => PlayerStrategy N U
  payoff σ i := outcome (profileStrategy σ) g i

/-- Replacing player `i`'s normal-form contingent plan produces an `i`-variant
    global tree strategy. -/
theorem profileStrategy_deviate_variant (σ : N → PlayerStrategy N U)
    (i : N) (s' : PlayerStrategy N U) :
    IVariant i (profileStrategy σ) (profileStrategy (Function.update σ i s')) := by
  intro m h t hmi
  simp [profileStrategy, hmi]

/-- Any global `i`-variant tree strategy can be represented by deviating player
    `i`'s normal-form contingent plan. -/
theorem profileStrategy_deviate_eq_of_variant (σ : N → PlayerStrategy N U)
    (i : N) (τ : Strategy N U) (hτ : IVariant i (profileStrategy σ) τ) :
    profileStrategy (Function.update σ i (τ : PlayerStrategy N U)) = τ := by
  funext m h t
  by_cases hmi : m = i
  · subst hmi
    simp [profileStrategy]
  · simp [profileStrategy, hmi]
    exact hτ m h t hmi

variable [TotalPreorder U]

/-- Nash equilibrium in the extracted strategic-form game is exactly Nash
    equilibrium at the root of the original tree. -/
theorem toStrategicGame_nash_iff_isNashAt (g : GameTree N U)
    (σ : (toStrategicGame g).Profile) :
    _root_.IsNashEquilibrium (toStrategicGame g) σ ↔ IsNashAt (profileStrategy σ) g := by
  constructor
  · intro hN i τ hτ
    have hdev := hN i (τ : PlayerStrategy N U)
    simpa [toStrategicGame, IsBestResponse, StrategicGame.deviate,
      profileStrategy_deviate_eq_of_variant σ i τ hτ] using hdev
  · intro hN i s'
    exact hN i (profileStrategy (Function.update σ i s'))
      (profileStrategy_deviate_variant σ i s')

end GameTree
