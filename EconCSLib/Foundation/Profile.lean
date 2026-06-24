/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Logic.Function.Basic

/-!
# EconCSLib.Foundation.Profile

Compatibility shim for the older standalone `Profile N S` vocabulary.

The canonical profile abstraction for strategic games is now `G.Profile` in
`StrategicGame.Basic`, together with `StrategicGame.deviate`.

This file remains only to minimize breakage while Stage 2 is in progress.
It should not be treated as the primary public interface.
-/

/-- A strategy profile: a dependent function assigning a value to each index.

    Compatibility alias only. Prefer game-bound profile aliases such as `G.Profile`. -/
abbrev Profile (N : Type*) (S : N → Type*) := ∀ i : N, S i

/-- Unilateral deviation: index `i` switches to `s'`, all others keep their value.
    This is `Function.update` with a game-theoretic name. -/
abbrev deviate {N : Type*} {S : N → Type*} [DecidableEq N]
    (σ : Profile N S) (i : N) (s' : S i) : Profile N S :=
  Function.update σ i s'

namespace Profile

variable {N : Type*} {S : N → Type*} [DecidableEq N]

/-- `σ[i ↦ s']` is the profile where index `i` holds `s'` and all others are as in `σ`.

Scoped to keep the postfix `[…]` bracket from clashing with list literals
(`… []`) in importing files; `open scoped Profile` to use it. -/
scoped notation:max σ "[" i " ↦ " s "]" => deviate σ i s

/-- Deviating to the same value is the identity. -/
@[simp]
theorem deviate_self (σ : Profile N S) (i : N) :
    deviate σ i (σ i) = σ := by
  simp [deviate]

/-- At the deviated index, the profile returns the new value. -/
@[simp]
theorem deviate_same (σ : Profile N S) (i : N) (s' : S i) :
    deviate σ i s' i = s' := by
  simp [deviate]

/-- At any other index, the profile is unchanged. -/
@[simp]
theorem deviate_of_ne (σ : Profile N S) (i : N) (s' : S i) {j : N} (h : j ≠ i) :
    deviate σ i s' j = σ j := by
  simp [deviate, h]

end Profile
