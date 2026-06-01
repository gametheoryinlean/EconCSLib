/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import EconCSLib.GameTheory.CoalitionalGame.Core

/-!
# EconCSLib.GameTheory.CoalitionalGame.ShapleyValue

The Shapley value: the unique single-valued solution concept satisfying
efficiency, symmetry, the null player property, and additivity.

## Main definitions

* `marginalContribution` — player `i`'s marginal contribution given a permutation
* `shapleyValue` — the Shapley value of each player [MSZ 18.14]
* Axioms: `Efficiency`, `Symmetry`, `NullPlayer`, `Additivity`

## References

* [MSZ] Chapter 18
-/

open Finset BigOperators

namespace CoalitionalGame

-- The Shapley value requires real-valued payoffs (ℝ-division, factorial arithmetic)
-- and a finite player set.
variable {N : Type*} [DecidableEq N] [Fintype N]
variable (G : CoalitionalGame N ℝ)

/-! ### Marginal contribution -/

/-- The marginal contribution of player `i` to coalition `S` (where `i ∉ S`). -/
def marginalContrib (i : N) (S : Finset N) : ℝ :=
  G.v (insert i S) - G.v S

/-- Two players are symmetric if swapping them doesn't change any coalition's worth. -/
def AreSymmetric (i j : N) : Prop :=
  ∀ S : Finset N, i ∉ S → j ∉ S → G.v (insert i S) = G.v (insert j S)

/-- A player is a null player if they add nothing to any coalition. [MSZ 18.6] -/
def IsNullPlayer (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S → G.v (insert i S) = G.v S

/-! ### Shapley value -/

/-- The Shapley value of player `i`. [MSZ 18.14, 18.17]

    `φᵢ(v) = ∑_{S ⊆ N\{i}} |S|!(|N|-|S|-1)!/|N|! · (v(S∪{i}) - v(S))` -/
noncomputable def shapleyValue (i : N) : ℝ :=
  ∑ S ∈ Finset.univ.filter (i ∉ ·),
    (Nat.factorial S.card * Nat.factorial (Fintype.card N - S.card - 1) : ℝ)
      / Nat.factorial (Fintype.card N)
      * G.marginalContrib i S

/-! ### Axioms for solution concepts -/

/-- A solution concept `φ` satisfies efficiency if payoffs sum to `v(N)`. [MSZ 18.2] -/
def SatisfiesEfficiency (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ G : CoalitionalGame N ℝ, ∑ i : N, φ G i = G.v Finset.univ

/-- A solution concept satisfies symmetry. [MSZ 18.4] -/
def SatisfiesSymmetry (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G : CoalitionalGame N ℝ) (i j : N), G.AreSymmetric i j → φ G i = φ G j

/-- A solution concept satisfies the null player property. [MSZ 18.7] -/
def SatisfiesNullPlayer (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G : CoalitionalGame N ℝ) (i : N), G.IsNullPlayer i → φ G i = 0

/-- A solution concept satisfies additivity. [MSZ 18.8] -/
def SatisfiesAdditivity (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G H : CoalitionalGame N ℝ) (i : N),
    φ ⟨fun S => G.v S + H.v S, by simp [G.empty_zero, H.empty_zero]⟩ i = φ G i + φ H i

end CoalitionalGame
