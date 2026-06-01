/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import EconCSLib.GameTheory.CoalitionalGame.Basic

/-!
# EconCSLib.GameTheory.CoalitionalGame.Core

The core of a coalitional game: the set of imputations that no coalition
can improve upon.

## Main definitions

* `Core` — the core of a coalitional game [MSZ 17.2]
* `IsBalanced` — balanced collection of coalitions [MSZ 17.11]

## Main results

* `core_subset_imputations` — every core element is an imputation ✓

## References

* [MSZ] Chapter 17
-/

open Finset BigOperators

namespace CoalitionalGame

-- Bondareva-Shapley requires real-valued payoffs (ℝ-linear programming)
-- and a finite player set.
variable {N : Type*} [DecidableEq N] [Fintype N]
variable (G : CoalitionalGame N ℝ)

/-! ### Core definition -/

/-- The core of a coalitional game: payoff vectors where no coalition can
    improve upon its allocation. [MSZ 17.2]

    An element `x` of the core satisfies:
    - Efficiency: `∑ᵢ xᵢ = v(N)`
    - Coalition stability: `∑_{i ∈ S} xᵢ ≥ v(S)` for all `S` -/
def Core : Set (PayoffVector N ℝ) :=
  { x | G.IsEfficient x ∧ ∀ S : Finset N, coalitionPayoff x S ≥ G.v S }

/-- Every element of the core is an imputation. -/
theorem core_subset_imputations :
    G.Core ⊆ { x | G.IsImputation x } := by
  intro x ⟨heff, hcoal⟩
  refine ⟨heff, fun i => ?_⟩
  have h := hcoal {i}
  simp [coalitionPayoff] at h
  exact h

/-! ### Balanced collections -/

/-- A collection of coalitions is balanced if there exist positive weights
    summing to the characteristic vector of `N`. [MSZ 17.11] -/
def IsBalanced (𝒟 : Finset (Finset N)) : Prop :=
  ∃ δ : Finset N → ℝ,
    (∀ S ∈ 𝒟, δ S > 0) ∧
    ∀ i : N, ∑ S ∈ 𝒟.filter (i ∈ ·), δ S = 1

/-- A game is balanced if every balanced collection satisfies the
    superadditivity-like condition. [MSZ 17.14 premise] -/
def IsBalancedGame : Prop :=
  ∀ (𝒟 : Finset (Finset N)) (δ : Finset N → ℝ),
    (∀ S ∈ 𝒟, δ S > 0) →
    (∀ i : N, ∑ S ∈ 𝒟.filter (i ∈ ·), δ S = 1) →
    ∑ S ∈ 𝒟, δ S * G.v S ≤ G.v Finset.univ

end CoalitionalGame
