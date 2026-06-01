/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.CoalitionalGame.Basic

Coalitional games with transferable utility (TU games).

## Design

`CoalitionalGame N U` is parameterized by both the player type `N` and the utility
type `U`. Assumptions are added at usage sites:
- `[Fintype N]` where grand coalition `Finset.univ` is needed (e.g., `IsEfficient`)
- `U = ℝ` only where real arithmetic is genuinely required (Shapley value, Bondareva-Shapley)

The structure requires `[AddZeroClass U]` (not just `[Zero U]`) to ensure a single
canonical `Zero` instance across the namespace, avoiding typeclass diamond issues when
theorems add `[AddCommMonoid U]` or stronger constraints.

## Main definitions

* `CoalitionalGame` — `(N; v)` where `v : Finset N → U` with `v ∅ = 0`
* `PayoffVector` — payoff assignment `N → U`
* `coalitionPayoff` — total payoff of a coalition
* `IsEfficient`, `IsIndividuallyRational`, `IsImputation`
* `IsSuperadditive`, `IsMonotonic`, `IsConvex`, `IsSimple`, `IsAdditive`

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 16
-/

open Finset BigOperators

/-! ### Coalitional game structure -/

/-- A coalitional game with transferable utility.
    `N` is the player type; `U` is the utility type.
    `v` assigns a worth to each coalition, with the empty coalition worth zero. [MSZ 16.1]

    No finiteness or concrete number-system assumptions are baked in.
    Specialize `U` to `ℝ` only where real arithmetic is genuinely required. -/
structure CoalitionalGame (N : Type*) (U : Type*) [DecidableEq N] [AddZeroClass U] where
  /-- The characteristic function: worth of each coalition. -/
  v : Finset N → U
  /-- The empty coalition is worth zero. -/
  empty_zero : v ∅ = 0

namespace CoalitionalGame

-- `[AddZeroClass U]` is the section-level minimum: provides both `Zero` and `Add`,
-- ensuring a single canonical `Zero` instance throughout the namespace.
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U]
variable (G : CoalitionalGame N U)

/-! ### Payoff vectors -/

/-- A payoff vector: an assignment of payoffs to players. -/
abbrev PayoffVector (N : Type*) (U : Type*) := N → U

/-- The total payoff of a coalition under a payoff vector.
    Requires `[AddCommMonoid U]` for the finite sum. -/
def coalitionPayoff [AddCommMonoid U] (x : PayoffVector N U) (S : Finset N) : U :=
  ∑ i ∈ S, x i

/-! ### Imputations -/

/-- A payoff vector is efficient if it distributes exactly `v(N)`. [MSZ 16.1]
    Requires `[Fintype N]` and `[AddCommMonoid U]`. -/
def IsEfficient [Fintype N] [AddCommMonoid U] (x : PayoffVector N U) : Prop :=
  coalitionPayoff x Finset.univ = G.v Finset.univ

/-- A payoff vector is individually rational if each player gets at least
    their singleton worth. Requires `[LE U]`. -/
def IsIndividuallyRational [LE U] (x : PayoffVector N U) : Prop :=
  ∀ i : N, x i ≥ G.v {i}

/-- An imputation is an efficient and individually rational payoff vector. [MSZ 17.1] -/
def IsImputation [Fintype N] [AddCommMonoid U] [LE U] (x : PayoffVector N U) : Prop :=
  G.IsEfficient x ∧ G.IsIndividuallyRational x

/-! ### Game properties -/

/-- A game is superadditive if the worth of the union of disjoint coalitions
    is at least the sum of their worths. [MSZ 16.8]
    Requires `[LE U]` (addition comes from the `[AddZeroClass U]` section variable). -/
def IsSuperadditive [LE U] : Prop :=
  ∀ S T : Finset N, Disjoint S T → G.v (S ∪ T) ≥ G.v S + G.v T

/-- A game is monotonic if larger coalitions are worth at least as much. [MSZ 16.10]
    Requires `[LE U]`. -/
def IsMonotonic [LE U] : Prop :=
  ∀ S T : Finset N, S ⊆ T → G.v S ≤ G.v T

/-- A game is convex if it satisfies the supermodularity condition. [MSZ 17.51]
    Requires `[LE U]` (addition comes from `[AddZeroClass U]`). -/
def IsConvex [LE U] : Prop :=
  ∀ S T : Finset N, G.v (S ∪ T) + G.v (S ∩ T) ≥ G.v S + G.v T

/-- A game is simple if every coalition's worth is 0 or 1,
    and the grand coalition's worth is 1. [MSZ 16.2]
    Requires `[Fintype N]` and `[One U]`. -/
def IsSimple [Fintype N] [One U] : Prop :=
  (∀ S : Finset N, G.v S = 0 ∨ G.v S = 1) ∧ G.v Finset.univ = 1

/-- A coalition is winning in a simple game if its worth is 1. Requires `[One U]`. -/
def IsWinning [One U] (S : Finset N) : Prop :=
  G.v S = 1

/-- A game is additive if `v(S) = ∑_{i ∈ S} v({i})`. [MSZ 17.41]
    Requires `[AddCommMonoid U]`. -/
def IsAdditive [AddCommMonoid U] : Prop :=
  ∀ S : Finset N, G.v S = ∑ i ∈ S, G.v {i}

/-! ### Basic theorems -/

/-- Convexity implies superadditivity.
    The `[LE U]` constraint is all that's needed beyond the section's `[AddZeroClass U]`. -/
theorem IsConvex.isSuperadditive [LE U] (hconv : G.IsConvex) : G.IsSuperadditive := by
  intro S T hST
  have h := hconv S T
  rw [Finset.disjoint_iff_inter_eq_empty.mp hST, G.empty_zero, add_zero] at h
  exact h

end CoalitionalGame
