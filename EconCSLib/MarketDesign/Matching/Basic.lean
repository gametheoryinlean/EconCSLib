/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Preference
import Mathlib.Data.Fintype.Basic

/-!
# EconCSLib.MarketDesign.Matching.Basic

Stable matching theory: two-sided markets where agents on each side
have preferences over agents on the other side.

## Main definitions

* `MatchingMarket` — a two-sided market with bundled preferences over partners
* `Matching` — a matching between two sets
* `IsBlocking` — a blocking pair [MSZ 22.5]
* `IsStable` — a stable matching (no blocking pair) [MSZ 22.5]
* `IsIndividuallyRational` — every matched agent strictly prefers their partner
  to being unmatched

## Design

`MatchingMarket` stores only preference data. It does **not** bake
`[Fintype M] [Fintype W]` into the structure. Finiteness belongs at the
algorithm or existence-theorem layer, not in the market itself.

Preferences are bundled using the foundation-level `Pref` interface,
applied to `Option W` and `Option M` so that `none` represents being unmatched.
Strict preference is derived uniformly via `strict`.

## References

* [MSZ] Chapter 22
* Gale, D. and Shapley, L.S. (1962). "College Admissions and the Stability of Marriage".
-/

/-! ### Matching market -/

/-- A two-sided matching market. `M` and `W` are the two sides (e.g., men and women,
    hospitals and residents). Each agent has a preference over agents on
    the other side plus the option of being unmatched (`none`). -/
structure MatchingMarket (M W : Type*) where
  /-- Each agent on side `M` has a preference over `Option W`. -/
  prefM : M → Pref (Option W)
  /-- Each agent on side `W` has a preference over `Option M`. -/
  prefW : W → Pref (Option M)

/-! ### Matching -/

/-- A matching is a partial bijection between `M` and `W`.
    `matchM i` is the partner of `i ∈ M` (or `none` if unmatched).
    `matchW j` is the partner of `j ∈ W` (or `none` if unmatched). -/
@[ext]
structure Matching (M W : Type*) where
  /-- Partner of each agent on side `M`. -/
  matchM : M → Option W
  /-- Partner of each agent on side `W`. -/
  matchW : W → Option M
  /-- Consistency: `matchM m = some w ↔ matchW w = some m`. -/
  consistent : ∀ (m : M) (w : W), matchM m = some w ↔ matchW w = some m

namespace Matching

variable {M W : Type*}

/-! ### Stability -/

/-- A pair `(m, w)` is a blocking pair for matching `μ` if both `m` and `w`
    strictly prefer each other to their current partners. [MSZ 22.5] -/
def IsBlocking (market : MatchingMarket M W) (μ : Matching M W)
    (m : M) (w : W) : Prop :=
  strict (market.prefM m) (some w) (μ.matchM m) ∧
  strict (market.prefW w) (some m) (μ.matchW w)

/-- A matching is stable if it has no blocking pair. [MSZ 22.5] -/
def IsStable (market : MatchingMarket M W) (μ : Matching M W) : Prop :=
  ∀ m : M, ∀ w : W, ¬ IsBlocking market μ m w

/-- A matching is individually rational if every matched agent strictly prefers
    their partner to being unmatched. -/
def IsIndividuallyRational (market : MatchingMarket M W) (μ : Matching M W) : Prop :=
  (∀ m : M, ∀ w : W, μ.matchM m = some w → strict (market.prefM m) (some w) none) ∧
  (∀ w : W, ∀ m : M, μ.matchW w = some m → strict (market.prefW w) (some m) none)

end Matching
