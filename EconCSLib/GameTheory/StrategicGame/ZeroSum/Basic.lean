/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic

Zero-sum and constant-sum two-player games.

## Main definitions

* `IsZeroSum` — payoffs sum to zero at every profile [MSZ 4.39]
* `IsConstantSum` — payoffs sum to a constant at every profile

## Main results

* `isZeroSum_iff_isConstantSum_zero` — `IsZeroSum G ↔ IsConstantSum G 0`
* `IsZeroSum.welfare_eq_zero` — two-player zero-sum welfare collapses to `0`
* `IsConstantSum.welfare_eq` — constant-sum welfare equals the constant
* `IsConstantSum.neg` — player 1's payoff equals `c - player 0's payoff`
* `IsZeroSum.neg` — one player's payoff is the negation of the other's
* `IsZeroSum.nash_payoff_eq` — all Nash equilibria yield the same payoff [MSZ 4.44]
* `IsConstantSum.nash_payoff_eq` — same for constant-sum games [MSZ 4.44–4.45]
* `IsZeroSum.expectedPayoff_neg` — mixed-strategy lift of `IsZeroSum.neg`
* `IsZeroSum.decidable` — `IsZeroSum` is decidable for finite-strategy games

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 4, Sections 4.4–4.6
-/

namespace StrategicGame

variable {U : Type*}

/-! ### Definitions -/

/-- A two-player game is zero-sum if payoffs sum to zero at every profile. [MSZ 4.39] -/
def IsZeroSum [Add U] [Zero U] (G : StrategicGame (Fin 2) U) : Prop :=
  ∀ σ : G.Profile, G.payoff σ 0 + G.payoff σ 1 = 0

/-- A two-player game is constant-sum if payoffs sum to `c` at every profile. -/
def IsConstantSum [Add U] (G : StrategicGame (Fin 2) U) (c : U) : Prop :=
  ∀ σ : G.Profile, G.payoff σ 0 + G.payoff σ 1 = c

/-! ### Zero-sum ↔ constant-sum zero

`IsZeroSum` and `IsConstantSum G 0` unfold to the exact same proposition; the
conversion lemmas let later API migrate between the two phrasings. We do **not**
mark them `@[simp]`: rewriting one definition into another in either direction
would just bounce simp between equivalent forms.
-/

/-- `IsZeroSum G` and `IsConstantSum G 0` are the same proposition. -/
theorem isZeroSum_iff_isConstantSum_zero [Add U] [Zero U]
    {G : StrategicGame (Fin 2) U} :
    IsZeroSum G ↔ IsConstantSum G 0 :=
  Iff.rfl

/-- A zero-sum game is a constant-sum game with constant `0`. -/
theorem IsZeroSum.toIsConstantSum [Add U] [Zero U]
    {G : StrategicGame (Fin 2) U} (hzs : IsZeroSum G) :
    IsConstantSum G 0 := hzs

/-- A constant-sum game whose constant is `0` is zero-sum. -/
theorem IsConstantSum.zero_isZeroSum [Add U] [Zero U]
    {G : StrategicGame (Fin 2) U} (h : IsConstantSum G 0) :
    IsZeroSum G := h

/-! ### Welfare collapse

`welfare` (from `StrategicGame.Basic`) sums payoffs. For two players this is
just `payoff σ 0 + payoff σ 1`, so the zero-sum / constant-sum predicates
collapse it directly. -/

/-- Two-player zero-sum games have zero social welfare at every profile. -/
theorem IsZeroSum.welfare_eq_zero [AddCommMonoid U]
    {G : StrategicGame (Fin 2) U} (hzs : IsZeroSum G) (σ : G.Profile) :
    welfare G σ = 0 := by
  unfold welfare
  rw [Fin.sum_univ_two]
  exact hzs σ

/-- Two-player constant-sum games have constant social welfare at every profile. -/
theorem IsConstantSum.welfare_eq [AddCommMonoid U]
    {G : StrategicGame (Fin 2) U} {c : U} (hcs : IsConstantSum G c) (σ : G.Profile) :
    welfare G σ = c := by
  unfold welfare
  rw [Fin.sum_univ_two]
  exact hcs σ

/-- In a constant-sum game, player 1's payoff is `c` minus player 0's.

`AddCommGroup` is needed (not just `AddGroup`): the RHS uses `Sub`, which
`AddGroup` defines as `c - a = c + -a`; matching it to `-a + c` (the canonical
rearrangement of `a + b = c`) requires commutativity. -/
theorem IsConstantSum.neg [AddCommGroup U]
    {G : StrategicGame (Fin 2) U} {c : U} (hcs : IsConstantSum G c) (σ : G.Profile) :
    G.payoff σ 1 = c - G.payoff σ 0 :=
  eq_sub_of_add_eq' (hcs σ)

/-- In a zero-sum game, player 1's payoff is the negation of player 0's.

Purely algebraic: holds in any additive group, no order or field needed. -/
theorem IsZeroSum.neg [AddGroup U]
    {G : StrategicGame (Fin 2) U} (hzs : IsZeroSum G) (σ : G.Profile) :
    G.payoff σ 1 = - G.payoff σ 0 :=
  add_eq_zero_iff_eq_neg'.mp (hzs σ)

/-- In a zero-sum game, player 0's payoff is the negation of player 1's. -/
theorem IsZeroSum.neg' [AddGroup U]
    {G : StrategicGame (Fin 2) U} (hzs : IsZeroSum G) (σ : G.Profile) :
    G.payoff σ 0 = - G.payoff σ 1 :=
  add_eq_zero_iff_eq_neg.mp (hzs σ)

/-! ### Decidability

For a finite-strategy two-player game with decidable equality on payoffs,
`IsZeroSum` is checkable by `decide` / `native_decide`. The proof reduces to
`Fintype.decidableForallFintype` on the underlying `∀ σ : G.Profile, …` form. -/

instance IsZeroSum.decidable [Add U] [Zero U] [DecidableEq U]
    {G : StrategicGame (Fin 2) U}
    [∀ i, Fintype (G.strategy i)] :
    Decidable (IsZeroSum G) :=
  Fintype.decidableForallFintype

/-! ### Properties over a linearly ordered field

We use `[Field U] [LinearOrder U] [IsStrictOrderedRing U]` which is the
Mathlib replacement for the deprecated `[LinearOrderedField U]`.

Note: The definitions and the lemmas above only need much weaker classes
(`[Add U] [Zero U]`, `[AddGroup U]`, `[AddCommMonoid U]`). The theorems below
need more structure for `linarith` and Nash equilibrium comparisons. See
`docs/research/zerosum_assumptions.md` for a detailed analysis of minimal
assumptions per concept.
-/

section Properties
set_option linter.unusedSectionVars false
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U]
variable {G : StrategicGame (Fin 2) U}

/-- In a zero-sum game, all Nash equilibria yield the same payoff for player 0.
    [MSZ Theorem 4.44-4.45] -/
theorem IsZeroSum.nash_payoff_eq
    (hzs : IsZeroSum G) {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 0 = G.payoff τ 0 := by
  -- Cross-profile (τ₀, σ₁) = deviate σ 0 (τ 0) = deviate τ 1 (σ 1)
  have hcross : ∀ j : Fin 2, deviate σ 0 (τ 0) j = deviate τ 1 (σ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq : G.payoff (deviate σ 0 (τ 0)) = G.payoff (deviate τ 1 (σ 1)) :=
    congr_arg G.payoff (funext hcross)
  -- σ₀ best-responds to σ₁: payoff(σ) ≥ payoff(τ₀, σ₁)
  have h1 := hσ 0 (τ 0)
  -- τ₁ best-responds to τ₀: payoff(τ,1) ≥ payoff(τ₀, σ₁, 1)
  have h2 := hτ 1 (σ 1)
  -- Zero-sum: convert player 1 inequality to player 0
  have hzc := hzs.neg (deviate σ 0 (τ 0))
  have hzt := hzs.neg τ
  -- From h2 + zero-sum: payoff(τ₀,σ₁, 0) ≥ payoff(τ, 0)
  have hge : G.payoff τ 0 ≤ G.payoff σ 0 := by
    -- hzc: payoff(cross,1) = -payoff(cross,0) where cross = deviate σ 0 (τ 0)
    -- h2: payoff(deviate τ 1 (σ 1),1) ≤ payoff(τ,1)
    -- hpeq: payoff(cross) = payoff(deviate τ 1 (σ 1))
    have heq0 : G.payoff (deviate σ 0 (τ 0)) 0 = G.payoff (deviate τ 1 (σ 1)) 0 :=
      congr_fun hpeq 0
    have heq1 : G.payoff (deviate σ 0 (τ 0)) 1 = G.payoff (deviate τ 1 (σ 1)) 1 :=
      congr_fun hpeq 1
    -- Now linarith can combine these
    linarith
  -- Symmetric: swap σ and τ
  have hcross' : ∀ j : Fin 2, deviate τ 0 (σ 0) j = deviate σ 1 (τ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq' : G.payoff (deviate τ 0 (σ 0)) = G.payoff (deviate σ 1 (τ 1)) :=
    congr_arg G.payoff (funext hcross')
  have h3 := hτ 0 (σ 0)
  have h4 := hσ 1 (τ 1)
  have hzc' := hzs.neg (deviate τ 0 (σ 0))
  have hzs' := hzs.neg σ
  have hle : G.payoff σ 0 ≤ G.payoff τ 0 := by
    have heq0' : G.payoff (deviate τ 0 (σ 0)) 0 = G.payoff (deviate σ 1 (τ 1)) 0 :=
      congr_fun hpeq' 0
    have heq1' : G.payoff (deviate τ 0 (σ 0)) 1 = G.payoff (deviate σ 1 (τ 1)) 1 :=
      congr_fun hpeq' 1
    linarith
  linarith

/-- In a zero-sum game, all Nash equilibria yield the same payoff for player 1. -/
theorem IsZeroSum.nash_payoff_eq_p1
    (hzs : IsZeroSum G) {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 1 = G.payoff τ 1 := by
  linarith [hzs.neg σ, hzs.neg τ, hzs.nash_payoff_eq hσ hτ]

/-! ### Constant-sum Nash payoff uniqueness [MSZ 4.44–4.45]

The same argument as `IsZeroSum.nash_payoff_eq` goes through verbatim: the only
use of `hzs.neg` becomes the constant-sum equation `payoff σ 0 + payoff σ 1 = c`
fed to `linarith`. -/

/-- In a constant-sum game, all Nash equilibria yield the same payoff for player 0.
    [MSZ Theorem 4.44–4.45] -/
theorem IsConstantSum.nash_payoff_eq
    {c : U} (hcs : IsConstantSum G c)
    {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 0 = G.payoff τ 0 := by
  have hcross : ∀ j : Fin 2, deviate σ 0 (τ 0) j = deviate τ 1 (σ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq : G.payoff (deviate σ 0 (τ 0)) = G.payoff (deviate τ 1 (σ 1)) :=
    congr_arg G.payoff (funext hcross)
  have h1 := hσ 0 (τ 0)
  have h2 := hτ 1 (σ 1)
  have hcc := hcs (deviate σ 0 (τ 0))
  have hct := hcs τ
  have hge : G.payoff τ 0 ≤ G.payoff σ 0 := by
    have heq0 : G.payoff (deviate σ 0 (τ 0)) 0 = G.payoff (deviate τ 1 (σ 1)) 0 :=
      congr_fun hpeq 0
    have heq1 : G.payoff (deviate σ 0 (τ 0)) 1 = G.payoff (deviate τ 1 (σ 1)) 1 :=
      congr_fun hpeq 1
    linarith
  have hcross' : ∀ j : Fin 2, deviate τ 0 (σ 0) j = deviate σ 1 (τ 1) j := by
    intro j; rcases j with ⟨j, hj⟩
    simp only [deviate, Function.update]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hpeq' : G.payoff (deviate τ 0 (σ 0)) = G.payoff (deviate σ 1 (τ 1)) :=
    congr_arg G.payoff (funext hcross')
  have h3 := hτ 0 (σ 0)
  have h4 := hσ 1 (τ 1)
  have hcc' := hcs (deviate τ 0 (σ 0))
  have hcs' := hcs σ
  have hle : G.payoff σ 0 ≤ G.payoff τ 0 := by
    have heq0' : G.payoff (deviate τ 0 (σ 0)) 0 = G.payoff (deviate σ 1 (τ 1)) 0 :=
      congr_fun hpeq' 0
    have heq1' : G.payoff (deviate τ 0 (σ 0)) 1 = G.payoff (deviate σ 1 (τ 1)) 1 :=
      congr_fun hpeq' 1
    linarith
  linarith

/-- In a constant-sum game, all Nash equilibria yield the same payoff for player 1. -/
theorem IsConstantSum.nash_payoff_eq_p1
    {c : U} (hcs : IsConstantSum G c)
    {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 1 = G.payoff τ 1 := by
  linarith [hcs σ, hcs τ, hcs.nash_payoff_eq hσ hτ]

/-! ### Mixed-strategy lift

The zero-sum property propagates linearly through expected payoff (a finite
sum of products of pure payoffs). These let downstream files avoid hand-rolled
sum manipulations at every mixed-strategy use site. -/

variable [∀ i, Fintype (G.strategy i)]

/-- In a zero-sum game, player 1's expected payoff is the negation of player 0's. -/
theorem IsZeroSum.expectedPayoff_neg
    (hzs : IsZeroSum G) (p : StrategicGame.MixedProfile G) :
    StrategicGame.expectedPayoff G p 1
      = -(StrategicGame.expectedPayoff G p 0) := by
  unfold StrategicGame.expectedPayoff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hzs.neg σ]
  ring

/-- In a zero-sum game, player 0's expected payoff is the negation of player 1's. -/
theorem IsZeroSum.expectedPayoff_neg'
    (hzs : IsZeroSum G) (p : StrategicGame.MixedProfile G) :
    StrategicGame.expectedPayoff G p 0
      = -(StrategicGame.expectedPayoff G p 1) := by
  rw [hzs.expectedPayoff_neg, neg_neg]

/-- Mixed-strategy version of the zero-sum axiom: expected payoffs sum to `0`. -/
@[simp] theorem IsZeroSum.expectedPayoff_add_zero
    (hzs : IsZeroSum G) (p : StrategicGame.MixedProfile G) :
    StrategicGame.expectedPayoff G p 0 + StrategicGame.expectedPayoff G p 1 = 0 := by
  rw [hzs.expectedPayoff_neg]; ring

end Properties

end StrategicGame
