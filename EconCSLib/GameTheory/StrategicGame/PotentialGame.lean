/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.GameTheory.StrategicGame.PotentialGame

Potential games: games admitting a potential function that captures
all unilateral incentives.

## Main definitions

* `IsExactPotential` — exact potential function
* `IsOrdinalPotential` — ordinal potential function

## Main results

* `IsExactPotential.maximizer_is_nash` — maximizer of an exact potential is Nash
* `IsOrdinalPotential.isNash_iff_localMax` — Nash ↔ local max of ordinal potential

## References

* [AGT] Chapter 18
* Monderer, D. and Shapley, L.S. (1996). "Potential Games".
-/

namespace StrategicGame

variable {N U : Type*} [DecidableEq N]

open StrategicGame

section Definitions
variable [Sub U] [Preorder U] {G : StrategicGame N U}

/-- An exact potential function: the change in `Φ` equals the change in
    the deviating player's payoff. -/
def IsExactPotential (G : StrategicGame N U) (Φ : G.Profile → U) : Prop :=
  ∀ (i : N) (σ : G.Profile) (s' : G.strategy i),
    G.payoff (deviate σ i s') i - G.payoff σ i =
    Φ (deviate σ i s') - Φ σ

/-- An ordinal potential function: a unilateral deviation improves payoff
    iff it increases Φ. -/
def IsOrdinalPotential (G : StrategicGame N U) (Φ : G.Profile → U) : Prop :=
  ∀ (i : N) (σ : G.Profile) (s' : G.strategy i),
    G.payoff (deviate σ i s') i > G.payoff σ i ↔
    Φ (deviate σ i s') > Φ σ

end Definitions

section Theorems
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U]
variable {G : StrategicGame N U}

set_option linter.unusedSectionVars false

/-- A profile maximizing an exact potential is a Nash equilibrium. -/
theorem IsExactPotential.maximizer_is_nash {Φ : G.Profile → U}
    (hΦ : IsExactPotential G Φ) {σ : G.Profile}
    (hmax : ∀ τ : G.Profile, Φ σ ≥ Φ τ) :
    IsNashEquilibrium G σ := by
  intro i s'
  -- Need: payoff(deviate σ i s', i) ≤ payoff(σ, i)
  -- By exact potential: payoff(dev) - payoff(σ) = Φ(dev) - Φ(σ)
  have h := hΦ i σ s'
  -- h : payoff(dev) - payoff(σ) = Φ(dev) - Φ(σ)
  -- hmax : Φ(σ) ≥ Φ(dev), i.e., Φ(dev) - Φ(σ) ≤ 0
  have hle : Φ (deviate σ i s') - Φ σ ≤ 0 := sub_nonpos.mpr (hmax _)
  -- So payoff(dev) - payoff(σ) ≤ 0, i.e., payoff(dev) ≤ payoff(σ)
  linarith

/-- Nash ↔ local maximizer of ordinal potential. -/
theorem IsOrdinalPotential.isNash_iff_localMax {Φ : G.Profile → U}
    (hΦ : IsOrdinalPotential G Φ) {σ : G.Profile} :
    IsNashEquilibrium G σ ↔
    ∀ i (s' : G.strategy i), Φ σ ≥ Φ (deviate σ i s') := by
  constructor
  · -- Nash → local max: if payoff doesn't improve, Φ doesn't improve
    intro hN i s'
    by_contra h
    push_neg at h
    -- h: Φ(deviate) > Φ(σ), so by ordinal potential: payoff(deviate) > payoff(σ)
    have := (hΦ i σ s').mpr h
    -- But Nash says payoff(deviate) ≤ payoff(σ)
    exact absurd this (not_lt.mpr (hN i s'))
  · -- Local max → Nash: if Φ doesn't improve, payoff doesn't improve
    intro hmax i s'
    by_contra h
    push_neg at h
    -- h: payoff(deviate) > payoff(σ), so by ordinal potential: Φ(deviate) > Φ(σ)
    have := (hΦ i σ s').mp h
    -- But local max says Φ(deviate) ≤ Φ(σ)
    exact absurd this (not_lt.mpr (hmax i s'))

end Theorems

end StrategicGame
