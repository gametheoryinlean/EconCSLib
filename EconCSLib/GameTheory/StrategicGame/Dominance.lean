/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.BestResponse

/-!
# EconCSLib.GameTheory.StrategicGame.Dominance

Dominance relations between strategies.

## Main definitions

* `WeaklyDominates` — `s` yields at least as high payoff as `s'` against all opponents
* `StrictlyDominates` — `s` yields strictly higher payoff than `s'` against all opponents
* `IsWeaklyDominant` / `IsStrictlyDominant` — dominates every alternative

## Main results

* T2: `IsWeaklyDominant.isBestResponse` — a weakly dominant strategy is always a best response
-/

variable {N U : Type*} [DecidableEq N] [Preorder U]

open StrategicGame

/-- Strategy `s` weakly dominates strategy `s'` for player `i`. -/
def WeaklyDominates (G : StrategicGame N U) (i : N) (s s' : G.strategy i) : Prop :=
  ∀ σ : G.Profile, G.payoff (deviate σ i s') i ≤ G.payoff (deviate σ i s) i

/-- Strategy `s` strictly dominates strategy `s'` for player `i`. -/
def StrictlyDominates (G : StrategicGame N U) (i : N) (s s' : G.strategy i) : Prop :=
  ∀ σ : G.Profile, G.payoff (deviate σ i s') i < G.payoff (deviate σ i s) i

/-- Strategy `s` is weakly dominant for player `i`. -/
def IsWeaklyDominant (G : StrategicGame N U) (i : N) (s : G.strategy i) : Prop :=
  ∀ s' : G.strategy i, WeaklyDominates G i s s'

/-- Strategy `s` is strictly dominant for player `i`. -/
def IsStrictlyDominant (G : StrategicGame N U) (i : N) (s : G.strategy i) : Prop :=
  ∀ s' : G.strategy i, s ≠ s' → StrictlyDominates G i s s'

/-- Strict dominance implies weak dominance. -/
theorem StrictlyDominates.weakly {G : StrategicGame N U} {i : N} {s s' : G.strategy i}
    (h : StrictlyDominates G i s s') : WeaklyDominates G i s s' :=
  fun σ => le_of_lt (h σ)

/-- A strictly dominant strategy is weakly dominant. -/
theorem IsStrictlyDominant.isWeaklyDominant {G : StrategicGame N U} {i : N} {s : G.strategy i}
    [DecidableEq (G.strategy i)]
    (h : IsStrictlyDominant G i s) : IsWeaklyDominant G i s := by
  intro s'
  by_cases heq : s = s'
  · subst heq; intro σ; exact le_refl _
  · exact (h s' heq).weakly

/-- T2: A weakly dominant strategy is a best response to any profile where player `i` plays it. -/
theorem IsWeaklyDominant.isBestResponse {G : StrategicGame N U} {i : N} {s : G.strategy i}
    (hdom : IsWeaklyDominant G i s) (σ : G.Profile) (hσ : σ i = s) :
    IsBestResponse G σ i := by
  intro s'
  have h := hdom s' σ
  simp only [← hσ, Profile.deviate_self] at h
  exact h
