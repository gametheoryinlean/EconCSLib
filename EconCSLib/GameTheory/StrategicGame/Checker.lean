/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.NashEquilibrium

/-!
# EconCSLib.GameTheory.StrategicGame.Checker

Executable Nash equilibrium checker for finite strategic games.

## Main definitions

* `isNashEq` — `Bool`-valued Nash checker
* `isNashEq_iff` — soundness and completeness: `isNashEq G σ = true ↔ IsNashEquilibrium G σ`
-/

variable {N U : Type*} [DecidableEq N] [Preorder U] [DecidableRel (· ≤ · : U → U → Prop)]

open StrategicGame

/-- Executable Nash equilibrium checker.
    Returns `true` iff `σ` is a pure Nash equilibrium of `G`. -/
def isNashEq [Fintype N] (G : StrategicGame N U) [∀ i, Fintype (G.strategy i)]
    (σ : G.Profile) : Bool :=
  decide (∀ i : N, ∀ s' : G.strategy i, G.payoff (deviate σ i s') i ≤ G.payoff σ i)

/-- T6: The checker correctly decides Nash equilibrium (soundness and completeness). -/
theorem isNashEq_iff [Fintype N] (G : StrategicGame N U) [∀ i, Fintype (G.strategy i)]
    (σ : G.Profile) :
    isNashEq G σ = true ↔ IsNashEquilibrium G σ := by
  simp [isNashEq, IsNashEquilibrium, IsBestResponse]
