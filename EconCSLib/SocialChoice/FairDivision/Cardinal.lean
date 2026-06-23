/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Welfare
import Mathlib.Data.Real.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Cardinal

Cardinal enrichments of the shared fair-division layer.

The primary interface here is the standard no-externality model
`CardinalInstance`, where each agent assigns a real value to an individual
share. It is independent from the ordinal `ShareInstance` layer; bridges derive
ordinal preferences from utility when needed.
-/

namespace SocialChoice
namespace FairDivision

/-- A real-valued cardinal fair-division instance in the standard no-externality
    model. -/
structure CardinalInstance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Utility assigned by each agent to each individual share. -/
  utility : N → S → ℝ

namespace CardinalInstance

/-- The share preference induced by a cardinal utility, using the convention that
    higher utility means weakly better. -/
def inducedSharePref {N R S : Type*}
    (I : CardinalInstance N R S) : N → Pref S :=
  fun i =>
    { rel := fun s t => I.utility i t ≤ I.utility i s
      prop :=
        { reflexive := ⟨fun s => le_rfl⟩
          transitive := ⟨fun _ _ _ hst htu => le_trans htu hst⟩
          total := fun s t =>
            by
              rcases le_total (I.utility i s) (I.utility i t) with h | h
              · exact Or.inr h
              · exact Or.inl h } }

/-- Convert a cardinal instance to the induced ordinal no-externality instance. -/
def toShareInstance {N R S : Type*}
    (I : CardinalInstance N R S) : ShareInstance N R S where
  resource := I.resource
  feasible := I.feasible
  sharePref := I.inducedSharePref

/-- An ordinal share instance is represented by a cardinal instance when its
    weak share preferences agree with the utility-induced weak order. -/
def UtilityRepresentsSharePref {N R S : Type*}
    (I₁ : ShareInstance N R S) (I₂ : CardinalInstance N R S) : Prop :=
  ∀ i s t, I₁.sharePref i s t ↔ I₂.utility i t ≤ I₂.utility i s

/-! ### Instance-relative fairness and welfare wrappers -/

/-- Envy-freeness for a cardinal instance. -/
def IsEnvyFree {N R S : Type*}
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsEnvyFree I.utility A

/-- Proportionality for a cardinal instance, relative to a distinguished whole
    share and a supplied population size. -/
def IsProportional {N R S : Type*}
    (I : CardinalInstance N R S) (n : ℕ) (whole : S)
    (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsProportional n whole I.utility A

/-- Equitability for a cardinal instance. -/
def IsEquitable {N R S : Type*}
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsEquitable I.utility A

/-- Pareto optimality for a cardinal instance, using the instance feasibility
    predicate. -/
def IsParetoOptimal {N R S : Type*}
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsParetoOptimal I.feasible I.utility A

/-- Utilitarian welfare for a cardinal instance. -/
noncomputable def utilitarianWelfare {N R S : Type*} [Fintype N]
    (I : CardinalInstance N R S) (A : Allocation N S) : ℝ :=
  SocialChoice.FairDivision.utilitarianWelfare I.utility A

/-- Egalitarian welfare for a cardinal instance. -/
noncomputable def egalitarianWelfare {N R S : Type*} [Fintype N] [Nonempty N]
    (I : CardinalInstance N R S) (A : Allocation N S) : ℝ :=
  SocialChoice.FairDivision.egalitarianWelfare I.utility A

/-- Utilitarian optimality for a cardinal instance, using the instance feasibility
    predicate. -/
def IsUtilitarianOptimal {N R S : Type*} [Fintype N]
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsUtilitarianOptimal I.feasible I.utility A

/-- Maximin optimality for a cardinal instance, using the instance feasibility
    predicate. -/
def IsMaxmin {N R S : Type*} [Fintype N] [Nonempty N]
    (I : CardinalInstance N R S) (A : Allocation N S) : Prop :=
  SocialChoice.FairDivision.IsMaxmin I.feasible I.utility A

end CardinalInstance

end FairDivision
end SocialChoice
