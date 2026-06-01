/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Basic

/-!
# EconCSLib.SocialChoice.FairDivision.Fairness

Shared fairness and efficiency predicates for the standard cardinal
no-externality fair-division layer.

Only genuinely share-generic notions belong here. Item-removal notions such as
EF1/EFX and cake-specific measurability or contiguity conditions belong in lower
specialized modules.
-/

namespace SocialChoice
namespace FairDivision

variable {N S : Type*}

/-- Envy-free: every agent weakly prefers their own share to every other
    agent's share. -/
def IsEnvyFree
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i j : N, u i (A j) ≤ u i (A i)

/-- Proportional: each agent values their share at least `1 / n` of a
    distinguished whole share, stated without division. -/
def IsProportional (n : ℕ)
    (whole : S) (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i : N, u i whole ≤ (n : ℝ) * u i (A i)

/-- Equitable: all agents obtain the same utility from their own shares. -/
def IsEquitable (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ i j : N, u i (A i) = u j (A j)

/-- Pareto optimal: there is no feasible allocation that weakly improves every
    agent and strictly improves at least one. -/
def IsParetoOptimal
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ¬ ∃ B : Allocation N S, feasible B ∧
    (∀ i : N, u i (A i) ≤ u i (B i)) ∧
    (∃ i : N, u i (A i) < u i (B i))

end FairDivision
end SocialChoice
