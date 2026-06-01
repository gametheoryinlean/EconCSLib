/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Fairness
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# EconCSLib.SocialChoice.FairDivision.Welfare

Shared social-welfare objectives for the standard no-externality cardinal
fair-division layer.
-/

namespace SocialChoice
namespace FairDivision

open BigOperators

variable {N S : Type*}

/-- Utilitarian welfare: the sum of agents' utilities from their own shares. -/
noncomputable def utilitarianWelfare [Fintype N]
    (u : N → S → ℝ) (A : Allocation N S) : ℝ :=
  ∑ i : N, u i (A i)

/-- Egalitarian welfare: the minimum utility among agents. -/
noncomputable def egalitarianWelfare [Fintype N] [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S) : ℝ :=
  Finset.univ.inf' ⟨Classical.arbitrary N, Finset.mem_univ _⟩ (fun i => u i (A i))

/-- Utilitarian optimality: no feasible allocation has larger utilitarian welfare. -/
def IsUtilitarianOptimal [Fintype N]
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ B : Allocation N S, feasible B →
    utilitarianWelfare u B ≤ utilitarianWelfare u A

/-- Maximin optimality: no feasible allocation has larger egalitarian welfare. -/
def IsMaxmin [Fintype N] [Nonempty N]
    (feasible : Allocation N S → Prop)
    (u : N → S → ℝ) (A : Allocation N S) : Prop :=
  ∀ B : Allocation N S, feasible B →
    egalitarianWelfare u B ≤ egalitarianWelfare u A

section BasicLemmas

variable [Fintype N]

/-- Utilitarian welfare is monotone: pointwise improvement implies welfare improvement. -/
lemma utilitarianWelfare_mono
    (u : N → S → ℝ) (A B : Allocation N S)
    (h : ∀ i : N, u i (A i) ≤ u i (B i)) :
    utilitarianWelfare u A ≤ utilitarianWelfare u B :=
  Finset.sum_le_sum (fun i _ => h i)

/-- For a unique agent, utilitarian welfare is just that agent's utility. -/
@[simp]
lemma utilitarianWelfare_unique [Unique N]
    (u : N → S → ℝ) (A : Allocation N S) :
    utilitarianWelfare u A = u default (A default) := by
  simp [utilitarianWelfare]

/-- Egalitarian welfare is bounded above by each agent's utility. -/
lemma egalitarianWelfare_le [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S) (i : N) :
    egalitarianWelfare u A ≤ u i (A i) :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- Without division, egalitarian welfare is bounded above by utilitarian welfare
    multiplied by the number of agents. -/
lemma nsmul_egalitarianWelfare_le_utilitarianWelfare
    [Nonempty N]
    (u : N → S → ℝ) (A : Allocation N S)
    (hle : ∀ i : N, egalitarianWelfare u A ≤ u i (A i)) :
    Fintype.card N • egalitarianWelfare u A ≤ utilitarianWelfare u A := by
  calc Fintype.card N • egalitarianWelfare u A
      = ∑ _i : N, egalitarianWelfare u A := by
          simp [Finset.sum_const, Finset.card_univ]
    _ ≤ ∑ i : N, u i (A i) := Finset.sum_le_sum (fun i _ => hle i)
    _ = utilitarianWelfare u A := rfl

end BasicLemmas

end FairDivision
end SocialChoice
