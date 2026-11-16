/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EconCSLib.Math.Probability.PMF.Equiv

Pushforward equivalences for discrete probability mass functions.

`PMF.mapEquiv e` packages pushforward along a type equivalence `e` as an
equivalence between the corresponding PMF types. Its inverse is pushforward
along `e.symm`; the two inverse laws follow from `PMF.map_comp`.

## Main definitions and results

* `PMF.mapEquiv`;
* `PMF.mapEquiv_apply`;
* `PMF.mapEquiv_symm_apply`;
* `PMF.map_equiv_apply`.
-/

namespace PMF

universe uα uβ

/-- Pushforward of probability mass functions along a type equivalence is
itself an equivalence. -/
noncomputable def mapEquiv {α : Type uα} {β : Type uβ}
    (e : α ≃ β) : PMF α ≃ PMF β where
  toFun := fun probability => probability.map e
  invFun := fun probability => probability.map e.symm
  left_inv := by
    intro probability
    change (probability.map e).map e.symm = probability
    rw [PMF.map_comp]
    have hcomp : (e.symm : β → α) ∘ (e : α → β) = id := by
      funext value
      exact e.symm_apply_apply value
    rw [hcomp, PMF.map_id]
  right_inv := by
    intro probability
    change (probability.map e.symm).map e = probability
    rw [PMF.map_comp]
    have hcomp : (e : α → β) ∘ (e.symm : β → α) = id := by
      funext value
      exact e.apply_symm_apply value
    rw [hcomp, PMF.map_id]

@[simp]
theorem mapEquiv_apply {α : Type uα} {β : Type uβ}
    (e : α ≃ β) (probability : PMF α) :
    mapEquiv e probability = probability.map e :=
  rfl

@[simp]
theorem mapEquiv_symm_apply {α : Type uα} {β : Type uβ}
    (e : α ≃ β) (probability : PMF β) :
    (mapEquiv e).symm probability = probability.map e.symm :=
  rfl

/-- Mapping a PMF along an equivalence merely reindexes its point masses. -/
theorem map_equiv_apply
    {α : Type uα} {β : Type uβ}
    (p : PMF α) (e : α ≃ β) (b : β) :
    (p.map e) b = p (e.symm b) := by
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    have himage : b ≠ e a := by
      intro hab
      apply ha
      calc
        a = e.symm (e a) := (e.symm_apply_apply a).symm
        _ = e.symm b := congrArg e.symm hab.symm
    simp [himage]

end PMF
