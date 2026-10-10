/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Product
import Mathlib.Data.Fintype.BigOperators

/-!
# Conditioning finite executable laws

Conditioning is deliberately partial.  A positive-mass Boolean event produces
the exact rationally normalized restriction; a zero-mass event produces
`none`.  In particular, this layer never invents an off-path posterior through
classical choice.

## Main definitions

* `FiniteLaw.condition?` and `FiniteLaw.conditionOnFiber`;
* `FiniteLaw.FiberPossible` for the positive-mass precondition.

## Main statements

* `FiniteLaw.mass_conditionOnFiber` is the exact normalized mass formula;
* `FiniteLaw.Equivalent.conditionOnFiber` preserves semantic equivalence;
* `FiniteLaw.fintypePi_conditionOnFiber_apply` conditions one independent coordinate.
-/

namespace FiniteLaw

universe uα uβ

/-! ## Restriction to a Boolean event -/

section Events

variable {α : Type*}

/-- Keep event atoms at their old weight and zero every other occurrence. -/
private def restrictAtoms (law : FiniteLaw α) (event : α → Bool) :
    List (α × ℚ≥0) :=
  law.atoms.map fun atom =>
    (atom.1, if event atom.1 then atom.2 else 0)

private lemma totalWeight_restrictAtoms
    (law : FiniteLaw α) (event : α → Bool) :
    totalWeight (restrictAtoms law event) = law.eventMass event := by
  simp [restrictAtoms, totalWeight, eventMass, List.map_map,
    Function.comp_def]

private lemma restrictedMass [DecidableEq α]
    (law : FiniteLaw α) (event : α → Bool) (outcome : α) :
    ((restrictAtoms law event).map fun atom =>
      if atom.1 = outcome then atom.2 else 0).sum =
      if event outcome then law.mass outcome else 0 := by
  unfold restrictAtoms mass eventMass
  simp only [List.map_map, Function.comp_def]
  by_cases hevent : event outcome
  · rw [if_pos hevent]
    apply congrArg List.sum
    apply List.map_congr_left
    intro atom _
    by_cases heq : atom.1 = outcome
    · subst outcome
      simp [hevent]
    · simp [heq]
  · rw [if_neg hevent]
    apply List.sum_eq_zero
    intro term hterm
    rw [List.mem_map] at hterm
    obtain ⟨atom, _, rfl⟩ := hterm
    by_cases heq : atom.1 = outcome
    · subst outcome
      simp [hevent]
    · simp [heq]

/-- Conditional law on an executable event.

Returns `none` exactly when the event has zero mass. -/
def condition? (law : FiniteLaw α) (event : α → Bool) :
    Option (FiniteLaw α) :=
  normalize? (restrictAtoms law event)

@[simp]
lemma condition?_eq_none_iff
    (law : FiniteLaw α) (event : α → Bool) :
    law.condition? event = none ↔ law.eventMass event = 0 := by
  rw [condition?, normalize?_eq_none_iff,
    totalWeight_restrictAtoms]

end Events

/-! ## Conditioning on an observed value -/

section Fibers

/-- The observed fiber has positive exact mass. -/
def FiberPossible [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β) : Prop :=
  law.eventMass (fun sample => decide (observe sample = value)) ≠ 0

/-- Posterior law after observing one fiber.

An impossible fiber returns `none`; no off-path law is manufactured. -/
def conditionOnFiber [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β) :
    Option (FiniteLaw α) :=
  law.condition?
    (fun sample => decide (observe sample = value))

/-- A fiber posterior is absent exactly when the observed fiber has zero
mass. -/
@[simp]
private lemma conditionOnFiber_eq_none_iff [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β) :
    law.conditionOnFiber observe value = none ↔
      law.eventMass
        (fun sample => decide (observe sample = value)) = 0 := by
  exact condition?_eq_none_iff law _

private lemma eventMass_ne_zero_of_conditionOnFiber_eq_some [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β)
    {conditioned : FiniteLaw α}
    (hconditioned : law.conditionOnFiber observe value = some conditioned) :
    law.eventMass (fun sample => decide (observe sample = value)) ≠ 0 := by
  intro hzero
  have hnone := (conditionOnFiber_eq_none_iff law observe value).mpr hzero
  rw [hconditioned] at hnone
  exact Option.some_ne_none _ hnone

/-- A zero-mass fiber has no posterior. -/
lemma conditionOnFiber_of_impossible [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β)
    (himpossible : ¬ law.FiberPossible observe value) :
    law.conditionOnFiber observe value = none := by
  unfold FiberPossible at himpossible
  have hzero :
      law.eventMass
        (fun sample => decide (observe sample = value)) = 0 :=
    not_ne_iff.mp himpossible
  exact (conditionOnFiber_eq_none_iff law observe value).mpr hzero

/-- Point mass of a successfully computed fiber posterior. -/
theorem mass_conditionOnFiber [DecidableEq α] [DecidableEq β]
    (law : FiniteLaw α) (observe : α → β) (value : β)
    (conditioned : FiniteLaw α)
    (hconditioned :
      law.conditionOnFiber observe value = some conditioned)
    (outcome : α) :
    conditioned.mass outcome =
      if observe outcome = value then
        law.mass outcome /
          law.eventMass
            (fun sample => decide (observe sample = value))
      else 0 := by
  have hnonzero :=
    eventMass_ne_zero_of_conditionOnFiber_eq_some law observe value hconditioned
  have htotal :
      totalWeight
          (restrictAtoms law
            (fun sample => decide (observe sample = value))) ≠ 0 := by
    rw [totalWeight_restrictAtoms]
    exact hnonzero
  have hcondition :
      conditioned =
        normalize
          (restrictAtoms law
            (fun sample => decide (observe sample = value)))
          htotal := by
    unfold conditionOnFiber condition? normalize? at hconditioned
    simp [htotal] at hconditioned
    exact hconditioned.symm
  rw [hcondition, mass_normalize,
    totalWeight_restrictAtoms, restrictedMass]
  by_cases heq : observe outcome = value
  · simp [heq]
  · simp [heq]

/-- Fiber conditioning respects semantic equivalence and propagates absence
on zero-mass fibers. -/
theorem Equivalent.conditionOnFiber
    [DecidableEq α] [DecidableEq β]
    {left right : FiniteLaw α}
    (h : left.Equivalent right)
    (observe : α → β) (value : β) :
    Option.Rel Equivalent
      (left.conditionOnFiber observe value)
      (right.conditionOnFiber observe value) := by
  have hevent :
      left.eventMass
          (fun sample => decide (observe sample = value)) =
        right.eventMass
          (fun sample => decide (observe sample = value)) :=
    h.eventMass
    (fun sample => decide (observe sample = value))
  by_cases hzero :
      left.eventMass
        (fun sample => decide (observe sample = value)) = 0
  · have hleft : left.conditionOnFiber observe value = none :=
      (conditionOnFiber_eq_none_iff left observe value).2 hzero
    have hright : right.conditionOnFiber observe value = none :=
      (conditionOnFiber_eq_none_iff right observe value).2
        (hevent ▸ hzero)
    rw [hleft, hright]
    exact Option.Rel.none
  · have hleft : left.conditionOnFiber observe value ≠ none := by
      simpa [conditionOnFiber_eq_none_iff] using hzero
    have hright : right.conditionOnFiber observe value ≠ none := by
      intro hnone
      exact hzero (hevent.trans
        ((conditionOnFiber_eq_none_iff right observe value).1 hnone))
    obtain ⟨leftConditioned, hleftConditioned⟩ :=
      Option.ne_none_iff_exists'.mp hleft
    obtain ⟨rightConditioned, hrightConditioned⟩ :=
      Option.ne_none_iff_exists'.mp hright
    rw [hleftConditioned, hrightConditioned]
    apply Option.Rel.some
    apply Equivalent.of_mass_eq
    intro outcome
    rw [mass_conditionOnFiber left observe value leftConditioned
      hleftConditioned outcome,
      mass_conditionOnFiber right observe value rightConditioned
        hrightConditioned outcome, ← hevent]
    have hmass : left.mass outcome = right.mass outcome := by
      simpa [mass] using
        h.eventMass (fun sample => decide (sample = outcome))
    rw [hmass]

/-- Fiber conditioning is independent of the particular equality decision
procedure supplied for the observed value type. -/
lemma conditionOnFiber_decidableEq_irrel
    (first second : DecidableEq β)
    (law : FiniteLaw α) (observe : α → β) (value : β) :
    (@conditionOnFiber (α := α) (β := β)
      first law observe value) =
      (@conditionOnFiber (α := α) (β := β)
        second law observe value) := by
  have hinstance : first = second := Subsingleton.elim _ _
  subst second
  rfl

end Fibers

/-! ## Conditioning independent tables -/

section IndependentTables

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type uα}

-- An event on one coordinate has exactly its marginal probability.
private lemma eventMass_fintypePi_apply
    (laws : (i : I) → FiniteLaw (X i)) (selected : I)
    (event : X selected → Bool) :
    (fintypePi laws).eventMass (fun tuple => event (tuple selected)) =
      (laws selected).eventMass event := by
  have hmarginal := (fintypePi_map_apply laws selected).eventMass event
  simpa only [eventMass_map, Function.comp_def] using hmarginal

variable [∀ i, DecidableEq (X i)] [DecidableEq ((i : I) → X i)]
variable (laws : (i : I) → FiniteLaw (X i)) (selected : I)

-- Updating one factor leaves the product over all other coordinates unchanged.
private lemma mass_fintypePi_update (selectedLaw : FiniteLaw (X selected))
    (tuple : (i : I) → X i) :
    (fintypePi (Function.update laws selected selectedLaw)).mass tuple =
      selectedLaw.mass (tuple selected) *
        ∏ i : {i : I // i ≠ selected}, (laws i.1).mass (tuple i.1) := by
  rw [fintypePi_mass, Fintype.prod_eq_mul_prod_subtype_ne _ selected]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Function.update_of_ne i.2]

section PosteriorMass

variable (value : X selected) (selectedLaw : FiniteLaw (X selected))
variable (productLaw : FiniteLaw ((i : I) → X i))
variable (hselected : (laws selected).conditionOnFiber id value = some selectedLaw)
variable (hproduct :
  (fintypePi laws).conditionOnFiber (fun tuple => tuple selected) value = some productLaw)

include hselected hproduct

-- Successful conditioning replaces precisely the selected factor.
private lemma conditioned_fintypePi_equivalent :
    productLaw.Equivalent (fintypePi (Function.update laws selected selectedLaw)) := by
  apply Equivalent.of_mass_eq
  intro tuple
  rw [mass_conditionOnFiber (fintypePi laws) (fun tuple => tuple selected)
      value productLaw hproduct tuple,
    fintypePi_mass,
    eventMass_fintypePi_apply laws selected (fun outcome => decide (outcome = value)),
    Fintype.prod_eq_mul_prod_subtype_ne _ selected,
    mass_fintypePi_update,
    mass_conditionOnFiber (laws selected) id value selectedLaw hselected]
  change
    (if tuple selected = value then
        ((laws selected).mass (tuple selected) *
          ∏ i : {i : I // i ≠ selected}, (laws i.1).mass (tuple i.1)) /
            (laws selected).eventMass (fun outcome => decide (outcome = value))
      else 0) =
      (if tuple selected = value then
          (laws selected).mass (tuple selected) /
            (laws selected).eventMass (fun outcome => decide (outcome = value))
        else 0) *
          ∏ i : {i : I // i ≠ selected}, (laws i.1).mass (tuple i.1)
  by_cases heq : tuple selected = value
  · simp [heq, div_mul_eq_mul_div]
  · simp [heq]

end PosteriorMass

/-- Conditioning one coordinate of an independent finite table preserves
independence and updates exactly that coordinate, up to sparse-presentation
equivalence. -/
theorem fintypePi_conditionOnFiber_apply (value : X selected) :
    Option.Rel Equivalent
      ((fintypePi laws).conditionOnFiber
        (fun tuple => tuple selected) value)
      ((laws selected).conditionOnFiber id value |>.map
        (fun selectedLaw =>
          fintypePi (Function.update laws selected selectedLaw))) := by
  have heventMass := eventMass_fintypePi_apply laws selected
    (fun outcome => decide (outcome = value))
  cases hselected : (laws selected).conditionOnFiber id value with
  | none =>
      have hproduct :
          (fintypePi laws).conditionOnFiber (fun tuple => tuple selected) value = none := by
        apply (conditionOnFiber_eq_none_iff _ _ _).2
        rw [heventMass]
        exact (conditionOnFiber_eq_none_iff (laws selected) id value).1 hselected
      rw [hproduct]
      exact Option.Rel.none
  | some selectedLaw =>
      have hnonzero :=
        eventMass_ne_zero_of_conditionOnFiber_eq_some (laws selected) id value hselected
      have hproductSome :
          (fintypePi laws).conditionOnFiber (fun tuple => tuple selected) value ≠ none := by
        intro hnone
        apply hnonzero
        simpa only [id_eq] using
          heventMass.symm.trans ((conditionOnFiber_eq_none_iff _ _ _).1 hnone)
      obtain ⟨productLaw, hproduct⟩ := Option.ne_none_iff_exists'.mp hproductSome
      rw [hproduct]
      exact Option.Rel.some
        (conditioned_fintypePi_equivalent laws selected value selectedLaw productLaw
          hselected hproduct)

end IndependentTables

end FiniteLaw
