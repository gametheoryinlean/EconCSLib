/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Product

/-!
# Constructive couplings of finite laws

A relational coupling is represented by a finite law on the subtype of
related pairs.  The relation proof therefore travels with every joint atom;
dependent coupling composition never extracts data from an existential proof
and never needs classical choice.

Marginals are compared by exact rational expectations.  Positive-atom
projection equivalences are retained explicitly because support transfer is
part of the executable finite semantics.

## Main definitions

* `FiniteLaw.RelCoupling`;
* `FiniteLaw.relCoupling_refl` and `FiniteLaw.relCoupling_pure`;
* `FiniteLaw.RelCoupling.map` and `FiniteLaw.RelCoupling.bind`.
-/

namespace FiniteLaw

universe uα uβ

/-! ## Coupling data and elementary constructions -/

section Basic

variable {α : Type uα} {β : Type uβ}

/-- An explicit finite coupling supported on `R`.

The joint law ranges over the subtype of related pairs, so every sampled
joint outcome carries its relation witness constructively. -/
structure RelCoupling
    (R : α → β → Prop) (left : FiniteLaw α) (right : FiniteLaw β) where
  /-- Executable finite joint law of related pairs. -/
  joint : FiniteLaw {pair : α × β // R pair.1 pair.2}
  /-- Exact first marginal, expressed by rational observables. -/
  leftEquivalent :
    (joint.map fun pair => pair.1.1).Equivalent left
  /-- Exact second marginal, expressed by rational observables. -/
  rightEquivalent :
    (joint.map fun pair => pair.1.2).Equivalent right
  /-- Positive atoms of the first marginal are represented exactly. -/
  leftPositive :
    ∀ outcome,
      (joint.map fun pair => pair.1.1).HasPositiveAtom outcome ↔
        left.HasPositiveAtom outcome
  /-- Positive atoms of the second marginal are represented exactly. -/
  rightPositive :
    ∀ outcome,
      (joint.map fun pair => pair.1.2).HasPositiveAtom outcome ↔
        right.HasPositiveAtom outcome

/-- A finite law couples to itself along equality. -/
def relCoupling_refl (law : FiniteLaw α) :
    RelCoupling (fun left right : α => left = right) law law := by
  let diagonal : α → {pair : α × α // pair.1 = pair.2} :=
    fun outcome => ⟨(outcome, outcome), rfl⟩
  let joint := law.map diagonal
  have hleft : (joint.map fun pair => pair.1.1) = law := by
    simp only [joint]
    rw [map_comp]
    simpa [diagonal, Function.comp_def] using map_id law
  have hright : (joint.map fun pair => pair.1.2) = law := by
    simp only [joint]
    rw [map_comp]
    simpa [diagonal, Function.comp_def] using map_id law
  exact
    { joint := joint
      leftEquivalent := Equivalent.of_eq hleft
      rightEquivalent := Equivalent.of_eq hright
      leftPositive := fun outcome => by rw [hleft]
      rightPositive := fun outcome => by rw [hright] }

namespace RelCoupling

variable {R : α → β → Prop} {left : FiniteLaw α} {right : FiniteLaw β}
variable (coupling : RelCoupling R left right)

include coupling

/-- Transpose a relational coupling. -/
def symm :
    RelCoupling (fun rightValue leftValue => R leftValue rightValue)
      right left := by
  let swap : {pair : α × β // R pair.1 pair.2} →
      {pair : β × α // R pair.2 pair.1} :=
    fun pair => ⟨(pair.1.2, pair.1.1), pair.2⟩
  let joint := coupling.joint.map swap
  have hleft :
      (joint.map fun pair => pair.1.1) =
        coupling.joint.map (fun pair => pair.1.2) := by
    simp only [joint]
    rw [map_comp]
    rfl
  have hright :
      (joint.map fun pair => pair.1.2) =
        coupling.joint.map (fun pair => pair.1.1) := by
    simp only [joint]
    rw [map_comp]
    rfl
  exact
    { joint := joint
      leftEquivalent :=
        (Equivalent.of_eq hleft).trans coupling.rightEquivalent
      rightEquivalent :=
        (Equivalent.of_eq hright).trans coupling.leftEquivalent
      leftPositive := fun outcome => by
        rw [hleft]
        exact coupling.rightPositive outcome
      rightPositive := fun outcome => by
        rw [hright]
        exact coupling.leftPositive outcome }

/-- Every positive atom of the right marginal has a related positive witness
in the left marginal. -/
lemma exists_left_of_hasPositiveAtom_right
    {rightValue : β} (hright : right.HasPositiveAtom rightValue) :
    ∃ leftValue, left.HasPositiveAtom leftValue ∧
      R leftValue rightValue := by
  have hprojected := (coupling.rightPositive rightValue).mpr hright
  rw [hasPositiveAtom_map_iff] at hprojected
  obtain ⟨pair, hpair, hrightPair⟩ := hprojected
  have hleftProjected :
      (coupling.joint.map fun pair => pair.1.1).HasPositiveAtom
        pair.1.1 :=
    (hasPositiveAtom_map_iff _ _ _).mpr ⟨pair, hpair, rfl⟩
  exact
    ⟨pair.1.1, (coupling.leftPositive pair.1.1).mp hleftProjected,
      hrightPair ▸ pair.2⟩

/-- Every positive atom of the left marginal has a related positive witness
in the right marginal. -/
lemma exists_right_of_hasPositiveAtom_left
    {leftValue : α} (hleft : left.HasPositiveAtom leftValue) :
    ∃ rightValue, right.HasPositiveAtom rightValue ∧
      R leftValue rightValue :=
  coupling.symm.exists_left_of_hasPositiveAtom_right hleft

end RelCoupling

end Basic

/-! ## Transporting a coupling and its observables -/

namespace RelCoupling

section Mapping

variable {α : Type uα} {β : Type uβ} {γ δ : Type*}
variable {R : α → β → Prop} {S : γ → δ → Prop}
variable {left : FiniteLaw α} {right : FiniteLaw β}

/-- Push a relational coupling through related deterministic maps. -/
def map
    {f : α → γ} {g : β → δ}
    (coupling : RelCoupling R left right)
    (hmap : ∀ leftValue rightValue,
      R leftValue rightValue → S (f leftValue) (g rightValue)) :
    RelCoupling S (left.map f) (right.map g) := by
  let push : {pair : α × β // R pair.1 pair.2} →
      {pair : γ × δ // S pair.1 pair.2} :=
    fun pair =>
      ⟨(f pair.1.1, g pair.1.2),
        hmap pair.1.1 pair.1.2 pair.2⟩
  let joint := coupling.joint.map push
  have hleft :
      (joint.map fun pair => pair.1.1) =
        (coupling.joint.map fun pair => pair.1.1).map f := by
    simp only [joint]
    rw [map_comp, map_comp]
    rfl
  have hright :
      (joint.map fun pair => pair.1.2) =
        (coupling.joint.map fun pair => pair.1.2).map g := by
    simp only [joint]
    rw [map_comp, map_comp]
    rfl
  refine
    { joint := joint
      leftEquivalent :=
        (Equivalent.of_eq hleft).trans (coupling.leftEquivalent.map f)
      rightEquivalent :=
        (Equivalent.of_eq hright).trans (coupling.rightEquivalent.map g)
      leftPositive := ?_
      rightPositive := ?_ }
  · intro outcome
    rw [hleft, hasPositiveAtom_map_iff, hasPositiveAtom_map_iff]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source, (coupling.leftPositive source).mp hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source, (coupling.leftPositive source).mpr hsource, rfl⟩
  · intro outcome
    rw [hright, hasPositiveAtom_map_iff, hasPositiveAtom_map_iff]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source, (coupling.rightPositive source).mp hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source, (coupling.rightPositive source).mpr hsource, rfl⟩

/-- Related observables have equivalent exact finite laws. -/
theorem map_eq
    {f : α → γ} {g : β → γ}
    (coupling : RelCoupling R left right)
    (hmap : ∀ leftValue rightValue,
      R leftValue rightValue → f leftValue = g rightValue) :
    (left.map f).Equivalent (right.map g) := by
  intro value
  change
    (left.map f).expectRat value = (right.map g).expectRat value
  rw [expectRat_map, expectRat_map]
  calc
    left.expectRat (value ∘ f) =
        (coupling.joint.map fun pair => pair.1.1).expectRat
          (value ∘ f) :=
      ((equivalent_iff_expectRat.mp coupling.leftEquivalent)
        (value ∘ f)).symm
    _ = coupling.joint.expectRat
        ((value ∘ f) ∘ fun pair => pair.1.1) := by
      rw [expectRat_map]
    _ = coupling.joint.expectRat
        ((value ∘ g) ∘ fun pair => pair.1.2) := by
      congr 1
      funext pair
      simp only [Function.comp_apply]
      rw [hmap pair.1.1 pair.1.2 pair.2]
    _ = (coupling.joint.map fun pair => pair.1.2).expectRat
        (value ∘ g) := by
      rw [expectRat_map]
    _ = right.expectRat (value ∘ g) :=
      (equivalent_iff_expectRat.mp coupling.rightEquivalent) _

end Mapping

end RelCoupling

/-! ## Point laws and dependent composition -/

section Composition

variable {α : Type uα} {β : Type uβ}

/-- Couple two point laws whenever their outcomes are related. -/
def relCoupling_pure
    {R : α → β → Prop} {left : α} {right : β}
    (hrelated : R left right) :
    RelCoupling R (pure left) (pure right) := by
  let pair : {pair : α × β // R pair.1 pair.2} :=
    ⟨(left, right), hrelated⟩
  let joint := pure pair
  have hleft : (joint.map fun pair => pair.1.1) = pure left := by
    simp only [joint]
    rw [pure_map]
  have hright : (joint.map fun pair => pair.1.2) = pure right := by
    simp only [joint]
    rw [pure_map]
  exact
    { joint := joint
      leftEquivalent := Equivalent.of_eq hleft
      rightEquivalent := Equivalent.of_eq hright
      leftPositive := fun outcome => by rw [hleft]
      rightPositive := fun outcome => by rw [hright] }

namespace RelCoupling

section MarginalComposition

variable {A B C D : Type*}
variable (joint : FiniteLaw A) (marginal : FiniteLaw B)
variable (next : A → FiniteLaw C) (marginalNext : B → FiniteLaw D)
variable (project : A → B) (projectNext : C → D)

section Expectations

variable (houter : (joint.map project).Equivalent marginal)
variable (hinner : ∀ source,
  ((next source).map projectNext).Equivalent (marginalNext (project source)))

include houter hinner

-- Projection commutes with composition when both marginal laws agree.
private lemma bind_marginal_equivalent :
    ((joint.bind next).map projectNext).Equivalent (marginal.bind marginalNext) := by
  rw [map_bind]
  apply ((Equivalent.refl joint).bind hinner).trans
  simpa only [bind_map, Function.comp_def] using
    houter.bind (fun _ => Equivalent.refl _)

end Expectations

section PositiveAtoms

variable (houter : ∀ outcome,
  (joint.map project).HasPositiveAtom outcome ↔ marginal.HasPositiveAtom outcome)
variable (hinner : ∀ source outcome,
  ((next source).map projectNext).HasPositiveAtom outcome ↔
    (marginalNext (project source)).HasPositiveAtom outcome)

include houter hinner

-- The same projection argument transports positive-atom witnesses.
private lemma bind_marginal_positive (outcome : D) :
    ((joint.bind next).map projectNext).HasPositiveAtom outcome ↔
      (marginal.bind marginalNext).HasPositiveAtom outcome := by
  rw [map_bind, hasPositiveAtom_bind_iff, hasPositiveAtom_bind_iff]
  simp_rw [hinner]
  constructor
  · rintro ⟨source, hsource, hnext⟩
    exact ⟨project source,
      (houter _).mp ((hasPositiveAtom_map_iff _ _ _).mpr ⟨source, hsource, rfl⟩), hnext⟩
  · rintro ⟨projected, hprojected, hnext⟩
    obtain ⟨source, hsource, rfl⟩ :=
      (hasPositiveAtom_map_iff _ _ _).mp ((houter _).mpr hprojected)
    exact ⟨source, hsource, hnext⟩

end PositiveAtoms

end MarginalComposition

variable {γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
variable {left : FiniteLaw α} {right : FiniteLaw β}
variable {leftNext : α → FiniteLaw γ} {rightNext : β → FiniteLaw δ}

/-- Compose a coupling with constructively supplied related continuations. -/
def bind
    (coupling : RelCoupling R left right)
    (nextCoupling : ∀ leftValue rightValue,
      R leftValue rightValue →
        RelCoupling S (leftNext leftValue) (rightNext rightValue)) :
    RelCoupling S (left.bind leftNext) (right.bind rightNext) := by
  let nextForPair := fun pair : {pair : α × β // R pair.1 pair.2} =>
    nextCoupling pair.1.1 pair.1.2 pair.2
  let joint := coupling.joint.bind fun pair => (nextForPair pair).joint
  exact
    { joint := joint
      leftEquivalent := bind_marginal_equivalent coupling.joint left
        (fun pair => (nextForPair pair).joint) leftNext
        (fun pair => pair.1.1) (fun pair => pair.1.1)
        coupling.leftEquivalent (fun pair => (nextForPair pair).leftEquivalent)
      rightEquivalent := bind_marginal_equivalent coupling.joint right
        (fun pair => (nextForPair pair).joint) rightNext
        (fun pair => pair.1.2) (fun pair => pair.1.2)
        coupling.rightEquivalent (fun pair => (nextForPair pair).rightEquivalent)
      leftPositive := bind_marginal_positive coupling.joint left
        (fun pair => (nextForPair pair).joint) leftNext
        (fun pair => pair.1.1) (fun pair => pair.1.1)
        coupling.leftPositive (fun pair => (nextForPair pair).leftPositive)
      rightPositive := bind_marginal_positive coupling.joint right
        (fun pair => (nextForPair pair).joint) rightNext
        (fun pair => pair.1.2) (fun pair => pair.1.2)
        coupling.rightPositive (fun pair => (nextForPair pair).rightPositive) }

end RelCoupling

end Composition

end FiniteLaw
