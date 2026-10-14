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

/-- An explicit finite coupling supported on `R`.

The joint law ranges over the subtype of related pairs, so every sampled
joint outcome carries its relation witness constructively. -/
structure RelCoupling {α : Type uα} {β : Type uβ}
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

/-- Transpose a relational coupling. -/
def RelCoupling.symm {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {left : FiniteLaw α} {right : FiniteLaw β}
    (coupling : RelCoupling R left right) :
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
theorem RelCoupling.exists_left_of_hasPositiveAtom_right
    {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {left : FiniteLaw α} {right : FiniteLaw β}
    (coupling : RelCoupling R left right)
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
theorem RelCoupling.exists_right_of_hasPositiveAtom_left
    {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {left : FiniteLaw α} {right : FiniteLaw β}
    (coupling : RelCoupling R left right)
    {leftValue : α} (hleft : left.HasPositiveAtom leftValue) :
    ∃ rightValue, right.HasPositiveAtom rightValue ∧
      R leftValue rightValue :=
  coupling.symm.exists_left_of_hasPositiveAtom_right hleft

/-- Push a relational coupling through related deterministic maps. -/
def RelCoupling.map
    {α : Type uα} {β : Type uβ} {γ : Type*} {δ : Type*}
    {R : α → β → Prop} {S : γ → δ → Prop}
    {left : FiniteLaw α} {right : FiniteLaw β}
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
theorem RelCoupling.map_eq
    {α : Type uα} {β : Type uβ} {γ : Type*}
    {R : α → β → Prop}
    {left : FiniteLaw α} {right : FiniteLaw β}
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

/-- Couple two point laws whenever their outcomes are related. -/
def relCoupling_pure {α : Type uα} {β : Type uβ}
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

/-- Compose a coupling with constructively supplied related continuations. -/
def RelCoupling.bind
    {α : Type uα} {β : Type uβ} {γ : Type*} {δ : Type*}
    {R : α → β → Prop} {S : γ → δ → Prop}
    {left : FiniteLaw α} {right : FiniteLaw β}
    {leftNext : α → FiniteLaw γ} {rightNext : β → FiniteLaw δ}
    (coupling : RelCoupling R left right)
    (nextCoupling : ∀ leftValue rightValue,
      R leftValue rightValue →
        RelCoupling S (leftNext leftValue) (rightNext rightValue)) :
    RelCoupling S (left.bind leftNext) (right.bind rightNext) := by
  let nextForPair := fun pair : {pair : α × β // R pair.1 pair.2} =>
    nextCoupling pair.1.1 pair.1.2 pair.2
  let joint := coupling.joint.bind fun pair => (nextForPair pair).joint
  refine
    { joint := joint
      leftEquivalent := ?_
      rightEquivalent := ?_
      leftPositive := ?_
      rightPositive := ?_ }
  · intro value
    change
      (joint.map fun pair => pair.1.1).expectRat value =
        (left.bind leftNext).expectRat value
    rw [expectRat_map]
    simp only [joint]
    rw [expectRat_bind, expectRat_bind]
    calc
      coupling.joint.expectRat
          (fun pair =>
            ((nextForPair pair).joint).expectRat
              (value ∘ fun related => related.1.1)) =
          coupling.joint.expectRat
            (fun pair => (leftNext pair.1.1).expectRat value) := by
        congr 1
        funext pair
        have hinner :=
          (equivalent_iff_expectRat.mp
            (nextForPair pair).leftEquivalent) value
        rw [expectRat_map] at hinner
        exact hinner
      _ = (coupling.joint.map fun pair => pair.1.1).expectRat
          (fun outcome => (leftNext outcome).expectRat value) := by
        rw [expectRat_map]
        rfl
      _ = left.expectRat
          (fun outcome => (leftNext outcome).expectRat value) :=
        (equivalent_iff_expectRat.mp coupling.leftEquivalent) _
  · intro value
    change
      (joint.map fun pair => pair.1.2).expectRat value =
        (right.bind rightNext).expectRat value
    rw [expectRat_map]
    simp only [joint]
    rw [expectRat_bind, expectRat_bind]
    calc
      coupling.joint.expectRat
          (fun pair =>
            ((nextForPair pair).joint).expectRat
              (value ∘ fun related => related.1.2)) =
          coupling.joint.expectRat
            (fun pair => (rightNext pair.1.2).expectRat value) := by
        congr 1
        funext pair
        have hinner :=
          (equivalent_iff_expectRat.mp
            (nextForPair pair).rightEquivalent) value
        rw [expectRat_map] at hinner
        exact hinner
      _ = (coupling.joint.map fun pair => pair.1.2).expectRat
          (fun outcome => (rightNext outcome).expectRat value) := by
        rw [expectRat_map]
        rfl
      _ = right.expectRat
          (fun outcome => (rightNext outcome).expectRat value) :=
        (equivalent_iff_expectRat.mp coupling.rightEquivalent) _
  · intro outcome
    simp only [joint]
    rw [hasPositiveAtom_bind_iff]
    rw [hasPositiveAtom_map_iff]
    simp_rw [hasPositiveAtom_bind_iff]
    constructor
    · rintro ⟨relatedOutcome, ⟨pair, hpair, hnext⟩, houtcome⟩
      have hsourceProjected :
          (coupling.joint.map fun pair => pair.1.1).HasPositiveAtom
            pair.1.1 :=
        (hasPositiveAtom_map_iff _ _ _).mpr ⟨pair, hpair, rfl⟩
      have hnextProjected :
          ((nextForPair pair).joint.map fun related =>
            related.1.1).HasPositiveAtom relatedOutcome.1.1 :=
        (hasPositiveAtom_map_iff _ _ _).mpr
          ⟨relatedOutcome, hnext, rfl⟩
      refine
        ⟨pair.1.1,
          (coupling.leftPositive pair.1.1).mp hsourceProjected, ?_⟩
      have hpositive :=
        ((nextForPair pair).leftPositive relatedOutcome.1.1).mp
          hnextProjected
      simpa [houtcome] using hpositive
    · rintro ⟨source, hsource, hnext⟩
      have hsourceProjected :=
        (coupling.leftPositive source).mpr hsource
      rw [hasPositiveAtom_map_iff] at hsourceProjected
      obtain ⟨pair, hpair, hpairSource⟩ := hsourceProjected
      subst source
      have hnextProjected :=
        ((nextForPair pair).leftPositive outcome).mpr hnext
      rw [hasPositiveAtom_map_iff] at hnextProjected
      obtain ⟨relatedOutcome, hrelatedOutcome, houtcome⟩ :=
        hnextProjected
      exact ⟨relatedOutcome, ⟨pair, hpair, hrelatedOutcome⟩, houtcome⟩
  · intro outcome
    simp only [joint]
    rw [hasPositiveAtom_bind_iff]
    rw [hasPositiveAtom_map_iff]
    simp_rw [hasPositiveAtom_bind_iff]
    constructor
    · rintro ⟨relatedOutcome, ⟨pair, hpair, hnext⟩, houtcome⟩
      have htargetProjected :
          (coupling.joint.map fun pair => pair.1.2).HasPositiveAtom
            pair.1.2 :=
        (hasPositiveAtom_map_iff _ _ _).mpr ⟨pair, hpair, rfl⟩
      have hnextProjected :
          ((nextForPair pair).joint.map fun related =>
            related.1.2).HasPositiveAtom relatedOutcome.1.2 :=
        (hasPositiveAtom_map_iff _ _ _).mpr
          ⟨relatedOutcome, hnext, rfl⟩
      refine
        ⟨pair.1.2,
          (coupling.rightPositive pair.1.2).mp htargetProjected, ?_⟩
      have hpositive :=
        ((nextForPair pair).rightPositive relatedOutcome.1.2).mp
          hnextProjected
      simpa [houtcome] using hpositive
    · rintro ⟨target, htarget, hnext⟩
      have htargetProjected :=
        (coupling.rightPositive target).mpr htarget
      rw [hasPositiveAtom_map_iff] at htargetProjected
      obtain ⟨pair, hpair, hpairTarget⟩ := htargetProjected
      subst target
      have hnextProjected :=
        ((nextForPair pair).rightPositive outcome).mpr hnext
      rw [hasPositiveAtom_map_iff] at hnextProjected
      obtain ⟨relatedOutcome, hrelatedOutcome, houtcome⟩ :=
        hnextProjected
      exact ⟨relatedOutcome, ⟨pair, hpair, hrelatedOutcome⟩, houtcome⟩

end FiniteLaw
