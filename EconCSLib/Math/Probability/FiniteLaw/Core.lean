/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Lemmas

/-!
# Finite exact probability laws

`FiniteLaw α` is the executable probability representation used by finite
EconCSLib models.  A law is a finite list of outcomes with nonnegative rational
weights whose total is one.  Repeated outcomes are intentional: construction,
mapping, and binding never need an ambient `Fintype α` or `DecidableEq α`.

The list is a sparse presentation, not the semantic equality of laws. When
outcomes are decidably equal, `mass` adds every occurrence of an outcome.
`Equivalent` instead compares all exact rational expectations, so semantic
comparison does not require equality on the outcome carrier.

## Main definitions

* `FiniteLaw.pure`, `FiniteLaw.map`, and `FiniteLaw.bind`;
* `FiniteLaw.HasPositiveAtom` for presentation-independent reachability
  arguments that do not require equality on the outcome type;
* `FiniteLaw.eventMass` and `FiniteLaw.mass`;
* `FiniteLaw.normalize?` for validated normalization of a nonzero weighted
  list;
* `FiniteLaw.expectRat` for exact rational expected values.

No declaration in this module uses classical choice or infinite sums.
-/

open BigOperators

universe uα uβ uγ

/-- A finite, exact probability law represented by rationally weighted atoms.

Repeated outcomes are allowed.  This keeps `map` and `bind` executable without
requiring equality or a finite enumeration of the ambient outcome type. -/
structure FiniteLaw (α : Type uα) where
  /-- Sparse weighted occurrences. -/
  atoms : List (α × ℚ≥0)
  /-- The occurrence weights sum to one. -/
  normalized : (atoms.map Prod.snd).sum = 1

namespace FiniteLaw

/-- Two finite laws are equal when their weighted atom lists are equal.

The normalization field is proof-valued, so no separate proof equality is
required. -/
@[ext]
theorem ext {left right : FiniteLaw α}
    (hatoms : left.atoms = right.atoms) : left = right := by
  cases left
  cases right
  cases hatoms
  rfl

/-- The total weight of a finite atom list. -/
def totalWeight (atoms : List (α × ℚ≥0)) : ℚ≥0 :=
  (atoms.map Prod.snd).sum

@[simp]
theorem totalWeight_atoms (law : FiniteLaw α) :
    totalWeight law.atoms = 1 :=
  law.normalized

/-- The point law concentrated at one outcome. -/
def pure (outcome : α) : FiniteLaw α where
  atoms := [(outcome, 1)]
  normalized := by simp

@[simp]
theorem pure_atoms (outcome : α) :
    (pure outcome).atoms = [(outcome, 1)] :=
  rfl

/-- An outcome occurs with positive weight in a finite-law presentation.

This predicate deliberately quantifies over occurrences rather than requiring
a duplicate-free support. It is usable without `DecidableEq α` and is stable
under the executable `map` and `bind` operations below. -/
def HasPositiveAtom (law : FiniteLaw α) (outcome : α) : Prop :=
  ∃ weight, (outcome, weight) ∈ law.atoms ∧ weight ≠ 0

@[simp]
theorem hasPositiveAtom_pure_iff (outcome target : α) :
    (pure outcome).HasPositiveAtom target ↔ target = outcome := by
  constructor
  · rintro ⟨weight, hmem, hweight⟩
    simp only [pure_atoms, List.mem_singleton] at hmem
    exact congrArg Prod.fst hmem
  · rintro rfl
    exact ⟨1, by simp, one_ne_zero⟩

private theorem exists_atom_ne_zero_of_totalWeight_eq_one
    (atoms : List (α × ℚ≥0)) (hnormalized : totalWeight atoms = 1) :
    ∃ atom ∈ atoms, atom.2 ≠ 0 := by
  induction atoms with
  | nil => simp [totalWeight] at hnormalized
  | cons atom atoms ih =>
      by_cases hweight : atom.2 = 0
      · have htail : totalWeight atoms = 1 := by
          simpa [totalWeight, hweight] using hnormalized
        obtain ⟨target, htarget, hpositive⟩ := ih htail
        exact ⟨target, by simp [htarget], hpositive⟩
      · exact ⟨atom, by simp, hweight⟩

/-- Every normalized finite law has at least one positive atom. -/
theorem exists_hasPositiveAtom (law : FiniteLaw α) :
    ∃ outcome, law.HasPositiveAtom outcome := by
  obtain ⟨atom, hatom, hweight⟩ :=
    exists_atom_ne_zero_of_totalWeight_eq_one law.atoms
      law.normalized
  exact ⟨atom.1, atom.2, hatom, hweight⟩

/-- Push a finite law forward along a function. -/
def map (f : α → β) (law : FiniteLaw α) : FiniteLaw β where
  atoms := law.atoms.map fun atom => (f atom.1, atom.2)
  normalized := by
    simpa [List.map_map, Function.comp_def] using law.normalized

@[simp]
theorem map_atoms (f : α → β) (law : FiniteLaw α) :
    (map f law).atoms =
      law.atoms.map fun atom => (f atom.1, atom.2) :=
  rfl

theorem hasPositiveAtom_map_iff (f : α → β) (law : FiniteLaw α)
    (target : β) :
    (law.map f).HasPositiveAtom target ↔
      ∃ source, law.HasPositiveAtom source ∧ f source = target := by
  constructor
  · rintro ⟨weight, hmem, hweight⟩
    rw [map_atoms, List.mem_map] at hmem
    obtain ⟨atom, hatom, heq⟩ := hmem
    refine ⟨atom.1, ⟨atom.2, hatom, ?_⟩, ?_⟩
    · intro hzero
      exact hweight ((congrArg Prod.snd heq).symm.trans hzero)
    · simpa only using congrArg Prod.fst heq
  · rintro ⟨source, ⟨weight, hmem, hweight⟩, rfl⟩
    refine ⟨weight, ?_, hweight⟩
    rw [map_atoms, List.mem_map]
    exact ⟨(source, weight), hmem, rfl⟩

/-- Scaling every atom scales the total weight by the same factor. -/
private theorem totalWeight_map_mul
    (weight : ℚ≥0) (atoms : List (β × ℚ≥0)) :
    totalWeight
        (atoms.map fun atom => (atom.1, weight * atom.2)) =
      weight * totalWeight atoms := by
  simp only [totalWeight, List.map_map]
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp [ih, mul_add]

/-- Total weight distributes over list append. -/
private theorem totalWeight_append
    (left right : List (α × ℚ≥0)) :
    totalWeight (left ++ right) =
      totalWeight left + totalWeight right := by
  simp [totalWeight, List.map_append]

/-- Binding over a list of outer atoms preserves its total weight when every
continuation law is normalized. -/
private theorem totalWeight_flatMap
    (atoms : List (α × ℚ≥0)) (next : α → FiniteLaw β) :
    totalWeight
        (atoms.flatMap fun atom =>
          (next atom.1).atoms.map fun target =>
            (target.1, atom.2 * target.2)) =
      totalWeight atoms := by
  induction atoms with
  | nil => simp [totalWeight]
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.flatMap_cons]
      rw [totalWeight_append, totalWeight_map_mul, ih,
        totalWeight_atoms, mul_one]
      rfl

/-- Sequential composition of finite laws.

Every continuation atom is multiplied by the weight of the outer atom that
reached it. The implementation is finite `List.flatMap`. -/
def bind (law : FiniteLaw α) (next : α → FiniteLaw β) :
    FiniteLaw β where
  atoms :=
    law.atoms.flatMap fun atom =>
      (next atom.1).atoms.map fun target =>
        (target.1, atom.2 * target.2)
  normalized :=
    by
      change
        totalWeight
            (law.atoms.flatMap fun atom =>
              (next atom.1).atoms.map fun target =>
                (target.1, atom.2 * target.2)) = 1
      exact (totalWeight_flatMap law.atoms next).trans law.normalized

@[simp]
theorem bind_atoms (law : FiniteLaw α) (next : α → FiniteLaw β) :
    (bind law next).atoms =
      law.atoms.flatMap fun atom =>
        (next atom.1).atoms.map fun target =>
          (target.1, atom.2 * target.2) :=
  rfl

@[simp]
theorem pure_bind (outcome : α) (next : α → FiniteLaw β) :
    (pure outcome).bind next = next outcome := by
  apply FiniteLaw.ext
  simp [bind_atoms]

@[simp]
theorem bind_pure (law : FiniteLaw α) :
    law.bind pure = law := by
  apply FiniteLaw.ext
  simp [bind_atoms]

theorem bind_bind (law : FiniteLaw α) (next : α → FiniteLaw β)
    (final : β → FiniteLaw γ) :
    (law.bind next).bind final =
      law.bind fun outcome => (next outcome).bind final := by
  apply FiniteLaw.ext
  simp only [bind_atoms]
  induction law.atoms with
  | nil => rfl
  | cons outer outers ih =>
      rcases outer with ⟨outcome, outerWeight⟩
      simp only [List.flatMap_cons]
      rw [List.flatMap_append, ih]
      congr 1
      induction (next outcome).atoms with
      | nil => rfl
      | cons inner inners ihInner =>
          rcases inner with ⟨target, innerWeight⟩
          simp only [List.map_cons, List.flatMap_cons, List.map_append]
          rw [ihInner]
          simp [mul_assoc]

theorem map_eq_bind_pure_comp (f : α → β) (law : FiniteLaw α) :
    law.map f = law.bind (pure ∘ f) := by
  apply FiniteLaw.ext
  simp only [map_atoms, bind_atoms]
  induction law.atoms with
  | nil => rfl
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp [ih]

theorem pure_map (f : α → β) (outcome : α) :
    (pure outcome).map f = pure (f outcome) := by
  apply FiniteLaw.ext
  simp [map_atoms]

theorem map_bind (law : FiniteLaw α) (next : α → FiniteLaw β)
    (f : β → γ) :
    (law.bind next).map f =
      law.bind fun outcome => (next outcome).map f := by
  rw [map_eq_bind_pure_comp, bind_bind]
  congr
  funext outcome
  rw [← map_eq_bind_pure_comp]

theorem bind_map (law : FiniteLaw α) (f : α → β)
    (next : β → FiniteLaw γ) :
    (law.map f).bind next =
      law.bind (next ∘ f) := by
  rw [map_eq_bind_pure_comp, bind_bind]
  congr
  funext outcome
  simp

theorem map_comp (f : α → β) (law : FiniteLaw α) (g : β → γ) :
    (law.map f).map g = law.map (g ∘ f) := by
  apply FiniteLaw.ext
  simp [map_atoms, List.map_map, Function.comp_def]

theorem map_id (law : FiniteLaw α) : law.map id = law := by
  apply FiniteLaw.ext
  simp [map_atoms]

/-- Pushforward along a type equivalence is an equivalence of finite-law
presentations. -/
def mapEquiv (equivalence : α ≃ β) : FiniteLaw α ≃ FiniteLaw β where
  toFun := map equivalence
  invFun := map equivalence.symm
  left_inv law := by
    rw [map_comp]
    have hcomp : (equivalence.symm : β → α) ∘ equivalence = id := by
      funext outcome
      exact equivalence.symm_apply_apply outcome
    rw [hcomp, map_id]
  right_inv law := by
    rw [map_comp]
    have hcomp : (equivalence : α → β) ∘ equivalence.symm = id := by
      funext outcome
      exact equivalence.apply_symm_apply outcome
    rw [hcomp, map_id]

theorem hasPositiveAtom_bind_iff (law : FiniteLaw α)
    (next : α → FiniteLaw β) (target : β) :
    (law.bind next).HasPositiveAtom target ↔
      ∃ source, law.HasPositiveAtom source ∧
        (next source).HasPositiveAtom target := by
  constructor
  · rintro ⟨weight, hmem, hweight⟩
    rw [bind_atoms, List.mem_flatMap] at hmem
    obtain ⟨outer, houter, hmem⟩ := hmem
    rw [List.mem_map] at hmem
    obtain ⟨inner, hinner, heq⟩ := hmem
    rcases outer with ⟨source, outerWeight⟩
    rcases inner with ⟨innerTarget, innerWeight⟩
    have htarget : innerTarget = target := by
      simpa only using congrArg Prod.fst heq
    subst innerTarget
    have hproduct : outerWeight * innerWeight = weight := by
      simpa only using congrArg Prod.snd heq
    have houterWeight : outerWeight ≠ 0 := by
      intro hzero
      apply hweight
      rw [← hproduct, hzero, zero_mul]
    have hinnerWeight : innerWeight ≠ 0 := by
      intro hzero
      apply hweight
      rw [← hproduct, hzero, mul_zero]
    exact
      ⟨source, ⟨outerWeight, houter, houterWeight⟩,
        innerWeight, hinner, hinnerWeight⟩
  · rintro
      ⟨source, ⟨outerWeight, houter, houterWeight⟩,
        innerWeight, hinner, hinnerWeight⟩
    refine ⟨outerWeight * innerWeight, ?_, mul_ne_zero houterWeight hinnerWeight⟩
    rw [bind_atoms, List.mem_flatMap]
    refine ⟨(source, outerWeight), houter, ?_⟩
    rw [List.mem_map]
    exact ⟨(target, innerWeight), hinner, rfl⟩

/-- Total mass of an executable Boolean event. -/
def eventMass (law : FiniteLaw α) (event : α → Bool) : ℚ≥0 :=
  (law.atoms.map fun atom =>
    if event atom.1 then atom.2 else 0).sum

theorem eventMass_map (law : FiniteLaw α) (f : α → β)
    (event : β → Bool) :
    (law.map f).eventMass event =
      law.eventMass (event ∘ f) := by
  unfold eventMass
  rw [map_atoms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _
  rfl

/-- Total mass assigned to one outcome.  Equality is requested only for this
observation; it is not needed to construct the law. -/
def mass [DecidableEq α] (law : FiniteLaw α) (outcome : α) : ℚ≥0 :=
  eventMass law fun candidate => decide (candidate = outcome)

@[simp]
theorem mass_pure [DecidableEq α] (outcome target : α) :
    (pure outcome).mass target = if outcome = target then 1 else 0 := by
  simp [mass, eventMass, pure]

/-- Mapping along an equivalence transports point masses through its unique
preimage. -/
theorem mass_map_equiv [DecidableEq α] [DecidableEq β]
  (law : FiniteLaw α) (equivalence : α ≃ β) (target : β) :
    (law.map equivalence).mass target =
      law.mass (equivalence.symm target) := by
  unfold mass eventMass
  rw [map_atoms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _
  simp [equivalence.eq_symm_apply]

/-- Point mass of a finite bind is the finite weighted sum of continuation
point masses. -/
theorem mass_bind [DecidableEq β]
    (law : FiniteLaw α) (next : α → FiniteLaw β) (target : β) :
    (law.bind next).mass target =
      (law.atoms.map fun atom =>
        atom.2 * (next atom.1).mass target).sum := by
  unfold mass eventMass
  rw [bind_atoms]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [ih]
      congr 1
      simp only [List.map_map, Function.comp_def]
      induction (next outcome).atoms with
      | nil => simp
      | cons inner inners ihInner =>
          rcases inner with ⟨innerOutcome, innerWeight⟩
          simp only [List.map_cons, List.sum_cons]
          rw [ihInner]
          by_cases heq : innerOutcome = target
          · simp [heq, mul_add]
          · simp [heq]

/-- An outcome absent from all positive atoms has zero total mass. -/
theorem mass_eq_zero_of_not_hasPositiveAtom [DecidableEq α]
    (law : FiniteLaw α) (outcome : α)
    (habsent : ¬ law.HasPositiveAtom outcome) :
    law.mass outcome = 0 := by
  unfold mass eventMass
  apply List.sum_eq_zero
  intro weight hweight
  rw [List.mem_map] at hweight
  obtain ⟨atom, hatom, rfl⟩ := hweight
  rcases atom with ⟨candidate, atomWeight⟩
  by_cases heq : candidate = outcome
  · subst candidate
    simp only [decide_true, ↓reduceIte]
    by_contra hnonzero
    exact habsent ⟨atomWeight, hatom, hnonzero⟩
  · simp [heq]

/-- Point mass is independent of the particular equality decision procedure
used to compute it. -/
theorem mass_decidableEq_irrel
    (first second : DecidableEq α)
    (law : FiniteLaw α) (outcome : α) :
    @mass α first law outcome = @mass α second law outcome := by
  unfold mass eventMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _
  by_cases heq : atom.1 = outcome
  · simp [heq]
  · simp [heq]

private def atomsMass [DecidableEq α]
    (atoms : List (α × ℚ≥0)) (outcome : α) : ℚ≥0 :=
  (atoms.map fun atom =>
    if decide (atom.1 = outcome) then atom.2 else 0).sum

/-- Two sparse presentations describe the same finite law when every exact
rational observable has the same expectation.

Quantifying over observables avoids a global `DecidableEq` requirement while
still identifying presentations that differ only by repeated or reordered
atoms. -/
def Equivalent (left right : FiniteLaw α) : Prop :=
  ∀ value : α → ℚ,
    (left.atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum =
      (right.atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum

/-- Exact rational expectation of a rational-valued observable. -/
def expectRat (law : FiniteLaw α) (value : α → ℚ) : ℚ :=
  (law.atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum

private theorem atomsExpectation_eq_finsetSum [DecidableEq α]
    (atoms : List (α × ℚ≥0)) (support : Finset α)
    (hmem : ∀ atom ∈ atoms, atom.1 ∈ support)
    (value : α → ℚ) :
    (atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum =
      ∑ outcome ∈ support,
        (atomsMass atoms outcome : ℚ) * value outcome := by
  induction atoms with
  | nil => simp [atomsMass]
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      have houtcome : outcome ∈ support :=
        hmem (outcome, weight) (by simp)
      have htail : ∀ atom ∈ atoms, atom.1 ∈ support := by
        intro atom hatom
        exact hmem atom (List.mem_cons_of_mem _ hatom)
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail]
      simp only [atomsMass, List.map_cons, List.sum_cons,
        NNRat.cast_add, add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single outcome]
      · simp
      · intro other _ hne
        simp [hne.symm]
      · intro hnot
        exact (hnot houtcome).elim

theorem equivalent_iff_expectRat {left right : FiniteLaw α} :
    left.Equivalent right ↔
      ∀ value, left.expectRat value = right.expectRat value :=
  Iff.rfl

@[simp]
theorem expectRat_pure (outcome : α) (value : α → ℚ) :
    (pure outcome).expectRat value = value outcome := by
  simp [expectRat]

theorem expectRat_map (f : α → β) (law : FiniteLaw α)
    (value : β → ℚ) :
    (law.map f).expectRat value = law.expectRat (value ∘ f) := by
  simp [expectRat, map_atoms, List.map_map, Function.comp_def]

private theorem expectRat_indicator (law : FiniteLaw α)
    (event : α → Bool) :
    law.expectRat (fun outcome => if event outcome then 1 else 0) =
      (law.eventMass event : ℚ) := by
  unfold expectRat
  let weights : List ℚ≥0 :=
    law.atoms.map fun atom =>
      if event atom.1 then atom.2 else 0
  change
    (law.atoms.map fun atom =>
      (atom.2 : ℚ) * if event atom.1 then 1 else 0).sum =
        (weights.sum : ℚ)
  calc
    (law.atoms.map fun atom =>
        (atom.2 : ℚ) * if event atom.1 then 1 else 0).sum =
        (List.map (NNRat.cast : ℚ≥0 → ℚ) weights).sum := by
      unfold weights
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro atom _
      by_cases hevent : event atom.1
      · simp [hevent]
      · simp [hevent]
    _ = (weights.sum : ℚ) := by
      simpa using
        (map_list_sum (NNRat.castHom ℚ) weights).symm

@[simp]
theorem expectRat_const (law : FiniteLaw α) (constant : ℚ) :
    law.expectRat (fun _ => constant) = constant := by
  unfold expectRat
  have hcast :
      (law.atoms.map fun atom => (atom.2 : ℚ)).sum = 1 := by
    calc
      (law.atoms.map fun atom => (atom.2 : ℚ)).sum =
          ((law.atoms.map Prod.snd).sum : ℚ) := by
        simpa using
          (map_list_sum (NNRat.castHom ℚ)
            (law.atoms.map Prod.snd)).symm
      _ = 1 := by rw [law.normalized]; norm_num
  calc
    (law.atoms.map fun atom => (atom.2 : ℚ) * constant).sum =
        (law.atoms.map fun atom => (atom.2 : ℚ)).sum * constant := by
      induction law.atoms with
      | nil => simp
      | cons atom atoms ih => simp [ih, add_mul]
    _ = constant := by rw [hcast, one_mul]

private theorem expectRat_scaledAtoms
    (weight : ℚ≥0) (atoms : List (β × ℚ≥0))
    (value : β → ℚ) :
    (atoms.map fun atom =>
        ((weight * atom.2 : ℚ≥0) : ℚ) * value atom.1).sum =
      (weight : ℚ) *
        (atoms.map fun atom => (atom.2 : ℚ) * value atom.1).sum := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, NNRat.cast_mul]
      have ih' :
          (atoms.map fun atom =>
            (weight : ℚ) * (atom.2 : ℚ) * value atom.1).sum =
            (weight : ℚ) *
              (atoms.map fun atom =>
                (atom.2 : ℚ) * value atom.1).sum := by
        simpa only [NNRat.cast_mul] using ih
      rw [ih', mul_add]
      ring

private theorem expectRat_bind_atoms
    (atoms : List (α × ℚ≥0)) (next : α → FiniteLaw β)
    (value : β → ℚ) :
    (List.map (fun atom : β × ℚ≥0 => (atom.2 : ℚ) * value atom.1)
        (atoms.flatMap fun atom =>
          (next atom.1).atoms.map fun target =>
            (target.1, atom.2 * target.2))).sum =
      (atoms.map fun atom =>
        (atom.2 : ℚ) * (next atom.1).expectRat value).sum := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      have hscaled :
          (List.map (fun atom : β × ℚ≥0 =>
                (atom.2 : ℚ) * value atom.1)
              (List.map (fun target =>
                (target.1, weight * target.2))
                (next outcome).atoms)).sum =
            (weight : ℚ) * (next outcome).expectRat value := by
        simpa only [List.map_map, Function.comp_def, expectRat] using
          expectRat_scaledAtoms weight (next outcome).atoms value
      rw [hscaled, ih]

theorem expectRat_bind (law : FiniteLaw α)
    (next : α → FiniteLaw β) (value : β → ℚ) :
    (law.bind next).expectRat value =
      law.expectRat fun outcome => (next outcome).expectRat value := by
  unfold expectRat
  rw [bind_atoms]
  exact expectRat_bind_atoms law.atoms next value

/-- Exact expectations depend only on an observable's values at positive
atoms. -/
theorem expectRat_congr_positive (law : FiniteLaw α)
    {left right : α → ℚ}
    (hcongr : ∀ outcome, law.HasPositiveAtom outcome →
      left outcome = right outcome) :
    law.expectRat left = law.expectRat right := by
  unfold expectRat
  congr 1
  apply List.map_congr_left
  intro atom hatom
  rcases atom with ⟨outcome, weight⟩
  by_cases hweight : weight = 0
  · simp [hweight]
  · rw [hcongr outcome ⟨weight, hatom, hweight⟩]

/-- Binding pointwise equivalent continuations need only be checked at the
positive atoms of the outer law. -/
theorem bind_congr_positive (law : FiniteLaw α)
    {left right : α → FiniteLaw β}
    (hcongr : ∀ outcome, law.HasPositiveAtom outcome →
      (left outcome).Equivalent (right outcome)) :
    (law.bind left).Equivalent (law.bind right) := by
  intro value
  change
    (law.bind left).expectRat value =
      (law.bind right).expectRat value
  rw [expectRat_bind, expectRat_bind]
  apply expectRat_congr_positive law
  intro outcome houtcome
  exact hcongr outcome houtcome value

theorem Equivalent.refl (law : FiniteLaw α) : law.Equivalent law :=
  fun _ => rfl

theorem Equivalent.symm {left right : FiniteLaw α}
    (h : left.Equivalent right) : right.Equivalent left :=
  fun value => (h value).symm

theorem Equivalent.trans {first second third : FiniteLaw α}
    (hfirst : first.Equivalent second)
    (hsecond : second.Equivalent third) : first.Equivalent third :=
  fun value => (hfirst value).trans (hsecond value)

theorem Equivalent.of_eq {left right : FiniteLaw α}
    (h : left = right) : left.Equivalent right := by
  subst right
  exact Equivalent.refl left

/-- Pointwise equality of total outcome masses implies semantic equality,
even when the sparse atom lists use different orders or duplicate outcomes. -/
theorem Equivalent.of_mass_eq [DecidableEq α]
    {left right : FiniteLaw α}
    (hmass : ∀ outcome, left.mass outcome = right.mass outcome) :
    left.Equivalent right := by
  intro value
  let support : Finset α :=
    (left.atoms.map Prod.fst ++ right.atoms.map Prod.fst).toFinset
  have hleft : ∀ atom ∈ left.atoms, atom.1 ∈ support := by
    intro atom hatom
    simp only [support, List.mem_toFinset, List.mem_append,
      List.mem_map]
    exact Or.inl ⟨atom, hatom, rfl⟩
  have hright : ∀ atom ∈ right.atoms, atom.1 ∈ support := by
    intro atom hatom
    simp only [support, List.mem_toFinset, List.mem_append,
      List.mem_map]
    exact Or.inr ⟨atom, hatom, rfl⟩
  change left.expectRat value = right.expectRat value
  unfold expectRat
  rw [atomsExpectation_eq_finsetSum left.atoms support hleft value,
    atomsExpectation_eq_finsetSum right.atoms support hright value]
  apply Finset.sum_congr rfl
  intro outcome _
  have hraw :
      atomsMass left.atoms outcome = atomsMass right.atoms outcome := by
    simpa [mass, eventMass, atomsMass] using hmass outcome
  rw [hraw]

theorem Equivalent.map {left right : FiniteLaw α}
    (h : left.Equivalent right) (f : α → β) :
    (left.map f).Equivalent (right.map f) := by
  intro value
  change (left.map f).expectRat value = (right.map f).expectRat value
  rw [expectRat_map, expectRat_map]
  exact h (value ∘ f)

/-- Semantically equivalent finite laws assign the same exact mass to every
executable Boolean event. -/
theorem Equivalent.eventMass {left right : FiniteLaw α}
    (h : left.Equivalent right) (event : α → Bool) :
    left.eventMass event = right.eventMass event := by
  apply NNRat.cast_injective (α := ℚ)
  rw [← expectRat_indicator, ← expectRat_indicator]
  exact (equivalent_iff_expectRat.mp h) _

theorem Equivalent.bind {left right : FiniteLaw α}
    (h : left.Equivalent right)
    {leftNext rightNext : α → FiniteLaw β}
    (hnext : ∀ outcome, (leftNext outcome).Equivalent (rightNext outcome)) :
    (left.bind leftNext).Equivalent (right.bind rightNext) := by
  intro value
  change
    (left.bind leftNext).expectRat value =
      (right.bind rightNext).expectRat value
  rw [expectRat_bind, expectRat_bind]
  calc
    left.expectRat (fun outcome => (leftNext outcome).expectRat value) =
        right.expectRat (fun outcome => (leftNext outcome).expectRat value) :=
      (equivalent_iff_expectRat.mp h) _
    _ = right.expectRat (fun outcome => (rightNext outcome).expectRat value) := by
      congr 1
      funext outcome
      exact (equivalent_iff_expectRat.mp (hnext outcome)) value

private theorem scalar_mul_list_sum {δ : Type*}
    (scalar : ℚ) (atoms : List δ) (f : δ → ℚ) :
    scalar * (atoms.map f).sum =
      (atoms.map fun atom => scalar * f atom).sum := by
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp [ih, mul_add]

private theorem list_double_sum_comm {δ ε : Type*}
    (first : List δ) (second : List ε) (f : δ → ε → ℚ) :
    (first.map fun a => (second.map fun b => f a b).sum).sum =
      (second.map fun b => (first.map fun a => f a b).sum).sum := by
  induction first with
  | nil => simp
  | cons a first ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, ← List.sum_map_add]

/-- Independent finite draws may be interchanged without changing any exact
rational observable.  The presentations can differ in atom order, so this is
semantic equivalence rather than structural equality. -/
theorem bind_comm_equivalent
    (left : FiniteLaw α) (right : FiniteLaw β)
    (next : α → β → FiniteLaw γ) :
    (left.bind fun a => right.bind fun b => next a b).Equivalent
      (right.bind fun b => left.bind fun a => next a b) := by
  intro value
  change
    (left.bind fun a => right.bind fun b => next a b).expectRat value =
      (right.bind fun b => left.bind fun a => next a b).expectRat value
  rw [expectRat_bind, expectRat_bind]
  simp only [expectRat_bind]
  unfold expectRat
  have weighted_double_sum_comm
      (first : List (α × ℚ≥0)) (second : List (β × ℚ≥0))
      (f : α → β → ℚ) :
      (first.map fun a => (a.2 : ℚ) *
          (second.map fun b => (b.2 : ℚ) * f a.1 b.1).sum).sum =
        (second.map fun b => (b.2 : ℚ) *
          (first.map fun a => (a.2 : ℚ) * f a.1 b.1).sum).sum := by
    calc
      _ = (first.map fun a =>
          (second.map fun b =>
            (a.2 : ℚ) * ((b.2 : ℚ) * f a.1 b.1)).sum).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro atom _
        exact scalar_mul_list_sum (atom.2 : ℚ) second _
      _ = (second.map fun b =>
          (first.map fun a =>
            (a.2 : ℚ) * ((b.2 : ℚ) * f a.1 b.1)).sum).sum :=
        list_double_sum_comm first second _
      _ = _ := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro atom _
        calc
          (first.map fun a =>
              (a.2 : ℚ) * ((atom.2 : ℚ) * f a.1 atom.1)).sum =
              (first.map fun a =>
                (atom.2 : ℚ) * ((a.2 : ℚ) * f a.1 atom.1)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro other _
            ring
          _ = (atom.2 : ℚ) *
              (first.map fun a => (a.2 : ℚ) * f a.1 atom.1).sum :=
            (scalar_mul_list_sum (atom.2 : ℚ) first _).symm
  exact weighted_double_sum_comm left.atoms right.atoms
    (fun a b =>
      (List.map
        (fun atom => (atom.2 : ℚ) * value atom.1)
        (next a b).atoms).sum)

/-- Dividing all weights by a fixed scalar divides the total weight by that
scalar. -/
private theorem totalWeight_map_div
    (atoms : List (α × ℚ≥0)) (divisor : ℚ≥0) :
    totalWeight
        (atoms.map fun atom =>
          (atom.1, atom.2 / divisor)) =
      totalWeight atoms / divisor := by
  simp only [totalWeight, List.map_map]
  induction atoms with
  | nil => simp
  | cons atom atoms ih =>
      simp [ih, add_div]

/-- Dividing all weights by their nonzero total produces a normalized law. -/
private theorem totalWeight_div
    (atoms : List (α × ℚ≥0)) (hnonzero : totalWeight atoms ≠ 0) :
    totalWeight
        (atoms.map fun atom =>
          (atom.1, atom.2 / totalWeight atoms)) = 1 := by
  rw [totalWeight_map_div, div_self hnonzero]

/-- Normalize an explicitly nonzero finite weighted list. -/
def normalize (atoms : List (α × ℚ≥0))
    (hnonzero : totalWeight atoms ≠ 0) : FiniteLaw α where
  atoms := atoms.map fun atom =>
    (atom.1, atom.2 / totalWeight atoms)
  normalized := by
    change
      totalWeight
        (atoms.map fun atom =>
          (atom.1, atom.2 / totalWeight atoms)) = 1
    exact totalWeight_div atoms hnonzero

/-- Point mass after normalization is the raw point weight divided by the
raw total weight. -/
theorem mass_normalize [DecidableEq α]
    (atoms : List (α × ℚ≥0)) (hnonzero : totalWeight atoms ≠ 0)
    (outcome : α) :
    (normalize atoms hnonzero).mass outcome =
      (atoms.map fun atom =>
        if atom.1 = outcome then atom.2 else 0).sum /
        totalWeight atoms := by
  unfold normalize mass eventMass
  simp only [List.map_map, Function.comp_def]
  have sum_indicator_div
      (raw : List (α × ℚ≥0)) (divisor : ℚ≥0) :
      (raw.map fun atom =>
        if decide (atom.1 = outcome) then atom.2 / divisor else 0).sum =
        (raw.map fun atom =>
          if atom.1 = outcome then atom.2 else 0).sum / divisor := by
    induction raw with
    | nil => simp
    | cons atom raw ih =>
        rcases atom with ⟨candidate, weight⟩
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        by_cases heq : candidate = outcome
        · simp [heq, add_div]
        · simp [heq]
  exact sum_indicator_div atoms (totalWeight atoms)

/-- Normalize a nonzero finite weighted list.

An all-zero or empty list returns `none`.  This is the computational boundary
used by conditioning: no law is invented for a zero-mass event. -/
def normalize? (atoms : List (α × ℚ≥0)) : Option (FiniteLaw α) :=
  if hzero : totalWeight atoms = 0 then
    none
  else
    some (normalize atoms hzero)

@[simp]
theorem normalize?_eq_none_iff (atoms : List (α × ℚ≥0)) :
    normalize? atoms = none ↔ totalWeight atoms = 0 := by
  simp [normalize?]

end FiniteLaw
