/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Core
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin

/-!
# Finite products of executable laws

This module constructs independent products by a fixed finite sampling order.
Use `finPi` for a dependent `Fin k` family and `fintypePi` for a family
with an explicit finite enumeration and linear order. The `FinPrefix` and
`finPiFrom` helpers expose the induction invariant used to prove product
identities; callers constructing a complete law normally use the two completed
product operations.

## Main definitions

* `FiniteLaw.independentPair`;
* `FiniteLaw.finPi` and `FiniteLaw.fintypePi`.

## Main statements

* `FiniteLaw.fintypePi_mass` gives the product formula for point masses;
* `FiniteLaw.fintypePi_reindex` makes enumeration order semantically irrelevant;
* `FiniteLaw.fintypePi_map_apply` recovers each coordinate marginal.
-/

namespace FiniteLaw

universe uα uβ

/-! ## Sampling pairs and dependent finite tuples -/

section FinProducts

variable {α β : Type*}

/-- Independent product of two finite laws, sampling the left component
first. -/
def independentPair (left : FiniteLaw α) (right : FiniteLaw β) :
    FiniteLaw (α × β) :=
  left.bind fun leftValue =>
    right.map fun rightValue => (leftValue, rightValue)

/-- Values already sampled below a numeric coordinate bound. -/
def FinPrefix {k : ℕ} (X : Fin k → Type uα)
    (count : ℕ) : Type uα :=
  (i : Fin k) → i.val < count → X i

namespace FinPrefix

variable {k : ℕ} {X : Fin k → Type uα}

/-- The empty dependent prefix. -/
def empty :
    FinPrefix X 0 :=
  fun i hi => (Nat.not_lt_zero i.val hi).elim

/-- Append the value at the next numeric coordinate. -/
def snoc
    {count : ℕ} (acc : FinPrefix X count)
    (hcount : count < k) (value : X ⟨count, hcount⟩) :
    FinPrefix X (count + 1) :=
  fun i hi =>
    if hprevious : i.val < count then
      acc i hprevious
    else
      have hvalue : i.val = count :=
        Nat.eq_of_lt_succ_of_not_lt hi hprevious
      have hindex : i = (⟨count, hcount⟩ : Fin k) :=
        Fin.ext hvalue
      hindex ▸ value

/-- Complete a prefix covering every coordinate. -/
def complete
    {count : ℕ} (acc : FinPrefix X count)
    (hcount : count = k) :
    (i : Fin k) → X i :=
  fun i => acc i (by omega)

/-- Restrict a complete tuple to a prefix. -/
def ofTuple
    (tuple : (i : Fin k) → X i) (count : ℕ) :
    FinPrefix X count :=
  fun i _ => tuple i

/-- Map every stored coordinate of a dependent prefix. -/
def map
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i)
    {count : ℕ} (acc : FinPrefix X count) :
    FinPrefix Y count :=
  fun i hi => f i (acc i hi)

@[simp]
lemma map_empty
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i) :
    map f (empty (X := X)) = empty (X := Y) := by
  funext i hi
  exact (Nat.not_lt_zero i.val hi).elim

@[simp]
lemma snoc_ofTuple
    (tuple : (i : Fin k) → X i) {count : ℕ}
    (hcount : count < k) :
    (ofTuple tuple count).snoc hcount
        (tuple ⟨count, hcount⟩) =
      ofTuple tuple (count + 1) := by
  funext i hi
  by_cases hprevious : i.val < count
  · simp [snoc, ofTuple, hprevious]
  · have hvalue : i.val = count := by omega
    have hindex : i = (⟨count, hcount⟩ : Fin k) := Fin.ext hvalue
    subst i
    simp [snoc, ofTuple]

@[simp]
lemma map_snoc
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i)
    {count : ℕ} (acc : FinPrefix X count)
    (hcount : count < k)
    (value : X ⟨count, hcount⟩) :
    map f (acc.snoc hcount value) =
      (map f acc).snoc hcount (f ⟨count, hcount⟩ value) := by
  funext i hi
  by_cases hprevious : i.val < count
  · simp [map, snoc, hprevious]
  · have hvalue : i.val = count := by omega
    have hindex : i = (⟨count, hcount⟩ : Fin k) := Fin.ext hvalue
    subst i
    simp [map, snoc]

@[simp]
lemma map_complete
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i)
    {count : ℕ} (acc : FinPrefix X count)
    (hcount : count = k) :
    (map f acc).complete hcount =
      fun i => f i (acc.complete hcount i) := by
  funext i
  rfl

end FinPrefix

/-- Independently sample the remaining coordinates after a fixed prefix. -/
def finPiFrom {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → FiniteLaw (X i)) :
    (remaining count : ℕ) →
      count + remaining = k →
      FinPrefix X count →
      FiniteLaw ((i : Fin k) → X i)
  | 0, _, htotal, acc =>
      pure (acc.complete (by omega))
  | remaining + 1, count, htotal, acc =>
      have hcount : count < k := by omega
      (laws ⟨count, hcount⟩).bind fun value =>
        finPiFrom laws remaining (count + 1) (by omega)
          (acc.snoc hcount value)

/-- Independent product of a finite dependent family.

Coordinates are processed in increasing `Fin` order. No `Fintype` instance
for the completed function space and no equality on coordinate values is
required. -/
def finPi (k : ℕ) {X : Fin k → Type uα}
    (laws : (i : Fin k) → FiniteLaw (X i)) :
    FiniteLaw ((i : Fin k) → X i) :=
  finPiFrom laws k 0 (by omega) FinPrefix.empty

/-- Independent point-mass coordinates give the point mass on the complete
dependent tuple. -/
lemma finPiFrom_pure {k : ℕ} {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k),
      finPiFrom (fun i => pure (tuple i))
          remaining count htotal
          (FinPrefix.ofTuple tuple count) =
        pure tuple := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal
      rw [finPiFrom]
      congr
  | succ remaining ih =>
      intro count htotal
      rw [finPiFrom, pure_bind, FinPrefix.snoc_ofTuple]
      exact ih (count + 1) (by omega)

/-- The independent product of point-mass laws is the point mass on the
corresponding tuple. -/
lemma finPi_pure (k : ℕ) {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) :
    finPi k (fun i => pure (tuple i)) = pure tuple := by
  unfold finPi
  have hprefix :
      (FinPrefix.empty (X := X)) =
        FinPrefix.ofTuple tuple 0 := by
    funext i hi
    exact (Nat.not_lt_zero i.val hi).elim
  rw [hprefix]
  exact finPiFrom_pure tuple k 0 (by omega)

/-- Dependent finite products commute with coordinatewise maps. -/
lemma finPiFrom_map {k : ℕ}
    {X : Fin k → Type uα} {Y : Fin k → Type uβ}
    (laws : (i : Fin k) → FiniteLaw (X i))
    (f : (i : Fin k) → X i → Y i) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k)
      (acc : FinPrefix X count),
      (finPiFrom laws remaining count htotal acc).map
          (fun tuple i => f i (tuple i)) =
        finPiFrom (fun i => (laws i).map (f i))
          remaining count htotal (acc.map f) := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal acc
      rw [finPiFrom, pure_map, finPiFrom]
      congr
  | succ remaining ih =>
      intro count htotal acc
      rw [finPiFrom, map_bind, finPiFrom, bind_map]
      congr 1
      funext value
      rw [ih]
      congr
      exact FinPrefix.map_snoc f acc (by omega) value

/-- The `Fin`-indexed independent product is natural under coordinatewise
maps. -/
lemma finPi_map (k : ℕ)
    {X : Fin k → Type uα} {Y : Fin k → Type uβ}
    (laws : (i : Fin k) → FiniteLaw (X i))
    (f : (i : Fin k) → X i → Y i) :
    (finPi k laws).map (fun tuple i => f i (tuple i)) =
      finPi k (fun i => (laws i).map (f i)) := by
  unfold finPi
  rw [finPiFrom_map]
  simp

end FinProducts

/-! ## Products indexed by an ordered finite type -/

private lemma piCongr_refl_apply
    {I J : Type*} (e : I ≃ J) (X : J → Type*)
    (tuple : (i : I) → X (e i)) (i : I) :
    (e.piCongr (fun j => Equiv.refl (X (e j))) tuple) (e i) =
      tuple i := by
  have h := congrFun
    ((e.piCongr
      (fun j => Equiv.refl (X (e j)))).symm_apply_apply tuple) i
  simpa only [Equiv.piCongr_symm_apply] using h

section FintypeProducts

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type uα}

/-- Independent product over an explicitly enumerable finite index type.

The supplied linear order turns `Fintype.elems` into an executable sorted
enumeration; no classical `Fintype.equivFin` choice is used. -/
def fintypePi
    (laws : (i : I) → FiniteLaw (X i)) :
    FiniteLaw ((i : I) → X i) :=
  let indices : List I := Finset.univ.sort (· ≤ ·)
  let e : Fin indices.length ≃ I :=
    List.Nodup.getEquivOfForallMemList indices
      (by simp [indices])
      (by intro i; simp [indices])
  (finPi indices.length (fun j => laws (e j))).map
    (e.piCongr fun _ => Equiv.refl _)

/-- Arbitrary finite independent products commute with coordinatewise maps. -/
lemma fintypePi_map {Y : I → Type uβ}
    (laws : (i : I) → FiniteLaw (X i))
    (f : (i : I) → X i → Y i) :
    (fintypePi laws).map (fun tuple i => f i (tuple i)) =
      fintypePi (fun i => (laws i).map (f i)) := by
  let indices : List I := Finset.univ.sort (· ≤ ·)
  let e : Fin indices.length ≃ I :=
    List.Nodup.getEquivOfForallMemList indices
      (by simp [indices])
      (by intro i; simp [indices])
  let reindexX :
      ((j : Fin indices.length) → X (e j)) →
        ((i : I) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  let reindexY :
      ((j : Fin indices.length) → Y (e j)) →
        ((i : I) → Y i) :=
    e.piCongr fun _ => Equiv.refl _
  let mapFin :
      ((j : Fin indices.length) → X (e j)) →
        ((j : Fin indices.length) → Y (e j)) :=
    fun tuple j => f (e j) (tuple j)
  let mapIndex : ((i : I) → X i) → ((i : I) → Y i) :=
    fun tuple i => f i (tuple i)
  change
    ((finPi indices.length
        (fun j => laws (e j))).map reindexX).map mapIndex =
      (finPi indices.length
        (fun j => (laws (e j)).map (f (e j)))).map reindexY
  calc
    ((finPi indices.length
        (fun j => laws (e j))).map reindexX).map mapIndex =
        (finPi indices.length
          (fun j => laws (e j))).map (mapIndex ∘ reindexX) :=
      map_comp reindexX _ mapIndex
    _ = (finPi indices.length
          (fun j => laws (e j))).map (reindexY ∘ mapFin) := by
      congr 1
      funext tuple i
      change
        f i
            ((e.piCongr
              (fun j => Equiv.refl (X (e j))) tuple) i) =
          (e.piCongr
            (fun j => Equiv.refl (Y (e j)))
            (fun j => f (e j) (tuple j))) i
      let j := e.symm i
      have hindex : e j = i := e.apply_symm_apply i
      rw [← hindex, piCongr_refl_apply, piCongr_refl_apply]
    _ = ((finPi indices.length
          (fun j => laws (e j))).map mapFin).map reindexY :=
      (map_comp mapFin _ reindexY).symm
    _ = (finPi indices.length
          (fun j => (laws (e j)).map (f (e j)))).map reindexY := by
      rw [finPi_map]

/-- Arbitrary finite independent point masses give the point mass on the
complete tuple. -/
lemma fintypePi_pure (tuple : (i : I) → X i) :
    fintypePi (fun i => pure (tuple i)) = pure tuple := by
  let indices : List I := Finset.univ.sort (· ≤ ·)
  let e : Fin indices.length ≃ I :=
    List.Nodup.getEquivOfForallMemList indices
      (by simp [indices])
      (by intro i; simp [indices])
  let reindex :
      ((j : Fin indices.length) → X (e j)) →
        ((i : I) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  change
    (finPi indices.length
      (fun j => pure (tuple (e j)))).map reindex = pure tuple
  rw [finPi_pure, pure_map]
  congr
  funext i
  change
    (e.piCongr
      (fun j => Equiv.refl (X (e j)))
      (fun j => tuple (e j))) i = tuple i
  let j := e.symm i
  have hindex : e j = i := e.apply_symm_apply i
  rw [← hindex, piCongr_refl_apply]

end FintypeProducts

/-! ## Positive atoms and the product mass formula -/

section ProductMass

/-- Every positive outcome of a completion law extends its fixed prefix. -/
lemma finPiFrom_apply_eq_of_hasPositiveAtom_of_lt
    {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → FiniteLaw (X i)) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k)
      (acc : FinPrefix X count)
      (outcome : (i : Fin k) → X i),
      (finPiFrom laws remaining count htotal acc).HasPositiveAtom outcome →
      ∀ (i : Fin k) (hi : i.val < count),
        outcome i = acc i hi := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal acc outcome houtcome i hi
      simp only [finPiFrom] at houtcome
      have houtcomeEq := (hasPositiveAtom_pure_iff _ _).mp houtcome
      subst outcome
      rfl
  | succ remaining ih =>
      intro count htotal acc outcome houtcome i hi
      simp only [finPiFrom] at houtcome
      obtain ⟨value, _, houtcome⟩ :=
        (hasPositiveAtom_bind_iff _ _ _).mp houtcome
      have hnext : i.val < count + 1 := by omega
      rw [ih (count + 1) (by omega)
        (acc.snoc (by omega) value) outcome houtcome i hnext]
      simp [FinPrefix.snoc, hi]

private def finPiMassFrom {k : ℕ} {X : Fin k → Type uα}
    [∀ i, DecidableEq (X i)]
    (laws : (i : Fin k) → FiniteLaw (X i))
    (tuple : (i : Fin k) → X i) :
    (remaining count : ℕ) → count + remaining = k → ℚ≥0
  | 0, _, _ => 1
  | remaining + 1, count, htotal =>
      (laws ⟨count, by omega⟩).mass (tuple ⟨count, by omega⟩) *
        finPiMassFrom laws tuple remaining (count + 1) (by omega)

private lemma sum_weight_mul_indicator
    [DecidableEq α] (law : FiniteLaw α)
    (target : α) (constant : ℚ≥0) :
    (law.atoms.map fun atom =>
      atom.2 * if atom.1 = target then constant else 0).sum =
      law.mass target * constant := by
  unfold mass eventMass
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      by_cases heq : outcome = target
      · simp [heq, add_mul]
      · simp [heq]

private lemma mass_map_pair_left
    [DecidableEq α] [DecidableEq β]
    (law : FiniteLaw β) (left : α) (target : α × β) :
    (law.map fun right => (left, right)).mass target =
      if left = target.1 then law.mass target.2 else 0 := by
  rcases target with ⟨targetLeft, targetRight⟩
  unfold mass eventMass
  rw [map_atoms, List.map_map]
  by_cases heq : left = targetLeft
  · subst left
    simp [Function.comp_def]
  · simp [heq, Function.comp_def]

/-- Point mass of an independent pair factors into the point masses of its
two coordinates. -/
theorem independentPair_mass
    [DecidableEq α] [DecidableEq β]
    (left : FiniteLaw α) (right : FiniteLaw β)
    (target : α × β) :
    (independentPair left right).mass target =
      left.mass target.1 * right.mass target.2 := by
  unfold independentPair
  rw [mass_bind]
  calc
    (left.atoms.map fun atom => atom.2 *
        (right.map fun rightValue =>
          (atom.1, rightValue)).mass target).sum =
        (left.atoms.map fun atom => atom.2 *
          if atom.1 = target.1 then right.mass target.2 else 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro atom _
      rw [mass_map_pair_left]
    _ = left.mass target.1 * right.mass target.2 :=
      sum_weight_mul_indicator left target.1 (right.mass target.2)

private lemma finPiFrom_mass_of_prefix
    {k : ℕ} {X : Fin k → Type uα}
    [∀ i, DecidableEq (X i)]
    [DecidableEq ((i : Fin k) → X i)]
    (laws : (i : Fin k) → FiniteLaw (X i))
    (tuple : (i : Fin k) → X i) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k)
      (acc : FinPrefix X count)
      (_hprefix : ∀ (i : Fin k) (hi : i.val < count),
        tuple i = acc i hi),
      (finPiFrom laws remaining count htotal acc).mass tuple =
        finPiMassFrom laws tuple remaining count htotal := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal acc hprefix
      rw [finPiFrom]
      have htuple : acc.complete (by omega) = tuple := by
        funext i
        exact (hprefix i (by omega)).symm
      simp [finPiMassFrom, htuple]
  | succ remaining ih =>
      intro count htotal acc hprefix
      rw [finPiFrom, mass_bind]
      rw [finPiMassFrom]
      let current : Fin k := ⟨count, by omega⟩
      let tailMass : ℚ≥0 :=
        finPiMassFrom laws tuple remaining (count + 1) (by omega)
      have hcontinuation (sampled : X current) :
          (finPiFrom laws remaining (count + 1) (by omega)
              (acc.snoc (by omega) sampled)).mass tuple =
            if sampled = tuple current then tailMass else 0 := by
        by_cases heq : sampled = tuple current
        · rw [if_pos heq]
          subst sampled
          apply ih (count + 1) (by omega)
          intro i hi
          by_cases hprevious : i.val < count
          · simp [FinPrefix.snoc, hprevious, hprefix i hprevious]
          · have hindex : i = current := by
              apply Fin.ext
              simp only [current]
              omega
            subst i
            simp [FinPrefix.snoc, current]
        · rw [if_neg heq]
          apply mass_eq_zero_of_not_hasPositiveAtom
          intro hpositive
          have hcurrent :=
            finPiFrom_apply_eq_of_hasPositiveAtom_of_lt
              laws remaining (count + 1) (by omega)
              (acc.snoc (by omega) sampled) tuple hpositive
              current (by simp [current])
          apply heq
          simpa [FinPrefix.snoc, current] using hcurrent.symm
      calc
        (List.map
            (fun atom =>
              atom.2 *
                (finPiFrom laws remaining (count + 1) (by omega)
                  (acc.snoc (by omega) atom.1)).mass tuple)
            (laws current).atoms).sum =
            (List.map
              (fun atom => atom.2 *
                if atom.1 = tuple current then tailMass else 0)
              (laws current).atoms).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro atom _
          rw [hcontinuation atom.1]
        _ = (laws current).mass (tuple current) * tailMass :=
          sum_weight_mul_indicator (laws current) (tuple current) tailMass
        _ = _ := rfl

/-- The point mass of a `Fin`-indexed independent product is the recursive
product of its coordinate masses in increasing index order. -/
theorem finPi_mass (k : ℕ) {X : Fin k → Type uα}
    [∀ i, DecidableEq (X i)]
    [DecidableEq ((i : Fin k) → X i)]
    (laws : (i : Fin k) → FiniteLaw (X i))
    (tuple : (i : Fin k) → X i) :
    (finPi k laws).mass tuple =
      finPiMassFrom laws tuple k 0 (by omega) := by
  unfold finPi
  exact finPiFrom_mass_of_prefix laws tuple k 0 (by omega)
    FinPrefix.empty (by intro i hi; omega)

private lemma finPiMassFrom_eq_prod
    {k : ℕ} {X : Fin k → Type uα}
    [∀ i, DecidableEq (X i)]
    (laws : (i : Fin k) → FiniteLaw (X i))
    (tuple : (i : Fin k) → X i) :
    ∀ (remaining count : ℕ) (htotal : count + remaining = k),
      finPiMassFrom laws tuple remaining count htotal =
        ∏ i ∈ (Finset.univ.filter fun i : Fin k => count ≤ i.val),
          (laws i).mass (tuple i) := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal
      rw [finPiMassFrom]
      apply (Finset.prod_eq_one ?_).symm
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
  | succ remaining ih =>
      intro count htotal
      rw [finPiMassFrom]
      let current : Fin k := ⟨count, by omega⟩
      have hfilter :
          (Finset.univ.filter fun i : Fin k => count ≤ i.val) =
            insert current
              (Finset.univ.filter fun i : Fin k => count + 1 ≤ i.val) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hi
          by_cases heq : i.val = count
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (heq | hi)
          · subst i
            simp [current]
          · omega
      rw [hfilter, Finset.prod_insert]
      · rw [ih (count + 1) (by omega)]
      · simp [current]

/-- Point mass of an arbitrary finite dependent product is the commutative
product of its coordinate point masses. -/
theorem fintypePi_mass {I : Type*} [Fintype I] [LinearOrder I]
    {X : I → Type uα}
    [∀ i, DecidableEq (X i)]
    [DecidableEq ((i : I) → X i)]
    (laws : (i : I) → FiniteLaw (X i))
    (tuple : (i : I) → X i) :
    (fintypePi laws).mass tuple =
      ∏ i, (laws i).mass (tuple i) := by
  let indices : List I := Finset.univ.sort (· ≤ ·)
  let e : Fin indices.length ≃ I :=
    List.Nodup.getEquivOfForallMemList indices
      (by simp [indices])
      (by intro i; simp [indices])
  let reindex :
      ((j : Fin indices.length) → X (e j)) →
        ((i : I) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  change
    ((finPi indices.length
      (fun j => laws (e j))).map reindex).mass tuple = _
  rw [mass_map_equiv, finPi_mass, finPiMassFrom_eq_prod]
  simp only [Nat.zero_le, Finset.filter_true]
  apply Fintype.prod_equiv e
  intro j
  congr 2

end ProductMass

/-! ## Reindexing and coordinate marginals -/

section Marginals

/-- Reindexing an independent finite product along an equivalence preserves
its exact distribution, although the sparse atom order may change. -/
theorem fintypePi_reindex
    {I J : Type*} [Fintype I] [LinearOrder I]
    [Fintype J] [LinearOrder J]
    (e : I ≃ J) {X : J → Type uα}
    (laws : (j : J) → FiniteLaw (X j)) :
    ((fintypePi (fun i : I => laws (e i))).map
      (e.piCongr fun _ => Equiv.refl _)).Equivalent
        (fintypePi laws) := by
  classical
  apply Equivalent.of_mass_eq
  intro tuple
  rw [mass_map_equiv, fintypePi_mass, fintypePi_mass]
  apply Fintype.prod_equiv e
  intro i
  congr 2

section PrefixMarginals

variable {k : ℕ} {X : Fin k → Type uα}
variable (laws : (i : Fin k) → FiniteLaw (X i))

private lemma expectRat_finPiFrom_lt
    (remaining count : ℕ) (htotal : count + remaining = k)
    (acc : FinPrefix X count) (i : Fin k) (hi : i.val < count)
    (value : X i → ℚ) :
    (finPiFrom laws remaining count htotal acc).expectRat
        (fun outcome => value (outcome i)) =
      value (acc i hi) := by
  induction remaining generalizing count i value with
  | zero =>
      simp only [finPiFrom, expectRat_pure]
      rfl
  | succ remaining ih =>
      simp only [finPiFrom, expectRat_bind]
      calc
        (laws ⟨count, by omega⟩).expectRat
            (fun sampled =>
              (finPiFrom laws remaining (count + 1) (by omega)
                  (acc.snoc (by omega) sampled)).expectRat
                (fun outcome => value (outcome i))) =
            (laws ⟨count, by omega⟩).expectRat
              (fun _ => value (acc i hi)) := by
          congr 1
          funext sampled
          rw [ih (count := count + 1) (htotal := by omega)
            (acc := acc.snoc (by omega) sampled) (hi := by omega)]
          congr 1
          simp [FinPrefix.snoc, hi]
        _ = value (acc i hi) := expectRat_const _ _

private lemma expectRat_finPiFrom_ge
    (remaining count : ℕ) (htotal : count + remaining = k)
    (acc : FinPrefix X count) (i : Fin k) (hi : count ≤ i.val)
    (value : X i → ℚ) :
    (finPiFrom laws remaining count htotal acc).expectRat
        (fun outcome => value (outcome i)) =
      (laws i).expectRat value := by
  induction remaining generalizing count i value with
  | zero => omega
  | succ remaining ih =>
      simp only [finPiFrom, expectRat_bind]
      by_cases hcurrent : i.val = count
      · rcases i with ⟨index, hindex⟩
        simp only at hcurrent
        subst index
        calc
          (laws ⟨count, hindex⟩).expectRat
              (fun sampled =>
                (finPiFrom laws remaining (count + 1) (by omega)
                    (acc.snoc hindex sampled)).expectRat
                  (fun outcome => value (outcome ⟨count, hindex⟩))) =
              (laws ⟨count, hindex⟩).expectRat value := by
            congr 1
            funext sampled
            rw [expectRat_finPiFrom_lt laws remaining (count + 1)
              (by omega) (acc.snoc hindex sampled)
              ⟨count, hindex⟩ (Nat.lt_succ_self count) value]
            congr 1
            simp [FinPrefix.snoc]
          _ = (laws ⟨count, hindex⟩).expectRat value := rfl
      · have hnext : count + 1 ≤ i.val := by omega
        calc
          (laws ⟨count, by omega⟩).expectRat
              (fun sampled =>
                (finPiFrom laws remaining (count + 1) (by omega)
                    (acc.snoc (by omega) sampled)).expectRat
                  (fun outcome => value (outcome i))) =
              (laws ⟨count, by omega⟩).expectRat
                (fun _ => (laws i).expectRat value) := by
            congr 1
            funext sampled
            exact ih (count := count + 1) (htotal := by omega)
              (acc := acc.snoc (by omega) sampled) (i := i) hnext value
          _ = (laws i).expectRat value := expectRat_const _ _

end PrefixMarginals

/-- Every coordinate of the finite dependent product has the declared exact
marginal law. -/
theorem finPi_map_apply
    (k : ℕ) {X : Fin k → Type uα}
    (laws : (i : Fin k) → FiniteLaw (X i)) (i : Fin k) :
    ((finPi k laws).map fun outcome => outcome i).Equivalent (laws i) := by
  intro value
  change
    ((finPi k laws).map fun outcome => outcome i).expectRat value =
      (laws i).expectRat value
  rw [expectRat_map]
  exact expectRat_finPiFrom_ge laws k 0 (by omega)
    FinPrefix.empty i (by omega) value

/-- Every coordinate of an arbitrary finite dependent product has the
declared exact marginal law. -/
theorem fintypePi_map_apply {I : Type*} [Fintype I] [LinearOrder I]
    {X : I → Type uα} (laws : (i : I) → FiniteLaw (X i)) (i : I) :
    ((fintypePi laws).map fun outcome => outcome i).Equivalent (laws i) := by
  let indices : List I := Finset.univ.sort (· ≤ ·)
  let e : Fin indices.length ≃ I :=
    List.Nodup.getEquivOfForallMemList indices
      (by simp [indices])
      (by intro target; simp [indices])
  let reindex :
      ((j : Fin indices.length) → X (e j)) →
        ((target : I) → X target) :=
    e.piCongr fun _ => Equiv.refl _
  let j := e.symm i
  have hindex : e j = i := e.apply_symm_apply i
  change
    (((finPi indices.length (fun coordinate => laws (e coordinate))).map
        reindex).map fun outcome => outcome i).Equivalent (laws i)
  rw [← hindex, map_comp]
  have hmap :
      (fun outcome => outcome (e j)) ∘ reindex =
        fun outcome => outcome j := by
    funext outcome
    change
      (e.piCongr
        (fun coordinate => Equiv.refl (X (e coordinate))) outcome) (e j) =
        outcome j
    rw [piCongr_refl_apply]
  rw [hmap]
  exact finPi_map_apply indices.length (fun coordinate => laws (e coordinate)) j

end Marginals

end FiniteLaw
