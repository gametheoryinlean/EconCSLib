/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF.Equiv

/-!
# EconCSLib.Math.Probability.PMF.FiniteProduct

Finite dependent products of discrete probability mass functions.

This module constructs independent laws for finite dependent families without
assuming a uniform coordinate type. `FinPrefix` supplies the accumulator used
for `Fin k`; `finPi` and `fintypePi` expose the resulting complete dependent
tables. Point-mass formulas, coordinate splitting, selected-coordinate
marginals, and reindexing invariance make the construction usable by deferred
sampling and conditional-product proofs.

## Main definitions

* `PMF.FinPrefix`;
* `PMF.finPiFrom` and `PMF.finPi`;
* `PMF.fintypePi`.

## Main results

* `PMF.finPi_apply` and `PMF.fintypePi_apply`;
* `PMF.fintypePi_map_apply`;
* the finite-coordinate splitting and reindexing theorems.
-/

namespace PMF

universe uα uβ

/-- Values already sampled for all coordinates whose numeric index is below
`count`.  This prefix presentation is shared with sequential serializers:
sampling one more coordinate is exactly `FinPrefix.snoc`. -/
def FinPrefix {k : ℕ} (X : Fin k → Type uα) (count : ℕ) : Type uα :=
  (i : Fin k) → i.val < count → X i

namespace FinPrefix

/-- The empty prefix. -/
def empty {k : ℕ} {X : Fin k → Type uα} :
    FinPrefix X 0 :=
  fun i hi => (Nat.not_lt_zero i.val hi).elim

/-- Append the value at coordinate `count`. -/
def snoc {k : ℕ} {X : Fin k → Type uα} {count : ℕ}
    (acc : FinPrefix X count)
    (hcount : count < k)
    (value : X ⟨count, hcount⟩) :
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

/-- Turn a prefix covering all `k` coordinates into a dependent tuple. -/
def complete {k : ℕ} {X : Fin k → Type uα} {count : ℕ}
    (acc : FinPrefix X count)
    (hcount : count = k) :
    (i : Fin k) → X i :=
  fun i => acc i (by omega)

/-- The prefix obtained by restricting a complete dependent tuple. -/
def ofTuple {k : ℕ} {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) (count : ℕ) :
    FinPrefix X count :=
  fun i _ => tuple i

/-- Map every stored coordinate of a dependent prefix. -/
def map {k : ℕ} {X : Fin k → Type uα}
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i)
    {count : ℕ} (acc : FinPrefix X count) :
    FinPrefix Y count :=
  fun i hi => f i (acc i hi)

@[simp]
theorem map_empty {k : ℕ} {X : Fin k → Type uα}
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i) :
    map f (empty (X := X)) = empty (X := Y) := by
  funext i hi
  exact (Nat.not_lt_zero i.val hi).elim

@[simp]
theorem snoc_ofTuple {k : ℕ} {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) {count : ℕ}
    (hcount : count < k) :
    (ofTuple tuple count).snoc hcount
        (tuple ⟨count, hcount⟩) =
      ofTuple tuple (count + 1) := by
  funext i hi
  by_cases hprevious : i.val < count
  · simp [snoc, ofTuple, hprevious]
  · have hvalue : i.val = count := by omega
    have hindex : i = (⟨count, hcount⟩ : Fin k) :=
      Fin.ext hvalue
    subst i
    simp [snoc, ofTuple]

@[simp]
theorem map_snoc {k : ℕ} {X : Fin k → Type uα}
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
    have hindex : i = (⟨count, hcount⟩ : Fin k) :=
      Fin.ext hvalue
    subst i
    simp [map, snoc]

@[simp]
theorem complete_ofTuple {k : ℕ} {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i)
    {count : ℕ} (hcount : count = k) :
    (ofTuple tuple count).complete hcount = tuple := by
  funext i
  rfl

@[simp]
theorem map_complete {k : ℕ} {X : Fin k → Type uα}
    {Y : Fin k → Type uβ}
    (f : (i : Fin k) → X i → Y i)
    {count : ℕ} (acc : FinPrefix X count)
    (hcount : count = k) :
    (map f acc).complete hcount =
      fun i => f i (acc.complete hcount i) := by
  funext i
  rfl

end FinPrefix

/-- Independently sample the remaining coordinates after a fixed prefix.

The recursion is on `remaining`; the equation `count + remaining = k` keeps
the next coordinate and the final completeness proof explicit.  This is the
accumulator form needed to identify simultaneous dependent products with
turn-taking behavioral execution. -/
noncomputable def finPiFrom {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i)) :
    (remaining count : ℕ) →
      count + remaining = k →
      FinPrefix X count →
      PMF ((i : Fin k) → X i)
  | 0, count, htotal, acc =>
      PMF.pure (acc.complete (by omega))
  | remaining + 1, count, htotal, acc =>
      have hcount : count < k := by omega
      (laws ⟨count, hcount⟩).bind fun value =>
        finPiFrom laws remaining (count + 1) (by omega)
          (acc.snoc hcount value)

/-- Independent product of a finite dependent family of PMFs.

Coordinates are sampled in increasing `Fin` order while accumulating a
prefix. This supplies the joint-action law induced by a behavioral-strategy
profile without requiring finite action types, and its operational order
matches the finite-player FOSG serializer. -/
noncomputable def finPi (k : ℕ) {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i)) :
    PMF ((i : Fin k) → X i) :=
  finPiFrom laws k 0 (by omega) FinPrefix.empty

/-- Independent Dirac coordinates give the Dirac law on the complete
dependent tuple. -/
theorem finPiFrom_pure {k : ℕ} {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k),
      finPiFrom (fun i => PMF.pure (tuple i))
          remaining count htotal
          (FinPrefix.ofTuple tuple count) =
        PMF.pure tuple := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal
      rw [finPiFrom]
      congr
  | succ remaining ih =>
      intro count htotal
      have hcount : count < k := by omega
      rw [finPiFrom, PMF.pure_bind,
        FinPrefix.snoc_ofTuple]
      exact ih (count + 1) (by omega)

/-- The independent product of a finite family of Dirac laws is the Dirac
law on the corresponding tuple. -/
theorem finPi_pure (k : ℕ) {X : Fin k → Type uα}
    (tuple : (i : Fin k) → X i) :
    finPi k (fun i => PMF.pure (tuple i)) =
      PMF.pure tuple := by
  unfold finPi
  have hprefix :
      (FinPrefix.empty (X := X)) =
        FinPrefix.ofTuple tuple 0 := by
    funext i hi
    exact (Nat.not_lt_zero i.val hi).elim
  rw [hprefix]
  exact finPiFrom_pure tuple k 0 (by omega)

/-- Independent dependent products commute with coordinatewise maps. -/
theorem finPiFrom_map {k : ℕ}
    {X : Fin k → Type uα} {Y : Fin k → Type uβ}
    (laws : (i : Fin k) → PMF (X i))
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
      rw [finPiFrom, PMF.pure_map, finPiFrom]
      congr
  | succ remaining ih =>
      intro count htotal acc
      have hcount : count < k := by omega
      rw [finPiFrom, PMF.map_bind, finPiFrom, PMF.bind_map]
      congr 1
      funext value
      rw [ih]
      congr
      exact FinPrefix.map_snoc f acc hcount value

/-- The finite-`Fin` independent product is natural under coordinatewise
maps. -/
theorem finPi_map (k : ℕ)
    {X : Fin k → Type uα} {Y : Fin k → Type uβ}
    (laws : (i : Fin k) → PMF (X i))
    (f : (i : Fin k) → X i → Y i) :
    (finPi k laws).map (fun tuple i => f i (tuple i)) =
      finPi k (fun i => (laws i).map (f i)) := by
  unfold finPi
  rw [finPiFrom_map]
  simp

/-- Independent product of a dependent PMF family over an arbitrary finite
index type.

The implementation chooses the canonical `Fintype.equivFin` enumeration.
The exposed naturality and Dirac theorems make downstream semantics
independent of this implementation detail. -/
noncomputable def fintypePi {ι : Type*} [Fintype ι]
    {X : ι → Type uα}
    (laws : (i : ι) → PMF (X i)) :
    PMF ((i : ι) → X i) :=
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  (finPi (Fintype.card ι) (fun j => laws (e j))).map
    (e.piCongr fun _ => Equiv.refl _)

private theorem piCongr_refl_apply
    {α β : Type*} (e : α ≃ β) (X : β → Type*)
    (tuple : (a : α) → X (e a)) (a : α) :
    (e.piCongr (fun a => Equiv.refl (X (e a))) tuple) (e a) =
      tuple a := by
  have h :=
    congrFun
      ((e.piCongr
        (fun a => Equiv.refl (X (e a)))).symm_apply_apply tuple)
      a
  simpa only [Equiv.piCongr_symm_apply] using h

/-- Arbitrary-finite independent products commute with coordinatewise maps. -/
theorem fintypePi_map {ι : Type*} [Fintype ι]
    {X : ι → Type uα} {Y : ι → Type uβ}
    (laws : (i : ι) → PMF (X i))
    (f : (i : ι) → X i → Y i) :
    (fintypePi laws).map (fun tuple i => f i (tuple i)) =
      fintypePi (fun i => (laws i).map (f i)) := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  let reindexX :
      ((j : Fin (Fintype.card ι)) → X (e j)) →
        ((i : ι) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  let reindexY :
      ((j : Fin (Fintype.card ι)) → Y (e j)) →
        ((i : ι) → Y i) :=
    e.piCongr fun _ => Equiv.refl _
  let mapFin :
      ((j : Fin (Fintype.card ι)) → X (e j)) →
        ((j : Fin (Fintype.card ι)) → Y (e j)) :=
    fun tuple j => f (e j) (tuple j)
  let mapIndex :
      ((i : ι) → X i) → ((i : ι) → Y i) :=
    fun tuple i => f i (tuple i)
  change
    ((finPi (Fintype.card ι)
        (fun j => laws (e j))).map reindexX).map mapIndex =
      (finPi (Fintype.card ι)
        (fun j => (laws (e j)).map (f (e j)))).map reindexY
  calc
    ((finPi (Fintype.card ι)
        (fun j => laws (e j))).map reindexX).map mapIndex =
        (finPi (Fintype.card ι)
          (fun j => laws (e j))).map
            (mapIndex ∘ reindexX) :=
      PMF.map_comp reindexX
        (finPi (Fintype.card ι)
          (fun j => laws (e j))) mapIndex
    _ = (finPi (Fintype.card ι)
          (fun j => laws (e j))).map
            (reindexY ∘ mapFin) := by
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
    _ = ((finPi (Fintype.card ι)
          (fun j => laws (e j))).map mapFin).map
            reindexY :=
      (PMF.map_comp mapFin
        (finPi (Fintype.card ι)
          (fun j => laws (e j))) reindexY).symm
    _ = (finPi (Fintype.card ι)
          (fun j => (laws (e j)).map (f (e j)))).map
            reindexY := by
      rw [finPi_map]

/-- Arbitrary-finite independent Dirac coordinates give a Dirac profile. -/
theorem fintypePi_pure {ι : Type*} [Fintype ι]
    {X : ι → Type uα}
    (tuple : (i : ι) → X i) :
    fintypePi (fun i => PMF.pure (tuple i)) =
      PMF.pure tuple := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  let reindex :
      ((j : Fin (Fintype.card ι)) → X (e j)) →
        ((i : ι) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  change
    (finPi (Fintype.card ι)
      (fun j => PMF.pure (tuple (e j)))).map reindex =
        PMF.pure tuple
  rw [finPi_pure, PMF.pure_map]
  congr
  funext i
  change
    (e.piCongr
      (fun j => Equiv.refl (X (e j)))
      (fun j => tuple (e j))) i =
        tuple i
  let j := e.symm i
  have hindex : e j = i := e.apply_symm_apply i
  rw [← hindex, piCongr_refl_apply]

/-- A coordinate of the accumulator product is already fixed when it lies in
the supplied prefix, and otherwise retains its declared component law. -/
theorem finPiFrom_map_apply {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i)) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k)
      (acc : FinPrefix X count)
      (i : Fin k),
      (finPiFrom laws remaining count htotal acc).map
          (fun outcome => outcome i) =
        if hi : i.val < count then
          PMF.pure (acc i hi)
        else
          laws i := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal acc i
      have hi : i.val < count := by omega
      rw [finPiFrom, PMF.pure_map, dif_pos hi]
      congr
  | succ remaining ih =>
      intro count htotal acc i
      have hcount : count < k := by omega
      rw [finPiFrom, PMF.map_bind]
      by_cases hprevious : i.val < count
      · have hnext : i.val < count + 1 := by omega
        calc
          (laws ⟨count, hcount⟩).bind
              (fun value =>
                (finPiFrom laws remaining (count + 1) (by omega)
                  (acc.snoc hcount value)).map
                    (fun outcome => outcome i)) =
              (laws ⟨count, hcount⟩).bind
                (fun _ => PMF.pure (acc i hprevious)) := by
                  congr 1
                  funext value
                  rw [ih]
                  simp [hnext, FinPrefix.snoc, hprevious]
          _ = PMF.pure (acc i hprevious) :=
            PMF.bind_const _ _
          _ = if hi : i.val < count then
                PMF.pure (acc i hi)
              else laws i := by
            simp [hprevious]
      · by_cases hcurrent : i.val = count
        · have hindex : i = (⟨count, hcount⟩ : Fin k) :=
            Fin.ext hcurrent
          subst i
          have hnext : count < count + 1 := by omega
          calc
            (laws ⟨count, hcount⟩).bind
                (fun value =>
                  (finPiFrom laws remaining (count + 1) (by omega)
                    (acc.snoc hcount value)).map
                      (fun outcome => outcome ⟨count, hcount⟩)) =
                (laws ⟨count, hcount⟩).bind PMF.pure := by
                  congr 1
                  funext value
                  rw [ih]
                  simp [hnext, FinPrefix.snoc]
            _ = laws ⟨count, hcount⟩ := PMF.bind_pure _
            _ = if hi : count < count then
                  PMF.pure (acc ⟨count, hcount⟩ hi)
                else laws ⟨count, hcount⟩ := by
              simp
        · have hnext : ¬ i.val < count + 1 := by omega
          calc
            (laws ⟨count, hcount⟩).bind
                (fun value =>
                  (finPiFrom laws remaining (count + 1) (by omega)
                    (acc.snoc hcount value)).map
                      (fun outcome => outcome i)) =
                (laws ⟨count, hcount⟩).bind
                  (fun _ => laws i) := by
                    congr 1
                    funext value
                    rw [ih]
                    simp [hnext]
            _ = laws i := PMF.bind_const _ _
            _ = if hi : i.val < count then
                  PMF.pure (acc i hi)
                else laws i := by
              simp [hprevious]

/-- Every coordinate marginal of `finPi` is its declared component law. -/
theorem finPi_map_apply (k : ℕ) {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i)) (i : Fin k) :
    (finPi k laws).map (fun outcome => outcome i) = laws i := by
  rw [finPi, finPiFrom_map_apply]
  simp

/-- Every coordinate marginal of an arbitrary-finite independent product is
its declared component law. -/
theorem fintypePi_map_apply {ι : Type*} [Fintype ι]
    {X : ι → Type uα}
    (laws : (i : ι) → PMF (X i)) (i : ι) :
    (fintypePi laws).map (fun tuple => tuple i) =
      laws i := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  let reindex :
      ((j : Fin (Fintype.card ι)) → X (e j)) →
        ((index : ι) → X index) :=
    e.piCongr fun _ => Equiv.refl _
  let j := e.symm i
  have hindex : e j = i :=
    e.apply_symm_apply i
  rw [← hindex]
  change
    ((finPi (Fintype.card ι)
      (fun index => laws (e index))).map
        reindex).map (fun tuple => tuple (e j)) =
      laws (e j)
  rw [PMF.map_comp]
  convert
    finPi_map_apply
      (Fintype.card ι)
      (fun index => laws (e index)) j using 1
  congr 1
  funext tuple
  change
    (e.piCongr
      (fun index =>
        Equiv.refl (X (e index)))
      tuple) (e j) =
        tuple j
  exact piCongr_refl_apply e X tuple j

/-- Every outcome in the support of a completion law extends its fixed
prefix pointwise. -/
theorem finPiFrom_apply_eq_of_mem_support_of_lt
    {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i))
    (remaining count : ℕ)
    (htotal : count + remaining = k)
    (acc : FinPrefix X count)
    (outcome : (i : Fin k) → X i)
    (houtcome :
      outcome ∈ (finPiFrom laws remaining count htotal acc).support)
    (i : Fin k) (hi : i.val < count) :
    outcome i = acc i hi := by
  have hmapped :
      outcome i ∈
        ((finPiFrom laws remaining count htotal acc).map
          (fun result => result i)).support :=
    (PMF.mem_support_map_iff
      (p := finPiFrom laws remaining count htotal acc)
      (f := fun result => result i)
      (b := outcome i)).mpr
        ⟨outcome, houtcome, rfl⟩
  rw [finPiFrom_map_apply, dif_pos hi] at hmapped
  exact (PMF.mem_support_pure_iff _ _).mp hmapped

/-- A completion has zero mass when it disagrees with a fixed prefix
coordinate. -/
theorem finPiFrom_apply_eq_zero_of_ne_of_lt
    {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i))
    (remaining count : ℕ)
    (htotal : count + remaining = k)
    (acc : FinPrefix X count)
    (outcome : (i : Fin k) → X i)
    (i : Fin k) (hi : i.val < count)
    (hne : outcome i ≠ acc i hi) :
    finPiFrom laws remaining count htotal acc outcome = 0 := by
  by_contra hnonzero
  have hsupport :
      outcome ∈
        (finPiFrom laws remaining count htotal acc).support :=
    (PMF.mem_support_iff
      (finPiFrom laws remaining count htotal acc)
      outcome).mpr hnonzero
  exact
    hne
      (finPiFrom_apply_eq_of_mem_support_of_lt
        laws remaining count htotal acc outcome
        hsupport i hi)

/-- Point mass of a prefix-completion product at the tuple whose supplied
prefix it extends.

The right-hand side is the ordinary finite product of the remaining
coordinate masses.  This theorem exposes the independence hidden by the
operational accumulator definition. -/
theorem finPiFrom_ofTuple_apply
    {k : ℕ} {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i))
    (outcome : (i : Fin k) → X i) :
    ∀ (remaining count : ℕ)
      (htotal : count + remaining = k),
      finPiFrom laws remaining count htotal
          (FinPrefix.ofTuple outcome count)
          outcome =
        ∏ n ∈ Finset.Ico count k,
          if hn : n < k then
            laws ⟨n, hn⟩ (outcome ⟨n, hn⟩)
          else 1 := by
  intro remaining
  induction remaining with
  | zero =>
      intro count htotal
      have hcount : count = k := by omega
      subst count
      simp [finPiFrom]
  | succ remaining ih =>
      intro count htotal
      have hcount : count < k := by omega
      let index : Fin k := ⟨count, hcount⟩
      rw [finPiFrom, PMF.bind_apply]
      calc
        (∑' value,
            laws index value *
              finPiFrom laws remaining (count + 1)
                (by omega)
                ((FinPrefix.ofTuple outcome count).snoc
                  hcount value)
                outcome) =
            laws index (outcome index) *
              finPiFrom laws remaining (count + 1)
                (by omega)
                (FinPrefix.ofTuple outcome (count + 1))
                outcome := by
          rw [tsum_eq_single (outcome index)]
          · rw [FinPrefix.snoc_ofTuple]
          · intro value hvalue
            have hprefix :
                outcome index ≠
                  ((FinPrefix.ofTuple outcome count).snoc
                    hcount value)
                    index (by simp [index]) := by
              simp only [FinPrefix.snoc]
              simp [index]
              exact Ne.symm hvalue
            rw [finPiFrom_apply_eq_zero_of_ne_of_lt
              laws remaining (count + 1) (by omega)
              ((FinPrefix.ofTuple outcome count).snoc
                hcount value)
              outcome index
              (by simp [index])
              hprefix]
            simp
        _ = laws index (outcome index) *
              ∏ n ∈ Finset.Ico (count + 1) k,
                if hn : n < k then
                  laws ⟨n, hn⟩ (outcome ⟨n, hn⟩)
                else 1 := by
          rw [ih (count + 1) (by omega)]
        _ = ∏ n ∈ Finset.Ico count k,
              if hn : n < k then
                laws ⟨n, hn⟩ (outcome ⟨n, hn⟩)
              else 1 := by
          rw [Finset.prod_eq_prod_Ico_succ_bot
            hcount]
          simp [index, hcount]

/-- Point mass of a finite dependent product is the product of its
coordinate point masses. -/
theorem finPi_apply
    (k : ℕ) {X : Fin k → Type uα}
    (laws : (i : Fin k) → PMF (X i))
    (outcome : (i : Fin k) → X i) :
    finPi k laws outcome =
      ∏ i : Fin k, laws i (outcome i) := by
  unfold finPi
  have hprefix :
      (FinPrefix.empty (X := X)) =
        FinPrefix.ofTuple outcome 0 := by
    funext i hi
    exact (Nat.not_lt_zero i.val hi).elim
  rw [hprefix, finPiFrom_ofTuple_apply]
  rw [Nat.Ico_zero_eq_range]
  simpa only using
    (Finset.prod_fin_eq_prod_range
      (fun i : Fin k => laws i (outcome i))).symm

/-- Point mass of an arbitrary-finite dependent product is the product of
its coordinate point masses.  In particular, this characterization is
independent of the enumeration used by `fintypePi`. -/
theorem fintypePi_apply
    {ι : Type*} [Fintype ι]
    {X : ι → Type uα}
    (laws : (i : ι) → PMF (X i))
    (outcome : (i : ι) → X i) :
    fintypePi laws outcome =
      ∏ i : ι, laws i (outcome i) := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  let reindex :
      ((j : Fin (Fintype.card ι)) → X (e j)) ≃
        ((i : ι) → X i) :=
    e.piCongr fun _ => Equiv.refl _
  change
    ((finPi (Fintype.card ι)
      (fun j => laws (e j))).map reindex) outcome =
        ∏ i : ι, laws i (outcome i)
  rw [map_equiv_apply, finPi_apply]
  calc
    (∏ j : Fin (Fintype.card ι),
        laws (e j) (reindex.symm outcome j)) =
        ∏ j : Fin (Fintype.card ι),
          laws (e j) (outcome (e j)) := by
      apply Finset.prod_congr rfl
      intro j _
      congr 2
    _ = ∏ i : ι, laws i (outcome i) :=
      Fintype.prod_equiv e
        (fun j => laws (e j) (outcome (e j)))
        (fun i => laws i (outcome i))
        (fun _ => rfl)

/-- Independent product of two PMFs, sampling the left component first. -/
noncomputable def independentPair
    {α : Type uα} {β : Type uβ}
    (left : PMF α) (right : PMF β) :
    PMF (α × β) :=
  left.bind fun a =>
    right.map (Prod.mk a)

/-- Point masses of an independent pair multiply. -/
theorem independentPair_apply
    {α : Type uα} {β : Type uβ}
    (left : PMF α) (right : PMF β)
    (outcome : α × β) :
    independentPair left right outcome =
      left outcome.1 * right outcome.2 := by
  rw [independentPair, PMF.bind_apply,
    tsum_eq_single outcome.1]
  · rw [PMF.map_apply,
      tsum_eq_single outcome.2]
    · simp
    · intro b hb
      have hpair : outcome ≠ (outcome.1, b) := by
        intro heq
        apply hb
        exact (congrArg Prod.snd heq).symm
      simp [hpair]
  · intro a ha
    have hmap :
        (right.map (Prod.mk a)) outcome = 0 := by
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro b
      have hpair : outcome ≠ (a, b) := by
        intro heq
        apply ha
        exact (congrArg Prod.fst heq).symm
      simp [hpair]
    simp [hmap]

/-- A finite independent dependent product splits exactly into any selected
coordinate and the independent product of all remaining coordinates.

This is the one-query deferred-sampling law: the selected coordinate can be
drawn now, leaving a fresh product law on the complement. -/
theorem fintypePi_map_piSplitAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type uα}
    (laws : (i : ι) → PMF (X i))
    (selected : ι) :
    (fintypePi laws).map
        (Equiv.piSplitAt selected X) =
      independentPair
        (laws selected)
        (fintypePi
          (fun remaining : {i : ι // i ≠ selected} =>
            laws remaining.1)) := by
  ext outcome
  rw [map_equiv_apply, fintypePi_apply,
    independentPair_apply, fintypePi_apply,
    Fintype.prod_eq_mul_prod_subtype_ne]
  have hselected :
      laws selected
          ((Equiv.piSplitAt selected X).symm
            outcome selected) =
        laws selected outcome.1 := by
    congr 2
    simp [Equiv.piSplitAt]
  rw [hselected]
  apply congrArg (fun mass =>
    laws selected outcome.1 * mass)
  apply Finset.prod_congr rfl
  intro remaining _
  congr 2
  simp [Equiv.piSplitAt, remaining.property]

/-- Independent dependent products are invariant under an equivalence of
their finite index types. -/
theorem fintypePi_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ)
    {X : κ → Type uα}
    (laws : (i : κ) → PMF (X i)) :
    (fintypePi (fun i : ι => laws (e i))).map
        (e.piCongr fun _ => Equiv.refl _) =
      fintypePi laws := by
  let reindex :
      ((i : ι) → X (e i)) ≃
        ((j : κ) → X j) :=
    e.piCongr fun _ => Equiv.refl _
  ext outcome
  change
    ((fintypePi
      (fun i : ι => laws (e i))).map reindex)
        outcome =
      fintypePi laws outcome
  rw [map_equiv_apply, fintypePi_apply,
    fintypePi_apply]
  calc
    (∏ i : ι,
        laws (e i) (reindex.symm outcome i)) =
        ∏ i : ι,
          laws (e i) (outcome (e i)) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 2
    _ = ∏ j : κ, laws j (outcome j) :=
      Fintype.prod_equiv e
        (fun i => laws (e i) (outcome (e i)))
        (fun j => laws j (outcome j))
        (fun _ => rfl)

end PMF
