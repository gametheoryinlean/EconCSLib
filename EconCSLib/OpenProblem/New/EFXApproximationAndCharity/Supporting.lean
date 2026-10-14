/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.EFXApproximationAndCharity.Problem

/-!
# EFXApproximationAndCharity: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## EFX approximation, charity, and chores

Native valuations and allocations are reused. Profiles are nonnegative and monotone on
finite goods; the literal problem-statement domain does not impose normalization on
nonadditive classes. Additivity itself forces the empty value to zero. There is at
least one agent, but zero goods are allowed.

Goods factors lie in `[0,1]`, with larger factors stronger. Chores factors are at
least one, with smaller factors stronger [Zhou–Wu 2022, Definition 1]. No finite
universal chores factor is assumed to exist.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

open SocialChoice.FairDivision.Indivisible

/-- Pointwise optimal worst-case charity for each positive `n` and each `m`. -/
def IsMinimumCharityBound (resource : ResourceKind)
    (kind : FunctionClass)
    (bound : ℕ → ℕ → ℕ) : Prop :=
  ∀ n m : ℕ, 0 < n →
    CharityGuarantee resource kind n m (bound n m) ∧
      ∀ smaller : ℕ, smaller < bound n m →
        ¬ CharityGuarantee resource kind n m smaller

end EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

end


section

/-!
## Resetting only the empty bundle

This normalization preserves all four valuation classes and transfers the specified
EFX guarantees back to the original profile.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity
namespace EmptyNormalization
open SocialChoice.FairDivision.Indivisible

/-- Preserve every nonempty bundle value and set only the empty value to zero. -/
def resetEmpty {n m : ℕ} (v : Valuation (Fin n) (Fin m)) :
    Valuation (Fin n) (Fin m) where
  val i S := if S = ∅ then 0 else v.val i S

/-- Normalization is an additional domain condition. -/
def NormalizedProfile {n m : ℕ} (v : Valuation (Fin n) (Fin m)) : Prop :=
  ∀ i, v.val i ∅ = 0

@[simp] theorem resetEmpty_empty {n m : ℕ} (v : Valuation (Fin n) (Fin m)) (i : Fin n) :
    (resetEmpty v).val i ∅ = 0 := by simp [resetEmpty]

theorem resetEmpty_normalized {n m : ℕ} (v : Valuation (Fin n) (Fin m)) :
    NormalizedProfile (resetEmpty v) := resetEmpty_empty v

theorem resetEmpty_nonempty {n m : ℕ} (v : Valuation (Fin n) (Fin m)) (i : Fin n)
    (S : Finset (Fin m)) (nonempty : S ≠ ∅) : (resetEmpty v).val i S = v.val i S := by
  simp [resetEmpty, nonempty]

/-- Resetting the empty value preserves admissibility, including subadditivity. -/
theorem resetEmpty_admissible {n m : ℕ} {kind : FunctionClass}
    {v : Valuation (Fin n) (Fin m)} (admissible : AdmissibleProfile kind v) :
    AdmissibleProfile kind (resetEmpty v) := by
  have nonnegative : ∀ i S, 0 ≤ (resetEmpty v).val i S := by
    intro i S
    by_cases hs : S = ∅
    · simp [resetEmpty, hs]
    · simpa [resetEmpty, hs] using admissible.1 i S
  refine ⟨nonnegative, ?_, ?_⟩
  · intro i S T subset
    by_cases hs : S = ∅
    · simpa [hs] using nonnegative i T
    · have ht : T ≠ ∅ := by
        intro ht
        apply hs
        simpa [ht] using subset
      simpa [resetEmpty, hs, ht] using admissible.2.1 i S T subset
  · intro i
    cases kind with
    | generalMonotone => trivial
    | additive =>
        intro S
        by_cases hs : S = ∅
        · simp [hs]
        · simpa [resetEmpty, hs] using admissible.2.2 i S
    | subadditive =>
        intro S T
        by_cases hs : S = ∅
        · simp [hs]
        by_cases ht : T = ∅
        · simp [ht]
        have hu : S ∪ T ≠ ∅ := fun h => hs (Finset.union_eq_empty.mp h).1
        simpa [resetEmpty, hs, ht, hu] using admissible.2.2 i S T
    | submodular =>
        intro S T
        by_cases hs : S = ∅
        · simp [hs]
        by_cases ht : T = ∅
        · simp [ht]
        have hu : S ∪ T ≠ ∅ := fun h => hs (Finset.union_eq_empty.mp h).1
        by_cases hi : S ∩ T = ∅
        · have bound := admissible.2.2 i S T
          rw [hi] at bound
          have hn := admissible.1 i ∅
          simp only [resetEmpty, if_neg hs, if_neg ht, if_neg hu, if_pos hi, add_zero]
          linarith
        · simpa [resetEmpty, hs, ht, hu, hi] using admissible.2.2 i S T

/-- Goods EFX for the reset profile implies the same guarantee for the original. -/
theorem goods_transfer {n m : ℕ} {kind : FunctionClass}
    {v : Valuation (Fin n) (Fin m)} (admissible : AdmissibleProfile kind v)
    {factor : ℝ} (factor_le_one : factor ≤ 1)
    {A : Allocation (Fin n) (Fin m)}
    (fair : ApproximateEFX .goods factor (resetEmpty v) A) :
    ApproximateEFX .goods factor v A := by
  intro i j distinct g member
  have h := fair i j distinct g member
  by_cases hr : A j \ {g} = ∅
  · rw [hr]
    calc
      factor * v.val i ∅ ≤ 1 * v.val i ∅ :=
        mul_le_mul_of_nonneg_right factor_le_one (admissible.1 i ∅)
      _ ≤ v.val i (A i) := by simpa using admissible.2.1 i ∅ (A i) (Finset.empty_subset _)
  · by_cases hi : A i = ∅
    · simp only [resetEmpty_nonempty v i _ hr, hi, resetEmpty_empty] at h
      exact h.trans (admissible.1 i (A i))
    · simpa only [resetEmpty_nonempty v i _ hr, resetEmpty_nonempty v i _ hi] using h

/-- Chores EFX for the reset profile implies the same guarantee for the original. -/
theorem chores_transfer {n m : ℕ} {kind : FunctionClass}
    {v : Valuation (Fin n) (Fin m)} (admissible : AdmissibleProfile kind v)
    {factor : ℝ} (one_le_factor : 1 ≤ factor)
    {A : Allocation (Fin n) (Fin m)}
    (fair : ApproximateEFX .chores factor (resetEmpty v) A) :
    ApproximateEFX .chores factor v A := by
  intro i j distinct g member
  have h := fair i j distinct g member
  by_cases hr : A i \ {g} = ∅
  · rw [hr]
    calc
      v.val i ∅ ≤ v.val i (A j) := admissible.2.1 i ∅ (A j) (Finset.empty_subset _)
      _ ≤ factor * v.val i (A j) := by
        simpa using mul_le_mul_of_nonneg_right one_le_factor (admissible.1 i (A j))
  · by_cases hj : A j = ∅
    · simp only [resetEmpty_nonempty v i _ hr, hj, resetEmpty_empty, mul_zero] at h
      exact h.trans (mul_nonneg (le_trans zero_le_one one_le_factor) (admissible.1 i (A j)))
    · simpa only [resetEmpty_nonempty v i _ hr, resetEmpty_nonempty v i _ hj] using h

/-- The normalized complete-allocation question, with the same output predicate. -/
def NormalizedUniversalApproximationGuarantee (resource : ResourceKind)
    (kind : FunctionClass) (factor : ℝ) : Prop :=
  ∀ n m : ℕ, 0 < n → ∀ v : Valuation (Fin n) (Fin m),
    AdmissibleProfile kind v → NormalizedProfile v →
      ∃ A : Allocation (Fin n) (Fin m),
        IsAllocation (Finset.univ : Finset (Fin m)) A ∧
        ApproximateEFX resource factor v A

/-- The usual goods factors have identical universal guarantees on both domains. -/
theorem goods_universal_iff (kind : FunctionClass) {factor : ℝ}
    (factor_le_one : factor ≤ 1) :
    NormalizedUniversalApproximationGuarantee .goods kind factor ↔
      UniversalApproximationGuarantee .goods kind factor := by
  constructor
  · intro holds n m hn v admissible
    obtain ⟨A, feasible, fair⟩ := holds n m hn (resetEmpty v)
      (resetEmpty_admissible admissible) (resetEmpty_normalized v)
    exact ⟨A, feasible, goods_transfer admissible factor_le_one fair⟩
  · intro holds n m hn v admissible _
    exact holds n m hn v admissible

/-- The usual chores factors have identical universal guarantees on both domains. -/
theorem chores_universal_iff (kind : FunctionClass) {factor : ℝ}
    (one_le_factor : 1 ≤ factor) :
    NormalizedUniversalApproximationGuarantee .chores kind factor ↔
      UniversalApproximationGuarantee .chores kind factor := by
  constructor
  · intro holds n m hn v admissible
    obtain ⟨A, feasible, fair⟩ := holds n m hn (resetEmpty v)
      (resetEmpty_admissible admissible) (resetEmpty_normalized v)
    exact ⟨A, feasible, chores_transfer admissible one_le_factor fair⟩
  · intro holds n m hn v admissible _
    exact holds n m hn v admissible

/-- Restrict only the promise of the original charity-rule question. -/
def NormalizedCharityGuarantee (resource : ResourceKind) (kind : FunctionClass)
    (n m k : ℕ) : Prop :=
  ∃ rule : Valuation (Fin n) (Fin m) → Allocation (Fin n) (Fin m),
    ∀ v : Valuation (Fin n) (Fin m), AdmissibleProfile kind v → NormalizedProfile v →
      IsPartialIndivisibleAllocation (Finset.univ : Finset (Fin m)) (rule v) ∧
      (charity (Finset.univ : Finset (Fin m)) (rule v)).card ≤ k ∧
      ApproximateEFX resource 1 v (rule v)

/-- Compose the normalized rule with reset; allocation and charity count are unchanged. -/
theorem charity_iff (resource : ResourceKind) (kind : FunctionClass) (n m k : ℕ) :
    NormalizedCharityGuarantee resource kind n m k ↔ CharityGuarantee resource kind n m k := by
  constructor
  · rintro ⟨rule, holds⟩
    refine ⟨fun v => rule (resetEmpty v), fun v admissible => ?_⟩
    obtain ⟨feasible, bound, fair⟩ := holds (resetEmpty v)
      (resetEmpty_admissible admissible) (resetEmpty_normalized v)
    refine ⟨feasible, bound, ?_⟩
    cases resource with
    | goods => exact goods_transfer admissible le_rfl fair
    | chores => exact chores_transfer admissible le_rfl fair
  · rintro ⟨rule, holds⟩
    exact ⟨rule, fun v admissible _ => holds v admissible⟩

end EmptyNormalization
end EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

end


section

/-!
## Quantitative EFX-answer specifications

Candidate numerical factors and charity bounds are explicit parameters: merely
asserting an unnamed optimum or copying its defining supremum is not an answer. The
submodular, subadditive, charity, and chores directions can be addressed
independently. A chores question explicitly selects its cost class.

Pointwise `(n,m)` charity and uniform `n`-only charity are distinct targets.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

/-- Joint compatibility form of the two optimal goods-factor questions. -/
def GoodsApproximationQuestion (submodularFactor subadditiveFactor : ℝ) : Prop :=
  IsBestGoodsFactor
      (UniversalApproximationGuarantee .goods .submodular)
      submodularFactor ∧
    IsBestGoodsFactor
      (UniversalApproximationGuarantee .goods .subadditive)
      subadditiveFactor

/-- Goal (2): a sharp pointwise charity bound for submodular goods. -/
def SubmodularGoodsCharityQuestion (bound : ℕ → ℕ → ℕ) : Prop :=
  IsMinimumCharityBound .goods .submodular bound

/-- Goal (3): optimal pointwise chores charity for the selected cost class. -/
def ChoresCharityQuestion (kind : FunctionClass) (bound : ℕ → ℕ → ℕ) : Prop :=
  IsMinimumCharityBound .chores kind bound

end EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

end
