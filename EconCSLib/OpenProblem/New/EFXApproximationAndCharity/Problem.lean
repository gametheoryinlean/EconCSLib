/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.SharedConcepts.All
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer

/-!
# 06. EFX approximation, charity, and chores
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

/-- Function classes; nonnegativity and monotonicity are imposed separately. -/
inductive FunctionClass
  | generalMonotone
  | additive
  | submodular
  | subadditive
  deriving DecidableEq

/-- Goods confer value; chores incur cost. -/
inductive ResourceKind
  | goods
  | chores
  deriving DecidableEq

/-- The selected structural property on all bundles of `Fin m`. -/
def InFunctionClass {m : ℕ} (kind : FunctionClass)
    (v : Finset (Fin m) → ℝ) : Prop :=
  match kind with
  | .generalMonotone => True
  | .additive => ∀ S, v S = S.sum (fun g => v {g})
  | .submodular => ∀ S T, v (S ∪ T) + v (S ∩ T) ≤ v S + v T
  | .subadditive => ∀ S T, v (S ∪ T) ≤ v S + v T

/-- Nonnegative monotone valuations or costs in the selected class, without an implicit
normalization or strict-positivity assumption. -/
def AdmissibleProfile {n m : ℕ} (kind : FunctionClass)
    (v : Valuation (Fin n) (Fin m)) : Prop :=
  (∀ i S, 0 ≤ v.val i S) ∧
  (∀ i S T, S ⊆ T → v.val i S ≤ v.val i T) ∧
  ∀ i, InFunctionClass kind (v.val i)

/-- Approximate EFX removes a good from the other bundle or a chore from one's own bundle.
Every item is checked, including zero-value items. -/
def ApproximateEFX {n m : ℕ} (resource : ResourceKind) (factor : ℝ)
    (v : Valuation (Fin n) (Fin m)) (A : Allocation (Fin n) (Fin m)) : Prop :=
  match resource with
  | .goods => IsAlphaEFXGoods factor v A
  | .chores => IsAlphaEFXChores factor v A

/-- A complete-allocation guarantee for every size and admissible profile. -/
def UniversalApproximationGuarantee (resource : ResourceKind)
    (kind : FunctionClass)
    (factor : ℝ) : Prop :=
  ∀ n m : ℕ, 0 < n → ∀ v : Valuation (Fin n) (Fin m),
    AdmissibleProfile kind v →
      ∃ A : Allocation (Fin n) (Fin m),
        IsAllocation (Finset.univ : Finset (Fin m)) A ∧
        ApproximateEFX resource factor v A

/-- An attained optimal goods factor: guaranteed, with every larger valid factor failing
on some instance. This is an existence question. -/
def IsBestGoodsFactor (guarantee : ℝ → Prop) (factor : ℝ) : Prop :=
  0 ≤ factor ∧ factor ≤ 1 ∧ guarantee factor ∧
    ∀ better : ℝ, factor < better → better ≤ 1 → ¬ guarantee better

/-- `some α` is an attained optimal finite chores factor; `none` means no finite factor
works uniformly. -/
def IsBestChoresFactor (guarantee : ℝ → Prop) (factor : Option ℝ) : Prop :=
  match factor with
  | some value =>
      1 ≤ value ∧ guarantee value ∧
        ∀ better : ℝ, 1 ≤ better → better < value → ¬ guarantee better
  | none => ∀ value : ℝ, 1 ≤ value → ¬ guarantee value

/-- A mathematical allocation rule, fixed before the profile, guarantees exact EFX and at
most `k` unallocated items. No efficiency or charity-envy constraint. -/
def CharityGuarantee (resource : ResourceKind)
    (kind : FunctionClass)
    (n m k : ℕ) : Prop :=
  ∃ rule : Valuation (Fin n) (Fin m) → Allocation (Fin n) (Fin m),
    ∀ v : Valuation (Fin n) (Fin m), AdmissibleProfile kind v →
      IsPartialIndivisibleAllocation (Finset.univ : Finset (Fin m)) (rule v) ∧
      (charity (Finset.univ : Finset (Fin m)) (rule v)).card ≤ k ∧
      ApproximateEFX resource 1 v (rule v)

/-- A charity guarantee uniform over every number of goods. -/
def UniformCharityGuarantee (resource : ResourceKind) (kind : FunctionClass)
    (n k : ℕ) : Prop :=
  ∀ m : ℕ, CharityGuarantee resource kind n m k

/-- An optimal `n`-only bound holds for all `m`; any smaller bound fails for at least one
`m`. It need not be pointwise optimal at each `m`. -/
def IsMinimumUniformCharityBound (resource : ResourceKind) (kind : FunctionClass)
    (bound : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n →
    UniformCharityGuarantee resource kind n (bound n) ∧
      ∀ smaller : ℕ, smaller < bound n →
        ¬ UniformCharityGuarantee resource kind n smaller

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

/-- Goal (3): the optimal chores factor for an explicitly selected cost class. -/
def ChoresApproximationQuestion (kind : FunctionClass) (factor : Option ℝ) : Prop :=
  IsBestChoresFactor
    (UniversalApproximationGuarantee .chores kind) factor

/-- Independent submodular branch of Goal (1). -/
def SubmodularGoodsApproximationQuestion (factor : ℝ) : Prop :=
  IsBestGoodsFactor (UniversalApproximationGuarantee .goods .submodular) factor

/-- Independent subadditive branch of Goal (1). -/
def SubadditiveGoodsApproximationQuestion (factor : ℝ) : Prop :=
  IsBestGoodsFactor (UniversalApproximationGuarantee .goods .subadditive) factor

/-- Uniform `n`-only submodular charity; separate from the pointwise question. -/
def UniformSubmodularGoodsCharityQuestion (bound : ℕ → ℕ) : Prop :=
  IsMinimumUniformCharityBound .goods .submodular bound

/-- Uniform `n`-only chores charity for the selected cost class. -/
def UniformChoresCharityQuestion (kind : FunctionClass) (bound : ℕ → ℕ) : Prop :=
  IsMinimumUniformCharityBound .chores kind bound

end EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity

/-- The optimal EFX approximation factor for submodular goods valuations. -/
theorem submodularGoodsFactor :
    SubmodularGoodsApproximationQuestion (answer(sorry)) := by
  sorry

/-- Independent optimal subadditive-goods factor. -/
theorem subadditiveGoodsFactor :
    SubadditiveGoodsApproximationQuestion (answer(sorry)) := by
  sorry

/-- Supply the sharp uniform charity bound as a function of the number of agents. -/
theorem submodularGoodsCharity :
    UniformSubmodularGoodsCharityQuestion (answer(sorry)) := by
  sorry

/-- Independent chores factor for the specified cost class; None means no finite factor. -/
theorem choresFactor (kind : FunctionClass) :
    ChoresApproximationQuestion kind (answer(sorry)) := by
  sorry

/-- Independent uniform chores charity bound. -/
theorem choresCharity (kind : FunctionClass) :
    UniformChoresCharityQuestion kind (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.EFXApproximationCharity
