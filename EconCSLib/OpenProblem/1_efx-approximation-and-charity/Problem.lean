/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.EFXApproximationCharity

open SocialChoice.FairDivision.Indivisible

/-- Convert bundle valuations on `M` to the library's raw valuation interface;
bundles are intersected with `M` so the function is total. -/
def toIndivisibleValuation
    {N G : Type*} [DecidableEq G] (M : Finset G)
    (v : N → BundleValuation M) : Valuation N G where
  val i S := (v i).val ⟨S ∩ M, Finset.inter_subset_right⟩

/-- Universal `α`-EFX guarantee for monotone subadditive goods valuations. -/
def SubadditiveGoodsGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (α : ℝ) : Prop :=
  ∀ v : N → SubadditiveBundleValuation M,
    ∃ A : Allocation N G,
      IsAllocation M A ∧
        IsAlphaEFXGoods α
          (toIndivisibleValuation M fun i => (v i).toBundleValuation) A

/-- Universal `α`-EFX guarantee for monotone submodular goods valuations. -/
def SubmodularGoodsGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (α : ℝ) : Prop :=
  ∀ v : N → SubmodularBundleValuation M,
    ∃ A : Allocation N G,
      IsAllocation M A ∧
        IsAlphaEFXGoods α
          (toIndivisibleValuation M fun i => (v i).toBundleValuation) A

/-- `α` is the supremum of the universally guaranteed goods approximation
factors.  The supremum need not itself be attained: every factor strictly
below `α` in `[0,1]` must be guaranteed, while every factor strictly above
`α` in `[0,1]` must be impossible as a universal guarantee. -/
def IsTightGoodsFactor (guarantee : ℝ → Prop) (α : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧
    (∀ β : ℝ, 0 ≤ β → β < α → guarantee β) ∧
    ∀ β : ℝ, α < β → β ≤ 1 → ¬ guarantee β

/-- Uniform goods guarantee across all finite nonempty agent sets and all
finite ground sets. -/
def UniversalSubadditiveGoodsGuarantee (α : ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubadditiveGoodsGuarantee (N := N) M α

/-- Uniform submodular-goods guarantee. -/
def UniversalSubmodularGoodsGuarantee (α : ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubmodularGoodsGuarantee (N := N) M α

/-- Exact EFX for submodular goods with at most `k` charity items. -/
def SubmodularGoodsCharityGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (k : ℕ) : Prop :=
  ∃ mechanism :
      (N → SubmodularBundleValuation M) → Allocation N G,
    ∀ v : N → SubmodularBundleValuation M,
      let A := mechanism v
      IsPartialIndivisibleAllocation M A ∧
      (charity M A).card ≤ k ∧
      IsAlphaEFXGoods 1
        (toIndivisibleValuation M fun i => (v i).toBundleValuation) A

/-- A charity bound depending only on the number of agents, uniformly over
all finite item sets. -/
def UniversalSubmodularGoodsCharityGuarantee (bound : ℕ → ℕ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubmodularGoodsCharityGuarantee (N := N) M (bound (Fintype.card N))

/-- A pointwise-minimal uniform charity-bound function for submodular goods. -/
def IsMinimumGoodsCharityBound (bound : ℕ → ℕ) : Prop :=
  UniversalSubmodularGoodsCharityGuarantee bound ∧
    ∀ other, UniversalSubmodularGoodsCharityGuarantee other →
      ∀ n, bound n ≤ other n

/-- Universal standard `α`-EFX guarantee for monotone subadditive chore costs,
where `α ≥ 1` and smaller factors are stronger. -/
def SubadditiveChoresGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (α : ℝ) : Prop :=
  ∀ cost : N → SubadditiveBundleValuation M,
    ∃ A : Allocation N G,
      IsAllocation M A ∧
        IsAlphaEFXChores α
          (toIndivisibleValuation M fun i => (cost i).toBundleValuation) A

/-- Universal standard `α`-EFX guarantee for monotone submodular chore costs,
where `α ≥ 1` and smaller factors are stronger. -/
def SubmodularChoresGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (α : ℝ) : Prop :=
  ∀ cost : N → SubmodularBundleValuation M,
    ∃ A : Allocation N G,
      IsAllocation M A ∧
        IsAlphaEFXChores α
          (toIndivisibleValuation M fun i => (cost i).toBundleValuation) A

/-- Uniform subadditive-chore guarantee. -/
def UniversalSubadditiveChoresGuarantee (α : ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubadditiveChoresGuarantee (N := N) M α

/-- Uniform submodular-chore guarantee. -/
def UniversalSubmodularChoresGuarantee (α : ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubmodularChoresGuarantee (N := N) M α

/-- `α` is the infimum of the universally guaranteed standard chore
approximation factors.  Exact EFX corresponds to `α = 1`.  The infimum need
not itself be attained: every strictly weaker factor above `α` must be
guaranteed, while no strictly stronger factor in `[1, α)` may be universally
guaranteed. -/
def IsTightChoresFactor (guarantee : ℝ → Prop) (α : ℝ) : Prop :=
  1 ≤ α ∧
    (∀ β : ℝ, α < β → guarantee β) ∧
    ∀ β : ℝ, 1 ≤ β → β < α → ¬ guarantee β

/-- Exact submodular-chore EFX with at most `k` unallocated chores. -/
def SubmodularChoresCharityGuarantee
    {N G : Type*} [Fintype N] [DecidableEq G]
    (M : Finset G) (k : ℕ) : Prop :=
  ∃ mechanism :
      (N → SubmodularBundleValuation M) → Allocation N G,
    ∀ cost : N → SubmodularBundleValuation M,
      let A := mechanism cost
      IsPartialIndivisibleAllocation M A ∧
      (charity M A).card ≤ k ∧
      IsAlphaEFXChores 1
        (toIndivisibleValuation M fun i => (cost i).toBundleValuation) A

/-- Uniform exact-EFX charity bound for submodular chores. -/
def UniversalSubmodularChoresCharityGuarantee (bound : ℕ → ℕ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G] (M : Finset G),
    SubmodularChoresCharityGuarantee (N := N) M (bound (Fintype.card N))

/-- Pointwise-minimal uniform charity-bound function for submodular chores. -/
def IsMinimumChoresCharityBound (bound : ℕ → ℕ) : Prop :=
  UniversalSubmodularChoresCharityGuarantee bound ∧
    ∀ other, UniversalSubmodularChoresCharityGuarantee other →
      ∀ n, bound n ≤ other n

/-- The six numerical/function-valued answers requested by the Markdown. Goods
factors lie in `[0,1]` and are maximized; standard chore factors lie in
`[1,∞)` and are minimized. Charity bounds depend on the number of agents.

A mathematically informative solution is expected to identify these factors
and bounds explicitly.  Reusing the defining `sSup`, `sInf`, or pointwise
minimum as the answer is formally well-typed and extensionally correct, but
merely restates what an optimum means and is not regarded as resolving the
research problem.  As with every use of `answer`, this explicitness condition
is enforced by human review rather than by restricting the mathematical answer
types. -/
structure EFXApproximationCharityAndChoresAnswer where
  subadditiveGoodsFactor : ℝ
  submodularGoodsFactor : ℝ
  submodularGoodsCharityBound : ℕ → ℕ
  subadditiveChoresFactor : ℝ
  submodularChoresFactor : ℝ
  submodularChoresCharityBound : ℕ → ℕ

/-- A proposed answer is correct exactly when all four approximation factors
and both charity-bound functions are optimal for their respective universal
guarantees. -/
def IsCorrectEFXApproximationCharityAndChoresAnswer
    (result : EFXApproximationCharityAndChoresAnswer) : Prop :=
  IsTightGoodsFactor UniversalSubadditiveGoodsGuarantee
      result.subadditiveGoodsFactor ∧
  IsTightGoodsFactor UniversalSubmodularGoodsGuarantee
      result.submodularGoodsFactor ∧
  IsMinimumGoodsCharityBound result.submodularGoodsCharityBound ∧
  IsTightChoresFactor UniversalSubadditiveChoresGuarantee
      result.subadditiveChoresFactor ∧
  IsTightChoresFactor UniversalSubmodularChoresGuarantee
      result.submodularChoresFactor ∧
  IsMinimumChoresCharityBound result.submodularChoresCharityBound

/-- Open-problem statement: there is a tuple answering all six quantitative
questions in the Markdown. -/
def EFXApproximationCharityAndChoresStatement : Prop :=
  ∃ result : EFXApproximationCharityAndChoresAnswer,
    IsCorrectEFXApproximationCharityAndChoresAnswer result

/-- Typed open-problem answer: a submission must supply the six requested
numbers/functions themselves, not merely repeat the existential statement. -/
theorem efxApproximationCharityAndChores :
    IsCorrectEFXApproximationCharityAndChoresAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.EFXApproximationCharity
