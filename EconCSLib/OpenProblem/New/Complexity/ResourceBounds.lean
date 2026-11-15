/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic



section

/-!
# Resource bounds

Polynomial bounds for resource counters, including query and communication costs.
Uniform variants quantify over all admissible execution choices.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench
universe u v w

/-- A fixed polynomial bound. Choose the coefficient and exponent before the instance
dimensions when expressing a uniform algorithm-family bound. This counts the stated
resource only; it does not certify arbitrary Lean runtime. -/
def ResourceBound
    {Input : Type u} (coefficient exponent : ℕ)
    (sizeOf : Input → ℕ) (cost : Input → ℕ) : Prop :=
  ∀ input,
    cost input ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size form of `ResourceBound`. The size parameters are aggregated by
addition, so one fixed pair of constants bounds one polynomial in all advertised
parameters. -/
def ResourceBoundInSizes
    {Input : Type u} (coefficient exponent : ℕ)
    (sizes : Input → List ℕ) (cost : Input → ℕ) : Prop :=
  ResourceBound coefficient exponent
    (fun input => (sizes input).sum) cost

/-- One specified worst-case polynomial bound, uniform over every seed, legal oracle,
tie-breaking rule, transcript, or other execution choice. -/
def UniformResourceBound
    {Input : Type u} {Choice : Input → Type v}
    (coefficient exponent : ℕ) (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∀ input choice,
    cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size version of `UniformResourceBound`. -/
def UniformResourceBoundInSizes
    {Input : Type u} {Choice : Input → Type v}
    (coefficient exponent : ℕ) (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∀ input choice,
    cost input choice ≤
      coefficient *
        ((sizes input).sum + 1) ^ exponent

/-- Promise-restricted uniform bound with fixed coefficient and exponent. -/
def UniformResourceBoundOn
    {Input : Type u} {Choice : Input → Type v}
    (coefficient exponent : ℕ)
    (valid : (input : Input) → Choice input → Prop)
    (sizeOf : Input → ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∀ input choice, valid input choice →
    cost input choice ≤ coefficient * (sizeOf input + 1) ^ exponent

/-- Multivariate-size promise-restricted uniform bound with fixed constants. -/
def UniformResourceBoundInSizesOn
    {Input : Type u} {Choice : Input → Type v}
    (coefficient exponent : ℕ)
    (valid : (input : Input) → Choice input → Prop)
    (sizes : Input → List ℕ)
    (cost : (input : Input) → Choice input → ℕ) : Prop :=
  ∀ input choice, valid input choice →
    cost input choice ≤
      coefficient *
        ((sizes input).sum + 1) ^ exponent

end EconCSLib.OpenProblem.New.EconCSBench

end
