/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

/-!
# 13. Multi-unit DSIC auctions
-/



section

/-!
## Multi-unit DSIC auctions beyond the one-half welfare factor

The resource is value queries. Values and payments are real.

Quantities include zero with `v(0)=0`, as in [Nisan 2014, §§2.2, 3.2.1] and
[Dobzinski–Nisan 2011, §2]. Queries at zero are allowed and charged.

A well-founded adaptive tree is chosen before the profile. Only its interpreter reads
the queried bidder-quantity entry; continuations see the returned value. Local
processing is free in this query model. The same run produces allocation, payments,
and the number of all queries used for both.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.MultiUnitDSIC

/-- Nonnegative normalized real values, nondecreasing in quantity. -/
structure MultiUnitValuation (m : ℕ) where
  val : Fin (m + 1) → ℝ
  nonnegative : ∀ q, 0 ≤ val q
  empty_value : val 0 = 0
  monotone : ∀ q q', q ≤ q' → val q ≤ val q'

/-- Integral allocation whose total quantity does not exceed supply. -/
structure MultiUnitAllocation (I : Type*) [Fintype I] (m : ℕ) where
  quantity : I → Fin (m + 1)
  capacity : (∑ i, (quantity i : ℕ)) ≤ m

/-- The output includes the allocation and every signed payment. -/
structure MultiUnitOutcome (I : Type*) [Fintype I] (m : ℕ) where
  allocation : MultiUnitAllocation I m
  payment : I → ℝ

/-- A query reads one bidder's value for one quantity. -/
structure MultiUnitValueQuery (I : Type*) (m : ℕ) where
  bidder : I
  quantity : Fin (m + 1)

/-- A deterministic adaptive decision tree; only query nodes read private data. -/
inductive MultiUnitValueQueryTree (I : Type*) [Fintype I] (m : ℕ)
  | output (outcome : MultiUnitOutcome I m)
  | query (question : MultiUnitValueQuery I m)
      (next : ℝ → MultiUnitValueQueryTree I m)

/-- One run returns output and query count. Repeated queries read the same fixed
valuation, and output nodes add no query. -/
def MultiUnitValueQueryTree.run
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m)
    (reports : I → MultiUnitValuation m) : MultiUnitOutcome I m × ℕ :=
  match tree with
  | .output outcome => (outcome, 0)
  | .query question next =>
      let result := (next ((reports question.bidder).val question.quantity)).run reports
      (result.1, result.2 + 1)

/-- Actual query count on an admissible profile. -/
def MultiUnitValueQueryTree.queryCount
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m)
    (reports : I → MultiUnitValuation m) : ℕ :=
  (tree.run reports).2

/-- A bound `C(1+n+floor(log₂(m+1)))^d` on every profile. The final statement chooses
`C,d` before every size and profile. -/
def MultiUnitValueQueryTree.UsesValueQueryBound
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m) (coefficient exponent : ℕ) : Prop :=
  ResourceBoundInSizes coefficient exponent
    (fun _reports : I → MultiUnitValuation m =>
      [Fintype.card I, Nat.log2 (m + 1)])
    tree.queryCount

noncomputable section

/-- Quasilinear DSIC uses true values to evaluate both truthful and deviating outcomes. -/
def MultiUnitValueQueryTree.IsDSIC
    {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m) : Prop :=
  ∀ (reports : I → MultiUnitValuation m) (i : I) (fake : MultiUnitValuation m),
    let truthful := (tree.run reports).1
    let deviating := (tree.run (Function.update reports i fake)).1
    (reports i).val (truthful.allocation.quantity i) - truthful.payment i ≥
      (reports i).val (deviating.allocation.quantity i) - deviating.payment i

/-- Welfare excludes payments, which are transfers. -/
def multiUnitWelfare
    {I : Type*} [Fintype I] {m : ℕ}
    (reports : I → MultiUnitValuation m) (allocation : MultiUnitAllocation I m) : ℝ :=
  ∑ i, (reports i).val (allocation.quantity i)

/-- Comparison against every feasible allocation equals the `α·OPT` guarantee for positive
`α`; the feasible allocation set is finite and nonempty. -/
def MultiUnitValueQueryTree.AchievesFactor
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m) (α : ℝ) : Prop :=
  ∀ (reports : I → MultiUnitValuation m) (alternative : MultiUnitAllocation I m),
    α * multiUnitWelfare reports alternative ≤
      multiUnitWelfare reports (tree.run reports).1.allocation

/-- One factor above one-half and one polynomial query bound work for every positive size.
Each size-dependent tree is fixed before the valuation profile. -/
def MultiUnitDSICBetterThanHalfStatement : Prop :=
  ∃ α : ℝ, (1 / 2 : ℝ) < α ∧
    ∃ coefficient exponent : ℕ,
      ∀ n m : ℕ, 0 < n → 0 < m →
        ∃ tree : MultiUnitValueQueryTree (Fin n) m,
          tree.UsesValueQueryBound coefficient exponent ∧
          tree.IsDSIC ∧ tree.AchievesFactor α

end

end EconCSLib.OpenProblem.New.EconCSBench.MultiUnitDSIC

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MultiUnitDSIC

/-- A uniform improvement above one half using polynomially many value queries. -/
theorem multiUnitDSIC :
    answer(sorry) ↔ MultiUnitDSICBetterThanHalfStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.MultiUnitDSIC
