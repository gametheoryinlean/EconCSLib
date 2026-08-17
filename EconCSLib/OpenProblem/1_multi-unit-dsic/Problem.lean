/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.MultiUnitDSIC

/-- A nonnegative monotone valuation for receiving between zero and `m`
identical units. -/
structure MultiUnitValuation (m : ℕ) where
  /-- Value of every feasible quantity. -/
  val : Fin (m + 1) → ℝ
  /-- Values are nonnegative. -/
  nonnegative : ∀ q, 0 ≤ val q
  /-- Receiving no units has value zero. -/
  empty_value : val 0 = 0
  /-- Values are monotone in quantity. -/
  monotone : ∀ q q', q ≤ q' → val q ≤ val q'

/-- A feasible allocation of at most `m` identical units. -/
structure MultiUnitAllocation (I : Type*) [Fintype I] (m : ℕ) where
  /-- Quantity assigned to each bidder. -/
  quantity : I → Fin (m + 1)
  /-- Total allocated quantity does not exceed supply. -/
  capacity : (∑ i, (quantity i : ℕ)) ≤ m

/-- A deterministic direct multi-unit mechanism. -/
structure MultiUnitMechanism
    (I : Type*) [Fintype I] (m : ℕ) where
  /-- Allocation rule. -/
  allocation : (I → MultiUnitValuation m) → MultiUnitAllocation I m
  /-- Payment rule. -/
  payment : (I → MultiUnitValuation m) → I → ℝ

/-- One value query asks one bidder for the value of one feasible quantity. -/
structure MultiUnitValueQuery (I : Type*) (m : ℕ) where
  bidder : I
  quantity : Fin (m + 1)

/-- Black-box answers to value queries. -/
abbrev MultiUnitValueOracle (I : Type*) (m : ℕ) :=
  MultiUnitValueQuery I m → ℝ

/-- An oracle represents exactly the submitted valuation profile. -/
def IsValidMultiUnitValueOracle
    {I : Type*} {m : ℕ}
    (reports : I → MultiUnitValuation m)
    (oracle : MultiUnitValueOracle I m) : Prop :=
  ∀ query, oracle query = (reports query.bidder).val query.quantity

/-- A finite adaptive value-query program returning an allocation and all
payments. -/
inductive MultiUnitValueQueryTree
    (I : Type*) [Fintype I] (m : ℕ)
  | output (allocation : MultiUnitAllocation I m) (payment : I → ℝ)
  | query (question : MultiUnitValueQuery I m)
      (next : ℝ → MultiUnitValueQueryTree I m)
      (localCost : ℝ → ℕ)

/-- Execute a multi-unit value-query program. -/
def MultiUnitValueQueryTree.run
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m)
    (oracle : MultiUnitValueOracle I m) :
    MultiUnitAllocation I m × (I → ℝ) :=
  match tree with
  | .output allocation payment => (allocation, payment)
  | .query question next _ => (next (oracle question)).run oracle

/-- Actual number of value queries on one oracle-answer path. -/
def MultiUnitValueQueryTree.queryCount
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m)
    (oracle : MultiUnitValueOracle I m) : ℕ :=
  match tree with
  | .output _ _ => 0
  | .query question next _ =>
      1 + (next (oracle question)).queryCount oracle

/-- Unit-cost running time along one path: each oracle call costs one unit and
`localCost answer` accounts for the explicitly annotated local computation
that selects the continuation. -/
def MultiUnitValueQueryTree.timeCost
    {I : Type*} [Fintype I] {m : ℕ}
    (tree : MultiUnitValueQueryTree I m)
    (oracle : MultiUnitValueOracle I m) : ℕ :=
  match tree with
  | .output _ _ => 1
  | .query question next localCost =>
      let answer := oracle question
      1 + localCost answer + (next answer).timeCost oracle

/-- A direct mechanism whose complete outcome can genuinely be implemented
using only value queries. -/
structure ValueQueryMultiUnitMechanism
    (I : Type*) [Fintype I] (m : ℕ)
    extends MultiUnitMechanism I m where
  program : MultiUnitValueQueryTree I m
  implements :
    ∀ reports oracle,
      IsValidMultiUnitValueOracle reports oracle →
        program.run oracle =
          (allocation reports, payment reports)

/-- One fixed polynomial query bound for the concrete adaptive program,
uniformly over every possible oracle-answer path. -/
def ValueQueryMultiUnitMechanism.UsesValueQueryBound
    {I : Type*} [Fintype I] {m : ℕ}
    (mechanism : ValueQueryMultiUnitMechanism I m)
    (coefficient exponent : ℕ) : Prop :=
  ResourceBoundInSizes coefficient exponent
    (fun _oracle : MultiUnitValueOracle I m =>
      [Fintype.card I, Nat.log 2 (m + 1)])
    mechanism.program.queryCount

/-- Dominant-strategy incentive compatibility with quasi-linear utility. -/
def MultiUnitMechanism.IsDSIC
    {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (mechanism : MultiUnitMechanism I m) : Prop :=
  ∀ reports i fake,
    (reports i).val ((mechanism.allocation reports).quantity i) -
        mechanism.payment reports i ≥
      (reports i).val
          ((mechanism.allocation (Function.update reports i fake)).quantity i) -
        mechanism.payment (Function.update reports i fake) i

/-- Welfare of a multi-unit allocation. -/
noncomputable def multiUnitWelfare
    {I : Type*} [Fintype I] {m : ℕ}
    (v : I → MultiUnitValuation m) (A : MultiUnitAllocation I m) : ℝ :=
  ∑ i, (v i).val (A.quantity i)

/-- Offline optimal multi-unit welfare. -/
noncomputable def multiUnitOPT
    {I : Type*} [Fintype I] {m : ℕ}
    (v : I → MultiUnitValuation m) : ℝ :=
  ⨆ A : MultiUnitAllocation I m, multiUnitWelfare v A

/-- Approximation factor of a deterministic multi-unit mechanism. -/
noncomputable def AchievesFactor
    {I : Type*} [Fintype I] {m : ℕ}
    (α : ℝ) (mechanism : MultiUnitMechanism I m) : Prop :=
  ∀ reports,
    α * multiUnitOPT reports ≤
      multiUnitWelfare reports (mechanism.allocation reports)

/-- Open-problem statement: some deterministic DSIC mechanism using
`poly(n,log m)` value queries beats the `1/2` factor. -/
def MultiUnitDSICBetterThanHalfStatement : Prop :=
  ∃ α : ℝ, 1 / 2 < α ∧
    ∃ coefficient exponent : ℕ,
      ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (m : ℕ),
        0 < m →
        ∃ mechanism : ValueQueryMultiUnitMechanism I m,
          mechanism.UsesValueQueryBound coefficient exponent ∧
          mechanism.toMultiUnitMechanism.IsDSIC ∧
          AchievesFactor α mechanism.toMultiUnitMechanism

/-- English version: "Can a deterministic DSIC multi-unit auction using
polynomially many value queries beat the one-half approximation barrier?" -/
theorem multiUnitDSICBetterThanHalf :
    answer(sorry) ↔ MultiUnitDSICBetterThanHalfStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.MultiUnitDSIC
