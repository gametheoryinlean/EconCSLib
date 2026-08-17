/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open scoped unitInterval

namespace EconCSLib.OpenProblem.EconCSBench.EnvyFreeCakeCuttingComplexity

open MeasureTheory
open SocialChoice.FairDivision.Divisible
open Filter

/-- A normalized nonatomic cake-cutting instance on the unit interval. -/
structure CakeInstance (N : Type*) where
  /-- Each agent's value measure. -/
  measure : N → Measure I
  /-- Every measure is a probability measure. -/
  probability : ∀ i, IsProbabilityMeasure (measure i)
  /-- Every measure is nonatomic. -/
  nonatomic : ∀ i, NoAtoms (measure i)

/-- The two Robertson-Webb query forms. -/
inductive RWQuery (N : Type*)
  | cut (agent : N) (left : I) (amount : ℝ)
  | eval (agent : N) (left right : I)

/-- The response type depends on the query form: a cut point or a real value. -/
def RWQuery.Answer {N : Type*} : RWQuery N → Type
  | .cut _ _ _ => I
  | .eval _ _ _ => ℝ

/-- Exact validity of a Robertson-Webb oracle answer for a cake instance. -/
def RWQuery.IsValidAnswer
    {N : Type*} (problem : CakeInstance N) :
    (query : RWQuery N) → query.Answer → Prop
  | .cut agent left amount, right =>
      left ≤ right ∧
        (problem.measure agent (Set.Icc left right)).toReal = amount
  | .eval agent left right, value =>
      left ≤ right ∧
        (problem.measure agent (Set.Icc left right)).toReal = value

/-- An oracle supplies an answer of the correct type to every RW query.  Only
answers encountered along an execution are required to satisfy the valuation. -/
abbrev RWOracle (N : Type*) :=
  (query : RWQuery N) → query.Answer

/-- A finite adaptive Robertson-Webb decision tree. -/
inductive RWQueryTree (N : Type*) [Fintype N]
  | output (allocation : Allocation N I)
  | query (question : RWQuery N)
      (next : question.Answer → RWQueryTree N)

/-- Execute a Robertson-Webb query tree against an oracle. -/
def RWQueryTree.run
    {N : Type*} [Fintype N] (tree : RWQueryTree N)
    (oracle : RWOracle N) : Allocation N I :=
  match tree with
  | .output allocation => allocation
  | .query question next => (next (oracle question)).run oracle

/-- Actual number of Cut/Eval queries on an oracle-answer path. -/
def RWQueryTree.queryCount
    {N : Type*} [Fintype N] (tree : RWQueryTree N)
    (oracle : RWOracle N) : ℕ :=
  match tree with
  | .output _ => 0
  | .query question next =>
      1 + (next (oracle question)).queryCount oracle

/-- Every answer encountered on a run is valid for the supplied valuation
profile. -/
def RWQueryTree.AnswersValid
    {N : Type*} [Fintype N] (problem : CakeInstance N)
    (tree : RWQueryTree N) (oracle : RWOracle N) : Prop :=
  match tree with
  | .output _ => True
  | .query question next =>
      question.IsValidAnswer problem (oracle question) ∧
        (next (oracle question)).AnswersValid problem oracle

/-- A Robertson-Webb protocol is structurally restricted to a finite adaptive
tree of Cut and Eval queries. -/
structure RWProtocol (N : Type*) [Fintype N] where
  /-- The complete adaptive query program. -/
  program : RWQueryTree N

/-- Two cake points lie in the same cell of the interval decomposition induced
by the cut points discovered so far.  Equality with a cut point is tracked
separately, so endpoint ownership can be represented without forcing adjacent
pieces to overlap. -/
def SameRWCell (cutPoints : Set I) (x y : I) : Prop :=
  ∀ c ∈ cutPoints,
    (x < c ↔ y < c) ∧ (x = c ↔ y = c) ∧ (c < x ↔ c < y)

/-- A piece is Robertson--Webb constructible from `cutPoints` when membership
is constant on every cell induced by those finitely generated cut points.  It
is therefore a finite union of trace intervals and selected endpoints, rather
than an arbitrary measurable subset of the cake. -/
def IsRWConstructiblePiece
    (cutPoints : Set I) (piece : Set I) : Prop :=
  ∀ x y, SameRWCell cutPoints x y → (x ∈ piece ↔ y ∈ piece)

/-- Every allocated piece is constructed from the cut points on the execution
path leading to the terminal node. -/
def IsRWConstructibleAllocation
    {N : Type*} (cutPoints : Set I) (allocation : Allocation N I) : Prop :=
  ∀ i, IsRWConstructiblePiece cutPoints (allocation i)

/-- A terminal piece in a discrete RW protocol is a finite union of interval
cells.  Its endpoints may be arbitrary real functions of the preceding
transcript; they need not themselves have been returned by Cut queries. -/
def IsFiniteIntervalPiece (piece : Set I) : Prop :=
  ∃ cutPoints : Set I,
    cutPoints.Finite ∧ IsRWConstructiblePiece cutPoints piece

/-- Every terminal bundle is a finite union of intervals. -/
def IsFiniteIntervalAllocation
    {N : Type*} (allocation : Allocation N I) : Prop :=
  ∀ i, IsFiniteIntervalPiece (allocation i)

/-- A tree solves one cake instance from a set of already known cut points.
Cut queries may start only at a known cut point and extend the trace with their
answer; Eval queries may use only known endpoints.  Every valid answer branch
must remain correct, and every terminal allocation must be RW-constructible,
complete, and envy-free. -/
def RWQueryTree.SolvesFromCutPoints
    {N : Type*} [Fintype N] (problem : CakeInstance N)
    (cutPoints : Set I) (tree : RWQueryTree N) : Prop :=
  match tree with
  | .output allocation =>
      IsRWConstructibleAllocation cutPoints allocation ∧
        IsAllocation allocation ∧
        IsEnvyFree (MeasureValuation problem.measure) allocation
  | .query (.cut agent left amount) next =>
      left ∈ cutPoints ∧
        (∃ right : I,
          (RWQuery.cut agent left amount).IsValidAnswer problem right) ∧
        ∀ right : I,
          (RWQuery.cut agent left amount).IsValidAnswer problem right →
            (next right).SolvesFromCutPoints problem
              (Set.insert right cutPoints)
  | .query (.eval agent left right) next =>
      left ∈ cutPoints ∧ right ∈ cutPoints ∧
        (∃ value : ℝ,
          (RWQuery.eval agent left right).IsValidAnswer problem value) ∧
        ∀ value : ℝ,
          (RWQuery.eval agent left right).IsValidAnswer problem value →
            (next value).SolvesFromCutPoints problem cutPoints

/-- Standard unrestricted Robertson--Webb correctness semantics.  Query
endpoints may be computed from the preceding transcript, and terminal
endpoints need not be Cut answers.  Correctness is semantic: every valid
answer branch must end in a finite-interval, complete, envy-free allocation. -/
def RWQueryTree.SolvesStandard
    {N : Type*} [Fintype N] (problem : CakeInstance N) :
    RWQueryTree N → Prop
  | .output allocation =>
      IsFiniteIntervalAllocation allocation ∧
        IsAllocation allocation ∧
        IsEnvyFree (MeasureValuation problem.measure) allocation
  | .query question next =>
      (∃ answer, question.IsValidAnswer problem answer) ∧
        ∀ answer, question.IsValidAnswer problem answer →
          (next answer).SolvesStandard problem

/-- Correctness in the standard unrestricted RW model. -/
def RWQueryTree.SolvesInstance
    {N : Type*} [Fintype N] (problem : CakeInstance N)
    (tree : RWQueryTree N) : Prop :=
  tree.SolvesStandard problem

/-- A Robertson-Webb protocol solves the problem if its tree solves every
normalized nonatomic valuation profile. -/
def RWProtocol.Solves
    {N : Type*} [Fintype N] (protocol : RWProtocol N) : Prop :=
  ∀ problem : CakeInstance N, protocol.program.SolvesInstance problem

/-- The quantitative answer requested by the Markdown: an achievable upper
bound and a universal lower bound that should close the query-complexity gap. -/
structure EnvyFreeCakeCuttingComplexityAnswer where
  upperBound : ℕ → ℕ
  lowerBound : ℕ → ℕ

/-- A proposed pair of bounds is correct when one family of RW protocols
achieves the upper bound, every correct RW protocol has a valid execution
meeting the lower bound, and the two functions are asymptotically tight. -/
def IsCorrectEnvyFreeCakeCuttingComplexityAnswer
    (result : EnvyFreeCakeCuttingComplexityAnswer) : Prop :=
  (∃ protocols : ∀ n : ℕ, RWProtocol (Fin n),
    (∀ n : ℕ, 2 ≤ n → (protocols n).Solves) ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ problem oracle,
        (protocols n).program.AnswersValid problem oracle →
          (protocols n).program.queryCount oracle ≤ result.upperBound n) ∧
  (∀ n : ℕ, 2 ≤ n →
    ∀ protocol : RWProtocol (Fin n), protocol.Solves →
      ∃ problem, ∃ oracle,
        protocol.program.AnswersValid problem oracle ∧
          result.lowerBound n ≤ protocol.program.queryCount oracle) ∧
  (fun n => (result.upperBound n : ℝ)) =Θ[atTop]
    (fun n => (result.lowerBound n : ℝ))

/-- Open-problem statement: asymptotically matching Robertson--Webb query
bounds can be supplied for complete envy-free cake cutting. -/
def EnvyFreeCakeCuttingComplexityStatement : Prop :=
  ∃ result : EnvyFreeCakeCuttingComplexityAnswer,
    IsCorrectEnvyFreeCakeCuttingComplexityAnswer result

/-- Typed open-problem answer.  A mathematically acceptable replacement must
give explicit asymptotic upper/lower-bound functions; copying their defining
optimum or this correctness predicate is not considered a solution. -/
theorem envyFreeCakeCuttingComplexity :
    IsCorrectEnvyFreeCakeCuttingComplexityAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.EnvyFreeCakeCuttingComplexity
