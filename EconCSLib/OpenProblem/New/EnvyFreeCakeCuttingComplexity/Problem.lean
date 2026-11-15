/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Divisible.Instance
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# 07. Envy-free cake-cutting complexity
-/



section

/-!
## Robertson–Webb envy-free cake-cutting model

Uses native divisible allocations and envy-freeness on the Borel unit interval.
Valuations are nonatomic probability measures; no density assumption is imposed.
Following Procaccia (IJCAI 2009, Section 2), query and output endpoints are
unrestricted reals, failed cuts are charged, and outputs are finite unions of interval
cells. All valid replies must be handled for the same valuation profile. Protocols are
deterministic well-founded query trees. Local computation and output are free; this is
not a Word-RAM running-time model.
-/

open scoped unitInterval

namespace EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

open MeasureTheory
open SocialChoice.FairDivision.Divisible

/-- Nonatomic probability measures on the unit interval, without density assumptions. -/
structure CakeInstance (N : Type*) where
  measure : N → Measure I
  probability : ∀ i, IsProbabilityMeasure (measure i)
  nonatomic : ∀ (i : N) (point : I), measure i {point} = 0

/-- Cut accepts any real amount; Eval accepts an interval with ordered endpoints. -/
inductive RWQuery (N : Type*)
  | cut (agent : N) (left : I) (amount : ℝ)
  | eval (agent : N) (left right : I) (ordered : left ≤ right)

/-- A cut returns a point or a failure report; an evaluation returns a real value. -/
def RWQuery.Answer {N : Type*} : RWQuery N → Type
  | .cut _ _ _ => Option I
  | .eval _ _ _ _ => ℝ

/-- An exact cut point, without a leftmost or rightmost tie-breaking convention. -/
def IsCutPoint {N : Type*} (problem : CakeInstance N)
    (agent : N) (left : I) (amount : ℝ) (right : I) : Prop :=
  left ≤ right ∧ (problem.measure agent (Set.Icc left right)).toReal = amount

/-- Replies must match one fixed instance. Repeated cuts may choose different valid
points. -/
def RWQuery.IsValidAnswer {N : Type*} (problem : CakeInstance N) :
    (question : RWQuery N) → question.Answer → Prop
  | .cut agent left amount, some right =>
      IsCutPoint problem agent left amount right
  | .cut agent left amount, none =>
      ¬ ∃ right, IsCutPoint problem agent left amount right
  | .eval agent left right _, value =>
      (problem.measure agent (Set.Icc left right)).toReal = value

/-- Interval cells distinguish each endpoint from its two adjacent open intervals. -/
def SameIntervalCell (endpoints : Set I) (x y : I) : Prop :=
  ∀ c ∈ endpoints,
    (x < c ↔ y < c) ∧ (x = c ↔ y = c) ∧ (c < x ↔ c < y)

/-- Finite unions of interval cells, allowing disconnected pieces, empty pieces, and real
endpoints. -/
def IsFiniteIntervalPiece (piece : Set I) : Prop :=
  ∃ endpoints : Set I, endpoints.Finite ∧
    ∀ x y, SameIntervalCell endpoints x y → (x ∈ piece ↔ y ∈ piece)

/-- Output contract: finite interval pieces forming a complete, exactly envy-free
partition. -/
def IsValidOutput {N : Type*} [Fintype N]
    (problem : CakeInstance N) (allocation : Allocation N I) : Prop :=
  (∀ i, IsFiniteIntervalPiece (allocation i)) ∧
    IsAllocation allocation ∧
    IsEnvyFree (MeasureValuation problem.measure) allocation

/-- A deterministic adaptive tree fixed before the valuations. Branching and height need
not be finite. -/
inductive RWProtocol (N : Type*) [Fintype N]
  | output (allocation : Allocation N I)
  | query (question : RWQuery N)
      (next : question.Answer → RWProtocol N)

/-- A valid execution with its exact query count, including failed cuts. Cut replies may
vary adaptively. -/
inductive RWExecution {N : Type*} [Fintype N] (problem : CakeInstance N) :
    RWProtocol N → Allocation N I → ℕ → Prop
  | output (allocation : Allocation N I) :
      RWExecution problem (.output allocation) allocation 0
  | query {question : RWQuery N}
      {next : question.Answer → RWProtocol N}
      {answer : question.Answer} {allocation : Allocation N I} {queries : ℕ}
      (valid : question.IsValidAnswer problem answer)
      (rest : RWExecution problem (next answer) allocation queries) :
      RWExecution problem (.query question next) allocation (queries + 1)

/-- Every reached query has a valid reply, and every valid reply continues to a correct
output. -/
def RWProtocol.SolvesInstance {N : Type*} [Fintype N]
    (problem : CakeInstance N) : RWProtocol N → Prop
  | .output allocation => IsValidOutput problem allocation
  | .query question next =>
      (∃ answer, question.IsValidAnswer problem answer) ∧
        ∀ answer, question.IsValidAnswer problem answer →
          (next answer).SolvesInstance problem

/-- One protocol works for every nonatomic probability valuation profile on these agents. -/
def RWProtocol.Solves {N : Type*} [Fintype N]
    (protocol : RWProtocol N) : Prop :=
  ∀ problem : CakeInstance N, protocol.SolvesInstance problem

end EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

end


section

/-!
## Query bounds for envy-free cake cutting

Upper and lower bounds are independent research targets; matching bounds are a
stronger target. Candidate functions must be supplied explicitly, not identified with
the optimal complexity by definition. Bounds are worst-case over valuations and all
valid cut replies. The restriction to at least two agents omits the trivial zero-query
case. Source: Procaccia (IJCAI 2009), Section 2.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

open Filter

/-- A protocol family fixed before valuations and replies, uniformly bounded on every
valid execution. -/
def IsQueryUpperBound (upper : ℕ → ℕ) : Prop :=
  ∃ protocols : ∀ n : ℕ, RWProtocol (Fin n),
    ∀ n : ℕ, 2 ≤ n →
      (protocols n).Solves ∧
      ∀ problem allocation queries,
        RWExecution problem (protocols n) allocation queries →
          queries ≤ upper n

/-- Every correct protocol has an instance and a valid execution requiring at least the
proposed bound. -/
def IsQueryLowerBound (lower : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ protocol : RWProtocol (Fin n), protocol.Solves →
      ∃ problem allocation queries,
        RWExecution problem protocol allocation queries ∧
          lower n ≤ queries

/-- Valid upper and lower bounds matching up to constant factors; neither one-sided
improvement requires this conjunction. -/
def MatchingQueryBoundsQuestion (lower upper : ℕ → ℕ) : Prop :=
  IsQueryLowerBound lower ∧ IsQueryUpperBound upper ∧
    (fun n => (upper n : ℝ)) =Θ[atTop] (fun n => (lower n : ℝ))

end EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

/-- A uniform upper bound on envy-free cake-cutting query complexity. -/
theorem cakeCuttingUpperBound :
    IsQueryUpperBound (answer(sorry)) := by
  sorry

/-- Independent lower-bound direction, against every correct protocol. -/
theorem cakeCuttingLowerBound :
    IsQueryLowerBound (answer(sorry)) := by
  sorry

/-- Matching asymptotic upper and lower query bounds. -/
theorem cakeCuttingMatchingBounds :
    MatchingQueryBoundsQuestion (answer(sorry)) (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity
