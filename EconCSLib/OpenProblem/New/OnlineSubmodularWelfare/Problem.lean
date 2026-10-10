/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.New.SharedConcepts.All
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# 14. Online submodular welfare in random order
-/



section

/-!
## Semantic definitions for online submodular welfare in uniformly random order

The semantic policy question targets exactly 0.51 for all normalized monotone
submodular real valuations. Complete assignments are irrevocable; joint-prefix
consistency excludes dependence on future items even through correlations. Dimensions
and labels are public. This section permits all value information on seen items and
does not certify query or local-computation efficiency. The stronger access model is
treated separately. Source: Korula–Mirrokni– Zadimoghaddam, arXiv:1712.05450, Section
2.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

/-- Normalized monotone submodular real-valued valuations. -/
abbrev OnlineValuationProfile (agents items : ℕ) :=
  Fin agents → SubmodularBundleValuation (Finset.univ : Finset (Fin items))

/-- A total owner function gives a complete, disjoint allocation. -/
abbrev OnlineAssignment (agents items : ℕ) := Fin items → Fin agents

/-- The bundle assigned to one agent. -/
def assignmentBundle {agents items : ℕ}
    (A : OnlineAssignment agents items) (i : Fin agents) :
    BundleAllocation (Finset.univ : Finset (Fin items)) :=
  ⟨Finset.univ.filter (fun j => A j = i), Finset.subset_univ _⟩

/-- Social welfare evaluated using each agent's own valuation. -/
noncomputable def assignmentWelfare {agents items : ℕ}
    (v : OnlineValuationProfile agents items)
    (A : OnlineAssignment agents items) : ℝ :=
  ∑ i, (v i).val (assignmentBundle A i)

/-- Items seen through the current zero-indexed arrival position. -/
def revealedPrefix {items : ℕ}
    (order : Equiv.Perm (Fin items)) (t : Fin items) : Finset (Fin items) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Identical revealed labels and values of every subset of the revealed prefix. -/
def SameSubmodularHistory {agents items : ℕ}
    (v v' : OnlineValuationProfile agents items)
    (order order' : Equiv.Perm (Fin items)) (t : Fin items) : Prop :=
  (∀ s, s ≤ t → order s = order' s) ∧
    ∀ i : Fin agents,
      ∀ S : BundleAllocation (Finset.univ : Finset (Fin items)),
        S.1 ⊆ revealedPrefix order t → (v i).val S = (v' i).val S

/-- The joint probability of the assignment pattern on the revealed set. -/
noncomputable def prefixAssignmentProbability {agents items : ℕ}
    (L : Lottery ℝ (OnlineAssignment agents items))
    (seen : Finset (Fin items)) (pattern : OnlineAssignment agents items) : ℝ := by
  classical
  exact ∑ A, L.val A * if (∀ j ∈ seen, A j = pattern j) then 1 else 0

/-- A randomized nonanticipating policy with public horizon. This is a semantic law. -/
structure RandomOrderSubmodularAlgorithm (agents items : ℕ) where
  /-- Allocation law for a fixed profile and arrival order. -/
  outcome : OnlineValuationProfile agents items → Equiv.Perm (Fin items) →
    Lottery ℝ (OnlineAssignment agents items)
  /-- Past assignments cannot change or depend on the future, including through joint
correlations. -/
  online :
    ∀ v v' order order' t,
      SameSubmodularHistory v v' order order' t →
        ∀ pattern,
          prefixAssignmentProbability (outcome v order)
              (revealedPrefix order t) pattern =
            prefixAssignmentProbability (outcome v' order')
              (revealedPrefix order' t) pattern

/-- Expectation over a uniform permutation and internal allocation randomness, never over
valuation profiles. -/
noncomputable def expectedOnlineWelfare {agents items : ℕ}
    (algorithm : RandomOrderSubmodularAlgorithm agents items)
    (v : OnlineValuationProfile agents items) : ℝ :=
  Lottery.expectedValue (uniformLottery (Equiv.Perm (Fin items))) fun order =>
    Lottery.expectedValue (algorithm.outcome v order) (assignmentWelfare v)

/-- The policy-only 0.51 question. Comparing against every complete assignment avoids
computing OPT and handles zero optimum without division. -/
def RandomOrderSubmodularPointFiveOneStatement : Prop :=
  ∀ agents items : ℕ, 0 < agents → 0 < items →
    ∃ algorithm : RandomOrderSubmodularAlgorithm agents items,
      ∀ (v : OnlineValuationProfile agents items)
        (alternative : OnlineAssignment agents items),
        (51 / 100 : ℝ) * assignmentWelfare v alternative ≤
          expectedOnlineWelfare algorithm v

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## Prefix value-query implementations

Each query reveals exactly one value on already arrived items; no exponential value
table is provided for free. One execution determines allocation decisions and query
count. The policy starts independently of valuations and arrival order. Local
continuation computation remains abstract, so the query predicate alone does not
assert polynomial Word-RAM time [KMZ, Section 2].
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
open MeasureTheory

inductive PrefixValueQueryTree (agents items : ℕ)
    (seen : Finset (Fin items)) (Result : Type)
  | done (result : Result)
  | query (agent : Fin agents) (bundle : Finset (Fin items))
      (available : bundle ⊆ seen)
      (next : ℝ → PrefixValueQueryTree agents items seen Result)

noncomputable def PrefixValueQueryTree.run {agents items : ℕ}
    {seen : Finset (Fin items)} {Result : Type}
    (v : OnlineValuationProfile agents items) :
    PrefixValueQueryTree agents items seen Result → Result × ℕ
  | .done result => (result, 0)
  | .query i S _ next =>
      let rest := (next ((v i).val ⟨S, Finset.subset_univ _⟩)).run v
      (rest.1, rest.2 + 1)

/-- The policy precedes valuations and order. Initial memory is public; steps see only
memory and arrived labels. -/
structure ValueQueryPolicy (agents items : ℕ) where
  Memory : Type
  initial : Memory
  step : Memory → (seen : Finset (Fin items)) → Fin items →
    PrefixValueQueryTree agents items seen (Fin agents × Memory)

noncomputable def ValueQueryPolicy.runFrom {agents items : ℕ}
    (P : ValueQueryPolicy agents items) (v : OnlineValuationProfile agents items) :
    List (Fin items) → Finset (Fin items) → P.Memory →
      List (Fin items × Fin agents) × ℕ
  | [], _, _ => ([], 0)
  | current :: tail, seen, memory =>
      let nextSeen := insert current seen
      let one := (P.step memory nextSeen current).run v
      let rest := P.runFrom v tail nextSeen one.1.2
      ((current, one.1.1) :: rest.1, one.2 + rest.2)

noncomputable def ValueQueryPolicy.run {agents items : ℕ}
    (P : ValueQueryPolicy agents items) (v : OnlineValuationProfile agents items)
    (order : Equiv.Perm (Fin items)) : List (Fin items × Fin agents) × ℕ :=
  P.runFrom v (List.ofFn (fun t => order t)) ∅ P.initial

/-- A valuation-independent seed law and a query execution realizing the specified
allocation law. -/
structure ValueQueryImplementation {agents items : ℕ}
    (A : RandomOrderSubmodularAlgorithm agents items) where
  Seed : Type
  [seedMeasurable : MeasurableSpace Seed]
  law : Measure Seed
  probability : IsProbabilityMeasure law
  policy : Seed → ValueQueryPolicy agents items
  output : OnlineValuationProfile agents items → Equiv.Perm (Fin items) →
    Seed → OnlineAssignment agents items
  executes : ∀ v order seed g,
    (g, output v order seed g) ∈ ((policy seed).run v order).1
  measurable_events : ∀ v order assignment,
    MeasurableSet {seed | output v order seed = assignment}
  realizes : ∀ v order assignment,
    law {seed | output v order seed = assignment} =
      ENNReal.ofReal ((A.outcome v order).val assignment)

attribute [instance] ValueQueryImplementation.seedMeasurable

/-- A query bound. A uniform family must choose its constants before the dimensions. -/
def ValueQueryImplementation.HasQueryBound {agents items : ℕ}
    {A : RandomOrderSubmodularAlgorithm agents items}
    (W : ValueQueryImplementation A) (coefficient exponent : ℕ) : Prop :=
  ∀ v order seed, ((W.policy seed).run v order).2 ≤
    coefficient * (agents + items + 1) ^ exponent

/-- The value-query 0.51 target, distinct from the unrestricted policy question and from
polynomial-time implementation. -/
def RandomOrderSubmodularPointFiveOneValueQueryStatement : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ agents items : ℕ, 0 < agents → 0 < items →
      ∃ A : RandomOrderSubmodularAlgorithm agents items,
        (∀ v alternative,
          (51 / 100 : ℝ) * assignmentWelfare v alternative ≤ expectedOnlineWelfare A v) ∧
        ∃ W : ValueQueryImplementation A, W.HasQueryBound coefficient exponent

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## Online execution schema

A fixed schema executes one finite program for all public dimensions. The driver
reveals each arriving item, answers value queries on the revealed prefix, and advances
after an irrevocable assignment. The accounting contract charges each local transition
as one operation.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
open WordRAM.FiniteData
open scoped BigOperators

/-- Prefix-local commands; an assignment irrevocably advances to the next arrival. -/
inductive OnlineCommand (agents items : ℕ) (State : Type)
  | assign (owner : Fin agents) (next : State)
  | local (next : State)
  | value (agent : Fin agents) (bundle : Finset (Fin items)) (next : ℝ → State)
  | randomBit (next : Bool → State)

/-- Operational semantics fixed before the finite program. No field receives private
future input. -/
structure OnlineExecutionSchema where
  State : ℕ → ℕ → Type
  initial : Code → (agents items : ℕ) → State agents items
  step : {agents items : ℕ} → State agents items → Finset (Fin items) →
    Fin items → OnlineCommand agents items (State agents items)

/-- Complete assignment transcript and resources from one run, or explicit failure. -/
structure OnlineExecutionResult (agents items : ℕ) where
  output : Option (List (Fin items × Fin agents))
  steps : ℕ
  queries : ℕ
  randomBits : ℕ

/-- Charge the command just executed; output remains tied to this result. -/
def OnlineExecutionResult.charge {agents items : ℕ}
    (result : OnlineExecutionResult agents items) (queries randomBits : ℕ) :
    OnlineExecutionResult agents items :=
  { result with steps := result.steps + 1
                queries := result.queries + queries
                randomBits := result.randomBits + randomBits }

/-- Only the driver sees the remaining order. Invalid future-item queries fail. -/
noncomputable def OnlineExecutionSchema.runFrom (E : OnlineExecutionSchema)
    {agents items : ℕ} (v : OnlineValuationProfile agents items)
    (tape : ℕ → Option Bool) : ℕ → List (Fin items) → Finset (Fin items) →
      E.State agents items → ℕ → OnlineExecutionResult agents items
  | _, [], _, _, _ => ⟨some [], 0, 0, 0⟩
  | 0, _ :: _, _, _, _ => ⟨none, 0, 0, 0⟩
  | fuel + 1, current :: tail, seen, state, cursor =>
      let now := insert current seen
      match E.step state now current with
      | .assign owner next =>
          let rest := E.runFrom v tape fuel tail now next cursor
          { rest.charge 0 0 with output := rest.output.map ((current, owner) :: ·) }
      | .local next =>
          (E.runFrom v tape fuel (current :: tail) seen next cursor).charge 0 0
      | .value agent bundle next =>
          if bundle ⊆ now then
            (E.runFrom v tape fuel (current :: tail) seen
              (next ((v agent).val ⟨bundle, Finset.subset_univ _⟩)) cursor).charge 1 0
          else ⟨none, 1, 1, 0⟩
      | .randomBit next =>
          match tape cursor with
          | none => ⟨none, 1, 0, 0⟩
          | some bit =>
              (E.runFrom v tape fuel (current :: tail) seen (next bit) (cursor + 1)).charge 0 1

/-- A fixed-length tape of fair bits for the worst-case bounded-time convention. -/
abbrev OnlineRandomTape (bits : ℕ) := Fin bits → Bool

/-- Uniform permutation and independent fair-bit expectation for an actual execution
outcome. -/
noncomputable def expectedExecutionWelfare {agents items bits : ℕ}
    (v : OnlineValuationProfile agents items)
    (outcome : Equiv.Perm (Fin items) → OnlineRandomTape bits → OnlineAssignment agents items) : ℝ :=
  Lottery.expectedValue (uniformLottery (Equiv.Perm (Fin items))) fun order =>
    (∑ tape, assignmentWelfare v (outcome order tape)) / (2 : ℝ) ^ bits

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## Concrete exact-real online execution

A finite arithmetic program persists across item arrivals. Word memory starts with
[agents, items]; word register 1 receives the current label. The next label is
revealed only after an irrevocable assignment. Private valuations can be accessed only
by charged queries on the revealed prefix. Real input memory is empty. The fixed
interpreter. This is an exact-real oracle-cost convention.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
namespace ExactReal

open ExactRealController

inductive Operation
  | value
  | assign
  | randomBit
  deriving DecidableEq, Fintype

/-- Value operands: a=agent word register, b=bundle-start word register, c=real result
register. Assign: a=owner word register. RandomBit: a=destination word register. There
are no arbitrary continuations or real program literals. -/
abbrev Program := ExactRealController.Program Operation

structure Result (agents items : ℕ) where
  output : Option (List (Fin items × Fin agents))
  cost : ℕ
  queries : ℕ
  randomBits : ℕ

def Result.charge {agents items : ℕ} (result : Result agents items)
    (cost queries randomBits : ℕ) : Result agents items :=
  { result with cost := result.cost + cost
                queries := result.queries + queries
                randomBits := result.randomBits + randomBits }

/-- A fixed zero/one-word bitmap, validated before accessing a valuation. -/
noncomputable def readBundle (width items : ℕ) (state : State) (start : ℕ) :
    Option (Finset (Fin items)) := by
  classical
  exact if start + items ≤ WordRAM.wordModulus width ∧
      ∀ j : Fin items, state.machine.memory (start + j.val) = 0 ∨
        state.machine.memory (start + j.val) = 1 then
    some (Finset.univ.filter fun j => state.machine.memory (start + j.val) = 1)
  else none

/-- `seen` includes the current item. Every successful assignment pays for its output cell
and the next-arrival update. Value scans pay for bitmap validation, prefix checking
and the scalar reply write. -/
noncomputable def runFrom (width : ℕ) (program : Program)
    {agents items : ℕ} (v : OnlineValuationProfile agents items)
    (tape : ℕ → Option Bool) : ℕ → List (Fin items) → Finset (Fin items) →
      State → ℕ → Result agents items
  | _, [], _, _, _ => ⟨some [], 0, 0, 0⟩
  | 0, _ :: _, _, _, _ => ⟨none, 0, 0, 0⟩
  | fuel + 1, current :: tail, seen, state, cursor =>
      let one := ExactRealController.step width program state
      match one.status with
      | .running =>
          (runFrom width program v tape fuel (current :: tail) seen one.state cursor).charge
            one.cost 0 0
      | .faulted | .halted _ _ => ⟨none, one.cost, 0, 0⟩
      | .request .value a b c _ =>
          let charged := one.cost + 3 * items + 1
          if ha : one.state.machine.registers a < agents then
            match readBundle width items one.state (one.state.machine.registers b) with
            | none => ⟨none, charged, 1, 0⟩
            | some bundle =>
                if bundle ⊆ seen then
                  let next := one.state.setReal c ((v ⟨_, ha⟩).val ⟨bundle, Finset.subset_univ _⟩)
                  (runFrom width program v tape fuel (current :: tail) seen next cursor).charge
                    charged 1 0
                else ⟨none, charged, 1, 0⟩
          else ⟨none, charged, 1, 0⟩
      | .request .assign a _ _ _ =>
          if ha : one.state.machine.registers a < agents then
            let next := match tail with
              | [] => one.state
              | nextItem :: _ => one.state.setWord width 1 nextItem.val
            let nextSeen := match tail with
              | [] => seen
              | nextItem :: _ => insert nextItem seen
            let rest := (runFrom width program v tape fuel tail nextSeen next cursor).charge
              (one.cost + 2) 0 0
            { rest with output := rest.output.map ((current, ⟨_, ha⟩) :: ·) }
          else ⟨none, one.cost, 0, 0⟩
      | .request .randomBit a _ _ _ =>
          match tape cursor with
          | none => ⟨none, one.cost, 0, 0⟩
          | some bit =>
              let next := one.state.setWord width a (if bit then 1 else 0)
              (runFrom width program v tape fuel (current :: tail) seen next (cursor + 1)).charge
                one.cost 0 1

/-- Initialization has no valuation-dependent data. The driver owns the order; the program
sees only its current label in register 1. The prefix bitmap's initialization and
public first-arrival update are included in the cost. -/
noncomputable def run (model : WordRAM.Model) (program : Program)
    (agents items budget : ℕ) (v : OnlineValuationProfile agents items)
    (order : Equiv.Perm (Fin items)) (tape : OnlineRandomTape budget) : Result agents items :=
  let width := WordRAM.wordWidth model.widthFactor (agents + items + 1)
  let input := [agents, items]
  if input.length < WordRAM.wordModulus width ∧
      agents < WordRAM.wordModulus width ∧ items < WordRAM.wordModulus width then
    let initial := State.initial width input []
    let remaining := List.ofFn (fun t => order t)
    let state := match remaining with
      | [] => initial
      | current :: _ => initial.setWord width 1 current.val
    let seen := match remaining with
      | [] => ∅
      | current :: _ => {current}
    (runFrom width program v
      (fun cursor => if h : cursor < budget then some (tape ⟨cursor, h⟩) else none)
      budget remaining seen state 0).charge (initialCost program input [] + items + 5) 0 0
  else ⟨none, initialCost program input [] + 3, 0, 0⟩

/-- One finite exact-real program and polynomial resource bound precede all profiles. The
only averaging is over arrival permutation and fair random bits. -/
def PointFiveOneQuestion : Prop :=
  ∃ model : WordRAM.Model, ∃ program : Program, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ agents items : ℕ, 0 < agents → 0 < items →
      ∀ v : OnlineValuationProfile agents items,
        ∃ outcome : Equiv.Perm (Fin items) →
            OnlineRandomTape (budget (agents + items + 1)) → OnlineAssignment agents items,
          (∀ order tape,
            let result := run model program agents items (budget (agents + items + 1)) v order tape
            result.output = some (List.ofFn (fun t => (order t, outcome order tape (order t)))) ∧
            result.cost ≤ budget (agents + items + 1) ∧
            result.queries ≤ budget (agents + items + 1) ∧
            result.randomBits ≤ budget (agents + items + 1)) ∧
          ∀ alternative, (51 / 100 : ℝ) * assignmentWelfare v alternative ≤
            expectedExecutionWelfare v outcome

end ExactReal
end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


section

/-!
## The 0.51 random-order online-welfare question

The primary efficiency target uses a finite exact-real arithmetic controller, with
fixed primitives and a charged prefix-local oracle interpreter. It has no arbitrary
local transition callback. Exact-real unit-cost arithmetic is an explicit model
convention. Policy, query, trusted-schema and rational Word-RAM variants remain
separately named.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

/-- The primary full-real question for the fixed exact-real controller. -/
def OnlineSubmodularWelfareQuestion : Prop :=
  ExactReal.PointFiveOneQuestion

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare

/-- The 0.51 random-order question under the explicit exact-real controller. -/
theorem onlineSubmodularWelfare :
    answer(sorry) ↔ OnlineSubmodularWelfareQuestion := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.OnlineSubmodularWelfare
