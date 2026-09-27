/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.SubmodularWelfareDemandOracle
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# 23. Submodular welfare maximization with demand oracles
-/



section

/-!
## Submodular welfare: semantic domain and guarantees

Uses native normalized monotone submodular valuations and complete allocations. The
rational-price interface is a separate finite-code implementation convention; it does
not claim that all real prices admit finite encodings. The full-real value-and-demand
interface is defined in RealOracle. Source: Feige–Vondrak, Theory of Computing 6
(2010), Section 1.
-/
open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

abbrev SWMProfile (agents items : ℕ) :=
  Fin agents → SubmodularBundleValuation (Finset.univ : Finset (Fin items))

abbrev SWMBundle (items : ℕ) := Finset (Fin items)

abbrev SWMAssignment (agents items : ℕ) := Fin items → Fin agents

def asBundle {items : ℕ} (S : SWMBundle items) :
    BundleAllocation (Finset.univ : Finset (Fin items)) :=
  ⟨S, Finset.subset_univ _⟩

noncomputable def value {agents items : ℕ} (v : SWMProfile agents items)
    (i : Fin agents) (S : SWMBundle items) : ℝ :=
  (v i).val (asBundle S)

def assignedBundle {agents items : ℕ} (A : SWMAssignment agents items)
    (i : Fin agents) : SWMBundle items :=
  Finset.univ.filter fun j => A j = i

noncomputable def welfare {agents items : ℕ} (v : SWMProfile agents items)
    (A : SWMAssignment agents items) : ℝ :=
  ∑ i, value v i (assignedBundle A i)

/-- The exact target 1 - 1/e + 0.01, without rounding or an unspecified epsilon. -/
noncomputable def targetRatio : ℝ := 1 - 1 / Real.exp 1 + 1 / 100

abbrev SWMRandomTape (bits : ℕ) := Fin bits → Bool

/-- Exact expectation over fixed-length fair-bit tapes, with no prior on valuations or
oracle randomness. -/
noncomputable def expectedWelfare {agents items bits : ℕ}
    (v : SWMProfile agents items)
    (outcome : SWMRandomTape bits → SWMAssignment agents items) : ℝ :=
  (∑ tape, welfare v (outcome tape)) / (2 : ℝ) ^ bits

/-- Comparison with every complete allocation is equivalent to comparison with OPT when
there is at least one agent. -/
def MeetsApproximation {agents items bits : ℕ} (v : SWMProfile agents items)
    (outcome : SWMRandomTape bits → SWMAssignment agents items) : Prop :=
  ∀ alternative : SWMAssignment agents items,
    targetRatio * welfare v alternative ≤ expectedWelfare v outcome

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Real-valued value and demand access

The main reference convention permits both charged value and demand queries.
Bundle-only access is retained as a separate literal variant. Prices and values remain
real; a fixed legal demand oracle precedes randomization. Execution reads private
values only at query nodes and counts repeated queries separately. Continuations have
abstract local computation, so this layer certifies only query complexity, not
polynomial running time [Feige–Vondrak 2010, p. 248].
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open MeasureTheory
open scoped BigOperators

structure RealDemandQuery (agents items : ℕ) where
  agent : Fin agents
  price : Fin items → ℝ
  nonnegative : ∀ j, 0 ≤ price j

noncomputable def realDemandUtility {agents items : ℕ} (v : SWMProfile agents items)
    (q : RealDemandQuery agents items) (S : SWMBundle items) : ℝ :=
  value v q.agent S - ∑ j ∈ S, q.price j

def IsRealDemandAnswer {agents items : ℕ} (v : SWMProfile agents items)
    (q : RealDemandQuery agents items) (S : SWMBundle items) : Prop :=
  ∀ T, realDemandUtility v q T ≤ realDemandUtility v q S

abbrev RealDemandOracle (agents items : ℕ) :=
  RealDemandQuery agents items → SWMBundle items

def IsValidRealDemandOracle {agents items : ℕ} (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) : Prop :=
  ∀ q, IsRealDemandAnswer v q (oracle q)

/-- A value-reporting reply contains a utility-maximizing bundle and exactly its value,
with no arbitrary advice scalar. -/
def IsValueReportingDemandAnswer {agents items : ℕ} (v : SWMProfile agents items)
    (q : RealDemandQuery agents items) (answer : SWMBundle items × ℝ) : Prop :=
  IsRealDemandAnswer v q answer.1 ∧ answer.2 = value v q.agent answer.1

inductive RealOracleConvention
  | bundleOnly
  | valueAndDemand
  deriving DecidableEq

inductive RealSWMQueryTree (agents items : ℕ)
  | done (assignment : SWMAssignment agents items)
  | demand (query : RealDemandQuery agents items)
      (next : SWMBundle items → RealSWMQueryTree agents items)
  | value (agent : Fin agents) (bundle : SWMBundle items)
      (next : ℝ → RealSWMQueryTree agents items)

def RealSWMQueryTree.Allowed {agents items : ℕ} (mode : RealOracleConvention) :
    RealSWMQueryTree agents items → Prop
  | .done _ => True
  | .demand _ next => ∀ answer, (next answer).Allowed mode
  | .value _ _ next => mode = .valueAndDemand ∧ ∀ answer, (next answer).Allowed mode

noncomputable def RealSWMQueryTree.run {agents items : ℕ}
    (v : SWMProfile agents items) (oracle : RealDemandOracle agents items) :
    RealSWMQueryTree agents items → SWMAssignment agents items × ℕ
  | .done assignment => (assignment, 0)
  | .demand query next =>
      let rest := (next (oracle query)).run v oracle
      (rest.1, rest.2 + 1)
  | .value agent bundle next =>
      let rest := (next (EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle.value v agent bundle)).run v oracle
      (rest.1, rest.2 + 1)

structure RealSWMQueryAlgorithm (agents items : ℕ) where
  Seed : Type
  [seedMeasurable : MeasurableSpace Seed]
  law : Measure Seed
  probability : IsProbabilityMeasure law
  program : Seed → RealSWMQueryTree agents items
  measurable_events : ∀ v oracle, IsValidRealDemandOracle v oracle → ∀ assignment,
    MeasurableSet {seed | ((program seed).run v oracle).1 = assignment}

attribute [instance] RealSWMQueryAlgorithm.seedMeasurable

noncomputable def RealSWMQueryAlgorithm.expectedWelfare {agents items : ℕ}
    (A : RealSWMQueryAlgorithm agents items) (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) : ℝ :=
  ∑ assignment,
    (A.law {seed | ((A.program seed).run v oracle).1 = assignment}).toReal *
      welfare v assignment

/-- The query and approximation part of the target. Local running time is a separate
obligation. -/
noncomputable def RealSWMPolynomialQueryStatement (mode : RealOracleConvention) : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ agents items : ℕ, 0 < agents →
      ∃ A : RealSWMQueryAlgorithm agents items,
        (∀ seed, (A.program seed).Allowed mode) ∧
        ∀ v oracle, IsValidRealDemandOracle v oracle →
          (∀ seed, ((A.program seed).run v oracle).2 ≤
            coefficient * (agents + items + 1) ^ exponent) ∧
          ∀ alternative,
            targetRatio * welfare v alternative ≤ A.expectedWelfare v oracle

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Welfare-maximization execution schema

A fixed schema executes one finite program for all dimensions. The driver supplies
oracle replies and random bits. The schema's accounting contract determines the cost
of local transitions, and the interpreter records output and accumulated cost.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

/-- Observable commands; the interpreter. -/
inductive RealSWMCommand (agents items : ℕ) (State : Type)
  | halt (assignment : SWMAssignment agents items)
  | local (next : State)
  | value (agent : Fin agents) (bundle : SWMBundle items) (next : ℝ → State)
  | demand (query : RealDemandQuery agents items) (next : SWMBundle items → State)
  | randomBit (next : Bool → State)

/-- A fixed operational meaning of finite programs. Local-step accounting is an explicit
trust boundary. -/
structure RealSWMExecutionSchema where
  State : ℕ → ℕ → Type
  initial : Code → (agents items : ℕ) → State agents items
  step : {agents items : ℕ} → State agents items →
    RealSWMCommand agents items (State agents items)

/-- Output and all charged resources from one execution; `none` denotes fuel or tape
exhaustion. -/
structure RealSWMExecutionResult (agents items : ℕ) where
  output : Option (SWMAssignment agents items)
  steps : ℕ
  queries : ℕ
  randomBits : ℕ

/-- Add the command just executed to the same result's counters. -/
def RealSWMExecutionResult.charge {agents items : ℕ}
    (result : RealSWMExecutionResult agents items) (queries randomBits : ℕ) :
    RealSWMExecutionResult agents items :=
  { result with steps := result.steps + 1
                queries := result.queries + queries
                randomBits := result.randomBits + randomBits }

/-- Bounded interpretation with full-real replies and fixed legal demand selection. -/
noncomputable def RealSWMExecutionSchema.runFrom (E : RealSWMExecutionSchema)
    {agents items : ℕ} (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) (tape : ℕ → Option Bool) :
    ℕ → E.State agents items → ℕ → RealSWMExecutionResult agents items
  | 0, _, _ => ⟨none, 0, 0, 0⟩
  | fuel + 1, state, cursor =>
      match E.step state with
      | .halt assignment => ⟨some assignment, items + 1, 0, 0⟩
      | .local next => (E.runFrom v oracle tape fuel next cursor).charge 0 0
      | .value agent bundle next =>
          (E.runFrom v oracle tape fuel (next (value v agent bundle)) cursor).charge 1 0
      | .demand query next =>
          (E.runFrom v oracle tape fuel (next (oracle query)) cursor).charge 1 0
      | .randomBit next =>
          match tape cursor with
          | none => ⟨none, 1, 0, 0⟩
          | some bit => (E.runFrom v oracle tape fuel (next bit) (cursor + 1)).charge 0 1

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Concrete exact-real value-and-demand execution

The controller has finite syntax and fixed arithmetic primitives. Only this
interpreter accesses valuations and the fixed legal demand oracle. Public input
consists of the two dimensions; real memory starts empty. Query buffers, returned
bundles, allocation validation and initialization are charged. This exact-real
unit-cost convention is distinct from bounded Word-RAM and has no solver-selected
transition function or output decoder.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
namespace ExactReal

open ExactRealController

/-- No external local-computation callback is available. -/
inductive Operation
  | value
  | demand
  | randomBit
  deriving DecidableEq, Fintype

/-- Value: a=agent word register, b=bundle-start word register, c=real result register.
Demand: a=agent, b=real-price-start, c=bundle-output-start word registers. RandomBit:
a=destination word register. Unused operands are ignored. -/
abbrev Program := ExactRealController.Program Operation

structure Result (agents items : ℕ) where
  output : Option (SWMAssignment agents items)
  cost : ℕ
  queries : ℕ
  randomBits : ℕ

def Result.charge {agents items : ℕ} (result : Result agents items)
    (cost queries randomBits : ℕ) : Result agents items :=
  { result with cost := result.cost + cost
                queries := result.queries + queries
                randomBits := result.randomBits + randomBits }

/-- A bundle is exactly one zero/one word per item, without an answer decoder. -/
noncomputable def readBundle (width items : ℕ) (state : State) (start : ℕ) :
    Option (SWMBundle items) := by
  classical
  exact if start + items ≤ WordRAM.wordModulus width ∧
      ∀ j : Fin items, state.machine.memory (start + j.val) = 0 ∨
        state.machine.memory (start + j.val) = 1 then
    some (Finset.univ.filter fun j => state.machine.memory (start + j.val) = 1)
  else none

/-- Decode exactly m owner indices. The interpreter charges this finite scan. -/
noncomputable def readAssignment (agents items : ℕ) (output : List ℕ) :
    Option (SWMAssignment agents items) := by
  classical
  exact if output.length = items then
    if h : ∀ j : Fin items, (output[j.val]?).getD agents < agents then
      some (fun j => ⟨(output[j.val]?).getD agents, h j⟩)
    else none
  else none

/-- Price reads, value replies and bundle writes have fixed meanings. A demand reply
supplies only the chosen bundle. -/
noncomputable def runFrom (width : ℕ) (program : Program)
    {agents items : ℕ} (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) (tape : ℕ → Option Bool) :
    ℕ → State → ℕ → Result agents items
  | 0, _, _ => ⟨none, 0, 0, 0⟩
  | fuel + 1, state, cursor =>
      let one := ExactRealController.step width program state
      match one.status with
      | .running =>
          (runFrom width program v oracle tape fuel one.state cursor).charge one.cost 0 0
      | .faulted => ⟨none, one.cost, 0, 0⟩
      | .halted output reals =>
          ⟨if reals.isEmpty then readAssignment agents items output else none,
            one.cost + output.length + 1, 0, 0⟩
      | .request .value a b c _ =>
          let charged := one.cost + 2 * items + 1
          if ha : one.state.machine.registers a < agents then
            match readBundle width items one.state (one.state.machine.registers b) with
            | none => ⟨none, charged, 1, 0⟩
            | some bundle =>
                let next := one.state.setReal c (value v ⟨_, ha⟩ bundle)
                (runFrom width program v oracle tape fuel next cursor).charge charged 1 0
          else ⟨none, charged, 1, 0⟩
      | .request .demand a b c _ =>
          let charged := one.cost + 3 * items
          let start := one.state.machine.registers b
          let destination := one.state.machine.registers c
          if ha : one.state.machine.registers a < agents then
            if start + items ≤ WordRAM.wordModulus width ∧
                destination + items ≤ WordRAM.wordModulus width ∧
                1 < WordRAM.wordModulus width then
              let prices := fun j : Fin items => one.state.memory (start + j.val)
              if hp : ∀ j, 0 ≤ prices j then
                let bundle := oracle ⟨⟨_, ha⟩, prices, hp⟩
                let bits := List.ofFn fun j : Fin items => if j ∈ bundle then 1 else 0
                let memory := writeWords one.state.machine.memory destination bits
                let next := { one.state with machine := { one.state.machine with memory } }
                (runFrom width program v oracle tape fuel next cursor).charge charged 1 0
              else ⟨none, charged, 1, 0⟩
            else ⟨none, charged, 1, 0⟩
          else ⟨none, charged, 1, 0⟩
      | .request .randomBit a _ _ _ =>
          match tape cursor with
          | none => ⟨none, one.cost, 0, 0⟩
          | some bit =>
              let next := one.state.setWord width a (if bit then 1 else 0)
              (runFrom width program v oracle tape fuel next (cursor + 1)).charge one.cost 0 1

/-- The address width is logarithmic in the public object count n+m+1. No valuation table
or hidden real input is supplied. -/
noncomputable def run (model : WordRAM.Model) (program : Program)
    (agents items budget : ℕ) (v : SWMProfile agents items)
    (oracle : RealDemandOracle agents items) (tape : SWMRandomTape budget) :
    Result agents items :=
  let width := WordRAM.wordWidth model.widthFactor (agents + items + 1)
  let input := [agents, items]
  if input.length < WordRAM.wordModulus width ∧
      agents < WordRAM.wordModulus width ∧ items < WordRAM.wordModulus width then
    let state := State.initial width input []
    (runFrom width program v oracle
      (fun cursor => if h : cursor < budget then some (tape ⟨cursor, h⟩) else none)
      budget state 0).charge (initialCost program input [] + 3) 0 0
  else ⟨none, initialCost program input [] + 3, 0, 0⟩

/-- One finite exact-real program works for every dimension and real profile. Actual
execution determines the allocation and all resource counts. -/
def PolynomialApproximationQuestion : Prop :=
  ∃ model : WordRAM.Model, ∃ program : Program, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ agents items : ℕ, 0 < agents →
      ∀ (v : SWMProfile agents items) (oracle : RealDemandOracle agents items),
        IsValidRealDemandOracle v oracle →
          ∃ outcome : SWMRandomTape (budget (agents + items + 1)) →
              SWMAssignment agents items,
            (∀ tape,
              let result := run model program agents items (budget (agents + items + 1)) v oracle tape
              result.output = some (outcome tape) ∧
              result.cost ≤ budget (agents + items + 1) ∧
              result.queries ≤ budget (agents + items + 1) ∧
              result.randomBits ≤ budget (agents + items + 1)) ∧
            MeetsApproximation v outcome

end ExactReal
end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


section

/-!
## Welfare targets with explicit computational scope

The full-real query target uses value and demand access, following the numerical
oracle convention in Feige–Vondrak (2010), p. 248. Query complexity alone does not
certify polynomial local time. The primary full-real question uses a fixed finite
exact-real arithmetic language with charged oracle interaction. The separate Word-RAM
statements use actual executions on named represented domains, with worst-case time,
query, and fair-bit bounds.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
open WordRAM.FiniteData

/-- The primary full-real value-and-demand target uses a finite exact-real controller with
fixed arithmetic instructions and charged oracle buffers. -/
def SubmodularWelfareQuestion : Prop :=
  ExactReal.PolynomialApproximationQuestion

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle

/-- The welfare approximation question with charged exact-real value and demand access. -/
theorem submodularWelfareDemandOracle :
    answer(sorry) ↔ SubmodularWelfareQuestion := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.SubmodularWelfareDemandOracle
