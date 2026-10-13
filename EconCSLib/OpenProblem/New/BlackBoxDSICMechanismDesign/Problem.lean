/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# 02. Black-box DSIC mechanism design
-/



section

/-!
## Economic specification of black-box DSIC reductions

Following Gergatsouli--Lucier--Tzamos (2019), Section 2.4, reports and valuation maps
are fixed before the simulator. Allocation and realized payment form one joint random
outcome. DSIC is truthfulness in expectation against arbitrary opponent reports, not
universal truthfulness. Nonnegative welfare uses extended expectation; finite expected
payments require integrability. These semantic contracts alone provide no black-box
execution or runtime.
-/
open scoped BigOperators
open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

abbrev RealProfile (n : ℕ) := {v : Fin n → ℝ // ∀ i, 0 ≤ v i}
abbrev Allocation (n : ℕ) := Fin n → ℝ
abbrev Outcome (n : ℕ) := Allocation n × (Fin n → ℝ)

/-- Allocations lie in the unit cube. -/
def IsUnitAllocation {n : ℕ} (x : Allocation n) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 1

/-- Social welfare excludes transfers. -/
def fractionalWelfare {n : ℕ} (v x : Fin n → ℝ) : ℝ :=
  ∑ i, v i * x i

/-- Independent types and an allocation kernel. Neither the feasibility set nor its
membership oracle is exposed. Full support and identical priors are not required. -/
structure AllocationOracle {n : ℕ} (Report : Type*) [MeasurableSpace Report]
    (values : Report → Fin n → ℝ) where
  values_nonnegative : ∀ r i, 0 ≤ values r i
  values_measurable : Measurable values
  prior : Measure Report
  probability : IsProbabilityMeasure prior
  independent : iIndepFun (fun i r => values r i) prior
  algorithm : Report → Measure (Allocation n)
  algorithm_probability : ∀ r, IsProbabilityMeasure (algorithm r)
  algorithm_measurable : ∀ s : Set (Allocation n), MeasurableSet s →
    Measurable (fun r => algorithm r s)
  allocation_mem_unit : ∀ r, ∀ᵐ x ∂algorithm r, IsUnitAllocation x

/-- Every hidden feasibility set compatible with the oracle must be respected. -/
structure CompatibleFeasibility {n : ℕ} {Report : Type*}
    [MeasurableSpace Report] {values : Report → Fin n → ℝ}
    (oracle : AllocationOracle Report values) where
  feasible : Set (Allocation n)
  algorithm_feasible : ∀ r, ∀ᵐ x ∂oracle.algorithm r, x ∈ feasible

/-- A direct mechanism with possibly correlated realized allocation and payment. It need
not compute the exact expected payment on every execution. -/
structure Mechanism (Report : Type*) [MeasurableSpace Report] (n : ℕ) where
  outcome : Report → Measure (Outcome n)
  probability : ∀ r, IsProbabilityMeasure (outcome r)
  outcome_measurable : ∀ s : Set (Outcome n), MeasurableSet s →
    Measurable (fun r => outcome r s)
  allocation_mem_unit : ∀ r, ∀ᵐ o ∂outcome r, IsUnitAllocation o.1
  /-- Allocations are bounded measurable coordinates; only payment integrability needs a
separate field. -/
  payment_integrable : ∀ r i, Integrable (fun o : Outcome n => o.2 i) (outcome r)

noncomputable def Mechanism.expectedAllocation {Report : Type*}
    [MeasurableSpace Report] {n : ℕ} (M : Mechanism Report n)
    (r : Report) (i : Fin n) : ℝ :=
  ∫ o, o.1 i ∂M.outcome r

noncomputable def Mechanism.expectedPayment {Report : Type*}
    [MeasurableSpace Report] {n : ℕ} (M : Mechanism Report n)
    (r : Report) (i : Fin n) : ℝ :=
  ∫ o, o.2 i ∂M.outcome r

/-- Utility uses the true value; r is only the report sent to the mechanism. -/
noncomputable def expectedUtility {Report : Type*} [MeasurableSpace Report]
    {n : ℕ} (values : Report → Fin n → ℝ) (M : Mechanism Report n)
    (truth r : Report) (i : Fin n) : ℝ :=
  values truth i * M.expectedAllocation r i - M.expectedPayment r i

/-- Only one coordinate changes; opponent reports need not lie in prior support. -/
def IsUnilateralDeviation {Report : Type*} {n : ℕ}
    (values : Report → Fin n → ℝ) (truth alternate : Report) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → values alternate j = values truth j

/-- DSIC/TIE against every opponent report, with expectation only over mechanism
randomness. -/
noncomputable def IsDSIC {Report : Type*} [MeasurableSpace Report]
    {n : ℕ} (values : Report → Fin n → ℝ) (M : Mechanism Report n) : Prop :=
  ∀ truth alternate i, IsUnilateralDeviation values truth alternate i →
    expectedUtility values M truth alternate i ≤ expectedUtility values M truth truth i

noncomputable def algorithmExpectedWelfare {Report : Type*}
    [MeasurableSpace Report] {n : ℕ} {values : Report → Fin n → ℝ}
    (O : AllocationOracle Report values) : ℝ≥0∞ :=
  ∫⁻ r, ∫⁻ x, ENNReal.ofReal (fractionalWelfare (values r) x)
    ∂O.algorithm r ∂O.prior

noncomputable def mechanismExpectedWelfare {Report : Type*}
    [MeasurableSpace Report] {n : ℕ} {values : Report → Fin n → ℝ}
    (O : AllocationOracle Report values) (M : Mechanism Report n) : ℝ≥0∞ :=
  ∫⁻ r, ∫⁻ o, ENNReal.ofReal (fractionalWelfare (values r) o.1)
    ∂M.outcome r ∂O.prior

/-- Hidden feasibility, DSIC and expected welfare at least that of A. No pointwise
guarantee or approximation against the optimum is substituted. -/
noncomputable def MeetsSpecification {Report : Type*} [MeasurableSpace Report]
    {n : ℕ} {values : Report → Fin n → ℝ}
    (O : AllocationOracle Report values) (M : Mechanism Report n) : Prop :=
  (∀ hidden : CompatibleFeasibility O, ∀ r,
    ∀ᵐ o ∂M.outcome r, o.1 ∈ hidden.feasible) ∧
  IsDSIC values M ∧
  algorithmExpectedWelfare O ≤ mechanismExpectedWelfare O M

/-- The full nonnegative-real report domain. -/
abbrev RealOracle (n : ℕ) :=
  AllocationOracle (RealProfile n) (fun r => r.1)

/-- Full-real economic correctness, without a computational claim. -/
noncomputable def MeetsRealSpecification {n : ℕ}
    (O : RealOracle n) (M : Mechanism (RealProfile n) n) : Prop :=
  MeetsSpecification O M

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Full-real reduction correctness and adaptive reply laws

Reports, allocations and payments remain real. Economic correctness does not imply
black-box access or efficiency. GLT (2019), Section 2.4 and Remark 1, distinguish a
once-fixed algorithm from fresh sampling. Conditional kernels specify each adaptive
next reply.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open MeasureTheory ProbabilityTheory

/-- A deterministic or once-fixed algorithm. The map f cannot receive the simulator's
history or private randomness. -/
def IsFixedRealAlgorithm {n : ℕ} (O : RealOracle n)
    (f : RealProfile n → Allocation n) : Prop :=
  Measurable f ∧ ∀ r, O.algorithm r = Measure.dirac (f r)

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Sample access and rational external operations

The simulator may query the allocation algorithm and sample the prior (GLT 2019,
Section 2.4). It cannot inspect feasibility, source code, CDFs, densities or
conditional distributions. This section uses fresh sampling; the once-fixed algorithm
convention is recorded separately.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open WordRAM.FiniteData
open MeasureTheory ProbabilityTheory

noncomputable def fairBitMeasure : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac false +
    (2 : ENNReal)⁻¹ • Measure.dirac true

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Output and cost from the same execution

Core commands use WordRAM.step through Interaction. External operations charge request
and response lengths. No freely annotated cost is accepted. The law includes realized
payments; expectations are imposed semantically.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open WordRAM.FiniteData
open MeasureTheory ProbabilityTheory

inductive RuntimeConvention
  | uniformAlmostSure
  | expected
  deriving DecidableEq, Fintype

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Black-box execution with a fixed allocation algorithm

The driver queries the allocation algorithm and draws fresh prior samples. The schema
receives reports and replies and produces realized allocations and payments. State
spaces, observations, and reply continuations satisfy the stated measurability
conditions [GLT 2019, Section 2.4 and Remark 1].

The accounting contract assigns unit cost to initialization and local transitions and
charges input, code, and output copying.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open MeasureTheory ProbabilityTheory
open WordRAM.FiniteData

/-- Prior samples and private fair bits; the fixed algorithm has no fresh tape. -/
abbrev RealSampleTape (n : ℕ) := (ℕ → RealProfile n) × (ℕ → Bool)

/-- Distinct sample requests use distinct independent coordinates. -/
inductive RealRandomSource
  | prior (serial : ℕ)
  | bit (serial : ℕ)

/-- The response type of each independent source. -/
def RealRandomSource.Value (n : ℕ) : RealRandomSource → Type
  | .prior _ => RealProfile n
  | .bit _ => Bool

@[reducible] def RealRandomSource.valueMeasurableSpace (n : ℕ)
    (source : RealRandomSource) : MeasurableSpace (source.Value n) :=
  match source with
  | .prior _ => (inferInstance : MeasurableSpace (RealProfile n))
  | .bit _ => (inferInstance : MeasurableSpace Bool)

/-- Read one source coordinate; the interpreter controls the serial number. -/
def RealRandomSource.observe {n : ℕ} (source : RealRandomSource)
    (tape : RealSampleTape n) : source.Value n :=
  match source with
  | .prior serial => tape.1 serial
  | .bit serial => tape.2 serial

/-- A product law of fresh prior samples and fair bits. Existence is required by the final
target; no assertion is made by quantifying over an empty law type. -/
structure FixedRealSampleLaw {n : ℕ} (O : RealOracle n) where
  measure : Measure (RealSampleTape n)
  probability : IsProbabilityMeasure measure
  independent : iIndepFun
    (m := fun source => RealRandomSource.valueMeasurableSpace n source)
    (fun source tape => RealRandomSource.observe source tape) measure
  prior_measurable : ∀ serial, Measurable (fun t : RealSampleTape n => t.1 serial)
  prior_law : ∀ serial,
    Measure.map (fun t : RealSampleTape n => t.1 serial) measure = O.prior
  bit_measurable : ∀ serial, Measurable (fun t : RealSampleTape n => t.2 serial)
  bit_law : ∀ serial,
    Measure.map (fun t : RealSampleTape n => t.2 serial) measure = fairBitMeasure

/-- Explicit permitted commands. No operation reads a prior description or feasibility. -/
inductive RealCommand (n : ℕ) (State : Type)
  | halt (outcome : Outcome n)
  | local (next : State)
  | algorithm (report : RealProfile n) (next : Allocation n → State)
  | samplePrior (next : RealProfile n → State)
  | randomBit (next : Bool → State)

/-- A discrete observable command tag. -/
def RealCommand.tag {n : ℕ} {State : Type} : RealCommand n State → ℕ
  | .halt _ => 0
  | .local _ => 1
  | .algorithm _ _ => 2
  | .samplePrior _ => 3
  | .randomBit _ => 4

/-- Tagged realized outcome: `inl ()` marks a command other than halt. -/
def RealCommand.haltOutput {n : ℕ} {State : Type} :
    RealCommand n State → Unit ⊕ Outcome n
  | .halt output => .inr output
  | _ => .inl ()

/-- Tagged next state of a local command. -/
def RealCommand.localNext {n : ℕ} {State : Type} : RealCommand n State → Unit ⊕ State
  | .local next => .inr next
  | _ => .inl ()

/-- Tagged report actually sent to the allocation oracle. -/
def RealCommand.algorithmReport {n : ℕ} {State : Type} :
    RealCommand n State → Unit ⊕ RealProfile n
  | .algorithm report _ => .inr report
  | _ => .inl ()

/-- Allocation-reply continuation, exposed jointly with its reply for measurability. -/
def RealCommand.afterAlgorithm {n : ℕ} {State : Type} :
    RealCommand n State → Allocation n → Unit ⊕ State
  | .algorithm _ next, reply => .inr (next reply)
  | _, _ => .inl ()

/-- Prior-reply continuation, exposed jointly with its reply for measurability. -/
def RealCommand.afterPrior {n : ℕ} {State : Type} :
    RealCommand n State → RealProfile n → Unit ⊕ State
  | .samplePrior next, reply => .inr (next reply)
  | _, _ => .inl ()

/-- Coin-reply continuation, exposed jointly with its reply for measurability. -/
def RealCommand.afterBit {n : ℕ} {State : Type} :
    RealCommand n State → Bool → Unit ⊕ State
  | .randomBit next, reply => .inr (next reply)
  | _, _ => .inl ()

/-- Local-step semantics chosen independently of the algorithmic witness. Its local
computation contract remains trusted until separately realized. -/
structure RealBlackBoxSchema where
  State : ℕ → Type
  stateSpace : (n : ℕ) → MeasurableSpace (State n)
  initial : Code → {n : ℕ} → RealProfile n → State n
  step : {n : ℕ} → State n → RealCommand n (State n)
  initial_measurable : ∀ program n,
    letI := stateSpace n
    Measurable (initial program (n := n))
  tag_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun state : State n => (step state).tag)
  output_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun state : State n => (step state).haltOutput)
  local_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun state : State n => (step state).localNext)
  query_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun state : State n => (step state).algorithmReport)
  algorithm_continuation_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun pair : State n × Allocation n => (step pair.1).afterAlgorithm pair.2)
  prior_continuation_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun pair : State n × RealProfile n => (step pair.1).afterPrior pair.2)
  bit_continuation_measurable : ∀ n,
    letI := stateSpace n
    Measurable (fun pair : State n × Bool => (step pair.1).afterBit pair.2)

/-- Execute commands using only the declared black-box access. Fuel is not available to
the schema. Each command costs one; halt also emits 2n coordinates. -/
noncomputable def RealBlackBoxSchema.runFrom (E : RealBlackBoxSchema)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (tape : RealSampleTape n) :
    ℕ → E.State n → ℕ → ℕ → Option (Outcome n) × ℕ
  | 0, _, _, _ => (none, 0)
  | fuel + 1, state, sampleCursor, bitCursor =>
      let charge := fun result : Option (Outcome n) × ℕ => (result.1, result.2 + 1)
      match E.step state with
      | .halt outcome => (some outcome, 2 * n + 1)
      | .local next => charge (E.runFrom algorithm tape fuel next sampleCursor bitCursor)
      | .algorithm report next =>
          charge (E.runFrom algorithm tape fuel (next (algorithm report)) sampleCursor bitCursor)
      | .samplePrior next =>
          charge (E.runFrom algorithm tape fuel (next (tape.1 sampleCursor))
            (sampleCursor + 1) bitCursor)
      | .randomBit next =>
          charge (E.runFrom algorithm tape fuel (next (tape.2 bitCursor))
            sampleCursor (bitCursor + 1))

/-- Public initialization receives only code and report. Their copying plus one trusted
initialization step is charged, independently of fuel. -/
noncomputable def RealBlackBoxSchema.run (E : RealBlackBoxSchema)
    (program : Code) {n : ℕ} (algorithm : RealProfile n → Allocation n)
    (report : RealProfile n) (tape : RealSampleTape n) (fuel : ℕ) :=
  let result := E.runFrom algorithm tape fuel (E.initial program report) 0 0
  (result.1, result.2 + program.length + n + 1)

/-- A measurable output read from this execution, allowing only a null set of
nonterminating tapes. -/
structure FixedRealExecutionWitness (E : RealBlackBoxSchema) (program : Code)
    {n : ℕ} {O : RealOracle n} (algorithm : RealProfile n → Allocation n)
    (report : RealProfile n) (L : FixedRealSampleLaw O) where
  fuel : RealSampleTape n → ℕ
  output : RealSampleTape n → Outcome n
  output_measurable : Measurable output
  halts : ∀ᵐ tape ∂L.measure,
    (E.run program algorithm report tape (fuel tape)).1 = some (output tape)

/-- Actual charged cost of the same run whose output is witnessed. -/
noncomputable def FixedRealExecutionWitness.cost
    {E : RealBlackBoxSchema} {program : Code} {n : ℕ} {O : RealOracle n}
    {algorithm : RealProfile n → Allocation n} {report : RealProfile n}
    {L : FixedRealSampleLaw O} (W : FixedRealExecutionWitness E program algorithm report L)
    (tape : RealSampleTape n) : ℕ :=
  (E.run program algorithm report tape (W.fuel tape)).2

/-- Select expected or uniform almost-sure runtime explicitly. -/
noncomputable def FixedRealExecutionWitness.Within
    {E : RealBlackBoxSchema} {program : Code} {n : ℕ} {O : RealOracle n}
    {algorithm : RealProfile n → Allocation n} {report : RealProfile n}
    {L : FixedRealSampleLaw O} (W : FixedRealExecutionWitness E program algorithm report L)
    (mode : RuntimeConvention) (bound : ℕ) : Prop :=
  match mode with
  | .expected =>
      Integrable (fun tape => (W.cost tape : ℝ)) L.measure ∧
        (∫ tape, (W.cost tape : ℝ) ∂L.measure) ≤ bound
  | .uniformAlmostSure => ∀ᵐ tape ∂L.measure, W.cost tape ≤ bound

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## A concrete exact-real black-box reduction language

One finite arithmetic program accesses only the fixed allocation map, fresh prior
samples and fair bits. No local callback, prior description, feasibility oracle or
output decoder is supplied. Realized allocation and payment vectors are read from the
actual halt buffer. Every buffer scan and copy is charged. This is exact-real
unit-cost computation.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
namespace ExactReal
open ExactRealController MeasureTheory ProbabilityTheory

inductive Operation
  | algorithm
  | prior
  | randomBit
  deriving DecidableEq, Fintype

/-- Algorithm: a=query-start and b=reply-start word registers. Prior: a=reply-start word
register. RandomBit: a=destination word register. -/
abbrev Program := ExactRealController.Program Operation

/-- Write exactly the supplied scalar list; callers validate its range. -/
noncomputable def writeScalars (memory : ℕ → ℝ) (start : ℕ) : List ℝ → ℕ → ℝ
  | [] => memory
  | value :: tail => writeScalars (Function.update memory start value) (start + 1) tail

/-- The first n scalar outputs are allocation coordinates; the next n are signed realized
payments. -/
noncomputable def readOutcome (n : ℕ) (output : List ℝ) : Option (Outcome n) :=
  if output.length = 2 * n then
    some (fun i => (output[i.val]?).getD 0,
      fun i => (output[n + i.val]?).getD 0)
  else none

/-- Actual fixed-instruction execution. Stream cursors belong to the driver. -/
noncomputable def runFrom (width : ℕ) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (tape : RealSampleTape n) :
    ℕ → State → ℕ → ℕ → Option (Outcome n) × ℕ
  | 0, _, _, _ => (none, 0)
  | fuel + 1, state, sampleCursor, bitCursor =>
      let one := ExactRealController.step width program state
      let charge := fun (cost : ℕ) (result : Option (Outcome n) × ℕ) =>
        (result.1, result.2 + cost)
      match one.status with
      | .running => charge one.cost
          (runFrom width program algorithm tape fuel one.state sampleCursor bitCursor)
      | .faulted => (none, one.cost)
      | .halted words reals =>
          (if words.isEmpty then readOutcome n reals else none,
            one.cost + words.length + reals.length + 1)
      | .request .algorithm a b _ _ =>
          let start := one.state.machine.registers a
          let destination := one.state.machine.registers b
          let cost := one.cost + 3 * n + 1
          if start + n ≤ WordRAM.wordModulus width ∧
              destination + n ≤ WordRAM.wordModulus width then
            let report := fun i : Fin n => one.state.memory (start + i.val)
            if h : ∀ i, 0 ≤ report i then
              let reply := algorithm ⟨report, h⟩
              let memory := writeScalars one.state.memory destination (List.ofFn reply)
              charge cost (runFrom width program algorithm tape fuel
                { one.state with memory } sampleCursor bitCursor)
            else (none, cost)
          else (none, cost)
      | .request .prior a _ _ _ =>
          let destination := one.state.machine.registers a
          let cost := one.cost + n + 1
          if destination + n ≤ WordRAM.wordModulus width then
            let memory := writeScalars one.state.memory destination
              (List.ofFn (tape.1 sampleCursor).1)
            charge cost (runFrom width program algorithm tape fuel
              { one.state with memory } (sampleCursor + 1) bitCursor)
          else (none, cost)
      | .request .randomBit a _ _ _ =>
          let next := one.state.setWord width a (if tape.2 bitCursor then 1 else 0)
          charge (one.cost + 1)
            (runFrom width program algorithm tape fuel next sampleCursor (bitCursor + 1))

/-- Input contains only n and the report. Capacity checks prevent truncation; the report,
code and validation costs are paid before the first instruction. -/
noncomputable def run (model : WordRAM.Model) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n)
    (report : RealProfile n) (tape : RealSampleTape n) (fuel : ℕ) :=
  let width := WordRAM.wordWidth model.widthFactor (n + 1)
  let words := [n]
  let reals := List.ofFn report.1
  let cost := initialCost program words reals + 3
  if words.length < WordRAM.wordModulus width ∧
      n < WordRAM.wordModulus width ∧ reals.length ≤ WordRAM.wordModulus width then
    let result := runFrom width program algorithm tape fuel
      (State.initial width words reals) 0 0
    (result.1, result.2 + cost)
  else (none, cost)

/-- A measurable output of the concrete execution, up to a null set of tapes. The output
cannot be an independently chosen expected payment rule. -/
structure ExecutionWitness (model : WordRAM.Model) (program : Program)
    {n : ℕ} {O : RealOracle n} (algorithm : RealProfile n → Allocation n)
    (report : RealProfile n) (L : FixedRealSampleLaw O) where
  fuel : RealSampleTape n → ℕ
  output : RealSampleTape n → Outcome n
  output_measurable : Measurable output
  halts : ∀ᵐ tape ∂L.measure,
    (run model program algorithm report tape (fuel tape)).1 = some (output tape)

noncomputable def ExecutionWitness.cost
    {model : WordRAM.Model} {program : Program} {n : ℕ} {O : RealOracle n}
    {algorithm : RealProfile n → Allocation n} {report : RealProfile n}
    {L : FixedRealSampleLaw O} (W : ExecutionWitness model program algorithm report L)
    (tape : RealSampleTape n) : ℕ :=
  (run model program algorithm report tape (W.fuel tape)).2

noncomputable def ExecutionWitness.Within
    {model : WordRAM.Model} {program : Program} {n : ℕ} {O : RealOracle n}
    {algorithm : RealProfile n → Allocation n} {report : RealProfile n}
    {L : FixedRealSampleLaw O} (W : ExecutionWitness model program algorithm report L)
    (mode : RuntimeConvention) (bound : ℕ) : Prop :=
  match mode with
  | .expected =>
      Integrable (fun tape => (W.cost tape : ℝ)) L.measure ∧
        (∫ tape, (W.cost tape : ℝ) ∂L.measure) ≤ bound
  | .uniformAlmostSure => ∀ᵐ tape ∂L.measure, W.cost tape ≤ bound

/-- One finite program precedes every dimension, prior and fixed algorithm. Its concrete
output law must implement the same correct mechanism for every legal product-tape law.
No trusted local-transition schema is quantified. -/
noncomputable def PolynomialReductionQuestion (mode : RuntimeConvention) : Prop :=
  ∃ model : WordRAM.Model, ∃ program : Program, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ n : ℕ, 0 < n → ∀ O : RealOracle n,
      ∀ algorithm : RealProfile n → Allocation n, IsFixedRealAlgorithm O algorithm →
      Nonempty (FixedRealSampleLaw O) ∧
      ∃ M : Mechanism (RealProfile n) n,
        MeetsRealSpecification O M ∧
        ∀ report : RealProfile n, ∀ L : FixedRealSampleLaw O,
          ∃ W : ExecutionWitness model program algorithm report L,
            Measure.map W.output L.measure = M.outcome report ∧
              W.Within mode (budget n)

end ExactReal
end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Concrete exact-real and bounded rational execution

RealSpecification retains full-real economic correctness and distinguishes fixed
algorithms from fresh-resampling oracles. The primary statement uses a finite
exact-real arithmetic program with fixed algorithm/prior/bit access. The separate
rational statement adopts fresh-resampling and a public response bound B. In both, the
actual output law and runtime refer to the same execution; neither requires computing
an expected payment on every finite run.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open WordRAM.FiniteData

/-- The primary full-real target uses concrete finite syntax and fixed oracle access.
Exact-real unit cost is explicit. -/
noncomputable def BlackBoxDSICExactRealStatement (mode : RuntimeConvention) : Prop :=
  ExactReal.PolynomialReductionQuestion mode

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

/-- Existence of a black-box DSIC reduction under the specified runtime convention. -/
theorem blackBoxDSIC (mode : RuntimeConvention) :
    answer(sorry) ↔ BlackBoxDSICExactRealStatement mode := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
