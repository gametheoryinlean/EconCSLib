/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.BlackBoxDSICMechanismDesign.Problem

/-!
# BlackBoxDSICMechanismDesign: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

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

/-- A semantic candidate on every real oracle. -/
abbrev RealReductionCandidate :=
  (n : ℕ) → RealOracle n → Mechanism (RealProfile n) n

/-- Correctness for all real reports and compatible hidden feasible sets; no IR, MIDR or
universal truthfulness assumption is added. -/
noncomputable def IsRealReductionCorrect (R : RealReductionCandidate) : Prop :=
  ∀ n, 0 < n → ∀ O : RealOracle n, MeetsRealSpecification O (R n O)

/-- The deterministic or once-fixed algorithm convention of GLT, Remark 1. Repeated
queries at a report have the same allocation. -/
def HasFixedRealAlgorithm {n : ℕ} (O : RealOracle n) : Prop :=
  ∃ f : RealProfile n → Allocation n, IsFixedRealAlgorithm O f

/-- Economic correctness for the adopted fixed-algorithm convention. Access and execution
constraints must be supplied separately; the function R alone is not a black-box
implementation. -/
noncomputable def IsFixedRealReductionCorrect (R : RealReductionCandidate) : Prop :=
  ∀ n, 0 < n → ∀ O : RealOracle n, HasFixedRealAlgorithm O →
    MeetsRealSpecification O (R n O)

/-- The next allocation-reply kernel conditional on the current history. -/
def IsConditionalAlgorithmReply {n : ℕ} {History : Type*}
    [MeasurableSpace History] (O : RealOracle n)
    (query : History → RealProfile n)
    (reply : Kernel History (Allocation n)) : Prop :=
  Measurable query ∧ ∀ h, reply h = O.algorithm (query h)

/-- A fresh prior sample has law O.prior conditional on the current history, not just as
an unconditional marginal. -/
def IsConditionalPriorReply {n : ℕ} {History : Type*}
    [MeasurableSpace History] (O : RealOracle n)
    (reply : Kernel History (RealProfile n)) : Prop :=
  ∀ h, reply h = O.prior

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## A separately named rational representation

Reports, realized allocations and payments use fixed structural rational codes. The
full-real economic specification remains separate.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open WordRAM.FiniteData
open MeasureTheory ProbabilityTheory

abbrev RationalProfile (n : ℕ) := {v : Fin n → ℚ // ∀ i, 0 ≤ v i}
abbrev RationalAllocation (n : ℕ) :=
  {x : Fin n → ℚ // ∀ i, 0 ≤ x i ∧ x i ≤ 1}
abbrev RationalOutcome (n : ℕ) := RationalAllocation n × (Fin n → ℚ)

/-- Exactly n nonnegative values, without a prior table, algorithm or feasible set. -/
def reportCode {n : ℕ} (r : RationalProfile n) : Code :=
  tableCode (List.ofFn fun i => Atom.rational (r.1 i))

def allocationCode {n : ℕ} (x : RationalAllocation n) : Code :=
  tableCode (List.ofFn fun i => Atom.rational (x.1 i))

/-- A realized allocation/payment pair, including negative payments. -/
def outcomeCode {n : ℕ} (o : RationalOutcome n) : Code :=
  tableCode ((List.ofFn fun i => Atom.rational (o.1.1 i)) ++
    (List.ofFn fun i => Atom.rational (o.2 i)))

/-- A public response-size bound is supplied once, independently of reports. -/
def requestCode {n : ℕ} (answerBound : ℕ) (r : RationalProfile n) : Code :=
  tableCode ([Atom.integer (Int.ofNat n), Atom.integer (Int.ofNat answerBound)] ++
    (List.ofFn fun i => Atom.rational (r.1 i)) ++
    List.replicate answerBound (Atom.bit false))

noncomputable def rationalValues {n : ℕ} (r : RationalProfile n) : Fin n → ℝ :=
  fun i => (r.1 i : ℝ)

noncomputable def rationalAllocationValues {n : ℕ}
    (x : RationalAllocation n) : Allocation n := fun i => (x.1 i : ℝ)

noncomputable def outcomeDenote {n : ℕ} (o : RationalOutcome n) : Outcome n :=
  (rationalAllocationValues o.1, fun i => (o.2 i : ℝ))

/-- Specification parser for the fixed format at the external-oracle boundary. -/
noncomputable def decodeReportSpec (n : ℕ) (code : Code) : Option (RationalProfile n) := by
  classical
  exact if h : ∃ r : RationalProfile n, reportCode r = code then
    some (Classical.choose h) else none

/-- The rational oracle with its real semantic law. The machine cannot read this semantic
object as input. -/
structure RationalOracle (n : ℕ) where
  semantic : AllocationOracle (RationalProfile n) (@rationalValues n)
  answerLaw : RationalProfile n → Measure (RationalAllocation n)
  answer_probability : ∀ r, IsProbabilityMeasure (answerLaw r)
  answer_measurable : ∀ s : Set (RationalAllocation n), MeasurableSet s →
    Measurable (fun r => answerLaw r s)
  answer_denotes : ∀ r,
    Measure.map (@rationalAllocationValues n) (answerLaw r) = semantic.algorithm r

/-- A common public bound on sample and reply representations. This is an explicit
restriction of the rational adapter. -/
def RationalOracle.HasResponseBitBound {n : ℕ}
    (O : RationalOracle n) (B : ℕ) : Prop :=
  (∀ᵐ r ∂O.semantic.prior, (reportCode r).length ≤ B) ∧
  (∀ r, ∀ᵐ x ∂O.answerLaw r, (allocationCode x).length ≤ B)

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

inductive ExternalOperation
  | algorithmSample
  | priorSample
  deriving DecidableEq, Fintype

/-- Finite operation names; no embedded real seed or solution callback. -/
abbrev Transcript (n : ℕ) :=
  (ℕ → RationalProfile n → RationalAllocation n) ×
  (ℕ → RationalProfile n) × (ℕ → Bool)

inductive RandomSource (n : ℕ)
  | algorithm (serial : ℕ) (report : RationalProfile n)
  | prior (serial : ℕ)
  | bit (serial : ℕ)

def RandomSource.Value {n : ℕ} : RandomSource n → Type
  | .algorithm _ _ => RationalAllocation n
  | .prior _ => RationalProfile n
  | .bit _ => Bool

@[reducible] def RandomSource.valueMeasurableSpace {n : ℕ}
    (source : RandomSource n) : MeasurableSpace source.Value :=
  match source with
  | .algorithm _ _ => (inferInstance : MeasurableSpace (RationalAllocation n))
  | .prior _ => (inferInstance : MeasurableSpace (RationalProfile n))
  | .bit _ => (inferInstance : MeasurableSpace Bool)

def RandomSource.observe {n : ℕ} (source : RandomSource n)
    (t : Transcript n) : source.Value :=
  match source with
  | .algorithm serial r => t.1 serial r
  | .prior serial => t.2.1 serial
  | .bit serial => t.2.2 serial

/-- A semantic law of replies, samples and bits, not machine-readable data. The final
statement requires existence, avoiding quantification over no laws. -/
structure LegalLaw {n : ℕ} (O : RationalOracle n) where
  law : Measure (Transcript n)
  probability : IsProbabilityMeasure law
  sources_independent :
    iIndepFun
      (m := fun source : RandomSource n => source.valueMeasurableSpace)
      (fun source t => RandomSource.observe source t) law
  algorithm_measurable : ∀ serial r,
    Measurable (fun t : Transcript n => t.1 serial r)
  algorithm_law : ∀ serial r,
    Measure.map (fun t : Transcript n => t.1 serial r) law = O.answerLaw r
  prior_measurable : ∀ serial,
    Measurable (fun t : Transcript n => t.2.1 serial)
  prior_law : ∀ serial,
    Measure.map (fun t : Transcript n => t.2.1 serial) law = O.semantic.prior
  bit_measurable : ∀ serial,
    Measurable (fun t : Transcript n => t.2.2 serial)
  bit_law : ∀ serial,
    Measure.map (fun t : Transcript n => t.2.2 serial) law = fairBitMeasure

/-- Only well-typed rational requests and empty sample arguments are accepted. Malformed
queries fault; reply words are checked by Interaction. -/
noncomputable def environment {n : ℕ} (t : Transcript n) :
    WordRAM.Interaction.Environment ExternalOperation where
  query operation serial argument :=
    match operation with
    | .priorSample => none
    | .algorithmSample => do
        let code ← ofWords argument
        let r ← decodeReportSpec n code
        pure (words (allocationCode (t.1 serial r)))
  sample operation serial argument :=
    match operation with
    | .algorithmSample => none
    | .priorSample =>
        if argument.isEmpty then some (words (reportCode (t.2.1 serial))) else none
  randomTape serial := some (t.2.2 serial)

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

structure Simulator where
  model : WordRAM.Model
  program : WordRAM.Interaction.Program ExternalOperation

/-- A witness chooses when to observe a halt and decodes its realized output. The program
cannot read the witness, fuel or semantic oracle law. Nontermination is allowed only
on a null event. -/
structure ExecutionWitness (S : Simulator) {n : ℕ} {O : RationalOracle n}
    (B : ℕ) (r : RationalProfile n) (L : LegalLaw O) where
  fuel : Transcript n → ℕ
  output : Transcript n → RationalOutcome n
  realized_measurable : Measurable (fun t => outcomeDenote (output t))
  halts : ∀ᵐ t ∂L.law,
    (WordRAM.Interaction.run S.model (environment t) S.program (fuel t)
      (requestCode B r)).termination = .halted (words (outcomeCode (output t)))

noncomputable def ExecutionWitness.execution {S : Simulator} {n B : ℕ}
    {O : RationalOracle n} {r : RationalProfile n} {L : LegalLaw O}
    (W : ExecutionWitness S B r L) (t : Transcript n) : WordRAM.Interaction.Result :=
  WordRAM.Interaction.run S.model (environment t) S.program (W.fuel t)
    (requestCode B r)

/-- The interpreter cost. -/
noncomputable def ExecutionWitness.cost {S : Simulator} {n B : ℕ}
    {O : RationalOracle n} {r : RationalProfile n} {L : LegalLaw O}
    (W : ExecutionWitness S B r L) (t : Transcript n) : ℕ :=
  (W.execution t).cost

/-- The pushforward law of the joint allocation/payment from that execution. -/
noncomputable def ExecutionWitness.outputLaw {S : Simulator} {n B : ℕ}
    {O : RationalOracle n} {r : RationalProfile n} {L : LegalLaw O}
    (W : ExecutionWitness S B r L) : Measure (Outcome n) :=
  Measure.map (fun t => outcomeDenote (W.output t)) L.law

/-- Specify which random runtime quantity is bounded without changing the shared
polynomial predicate. -/
noncomputable def ExecutionWitness.Within {S : Simulator} {n B : ℕ}
    {O : RationalOracle n} {r : RationalProfile n} {L : LegalLaw O}
    (W : ExecutionWitness S B r L) (convention : RuntimeConvention) (bound : ℕ) : Prop :=
  match convention with
  | .uniformAlmostSure => ∀ᵐ t ∂L.law, W.cost t ≤ bound
  | .expected =>
      Integrable (fun t => (W.cost t : ℝ)) L.law ∧
        (∫ t, (W.cost t : ℝ) ∂L.law) ≤ (bound : ℝ)

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

/-- Once a run halts, extra fuel changes neither its realized outcome nor its cost. -/
theorem RealBlackBoxSchema.runFrom_add_fuel_of_halts (E : RealBlackBoxSchema)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (tape : RealSampleTape n)
    (fuel extra : ℕ) (state : E.State n) (sampleCursor bitCursor : ℕ)
    (outcome : Outcome n)
    (halts : (E.runFrom algorithm tape fuel state sampleCursor bitCursor).1 = some outcome) :
    E.runFrom algorithm tape (fuel + extra) state sampleCursor bitCursor =
      E.runFrom algorithm tape fuel state sampleCursor bitCursor := by
  induction fuel generalizing state sampleCursor bitCursor with
  | zero => simp [runFrom] at halts
  | succ fuel ih =>
      cases command : E.step state with
      | halt output => simp [Nat.succ_add, runFrom, command]
      | «local» next =>
          simp only [Nat.succ_add, runFrom, command] at halts ⊢
          rw [ih next sampleCursor bitCursor halts]
      | algorithm report next =>
          simp only [Nat.succ_add, runFrom, command] at halts ⊢
          rw [ih (next (algorithm report)) sampleCursor bitCursor halts]
      | samplePrior next =>
          simp only [Nat.succ_add, runFrom, command] at halts ⊢
          rw [ih (next (tape.1 sampleCursor)) (sampleCursor + 1) bitCursor halts]
      | randomBit next =>
          simp only [Nat.succ_add, runFrom, command] at halts ⊢
          rw [ih (next (tape.2 bitCursor)) sampleCursor (bitCursor + 1) halts]

/-- Public initialization accounting is also invariant under extra post-halt fuel. -/
theorem RealBlackBoxSchema.run_add_fuel_of_halts (E : RealBlackBoxSchema)
    (program : Code) {n : ℕ} (algorithm : RealProfile n → Allocation n)
    (report : RealProfile n) (tape : RealSampleTape n) (fuel extra : ℕ)
    (outcome : Outcome n)
    (halts : (E.run program algorithm report tape fuel).1 = some outcome) :
    E.run program algorithm report tape (fuel + extra) =
      E.run program algorithm report tape fuel := by
  have stable := E.runFrom_add_fuel_of_halts algorithm tape fuel extra
    (E.initial program report) 0 0 outcome halts
  simp only [run, stable]

/-- Full-real fixed-algorithm target relative to E. A single finite program and polynomial
budget work for all priors and algorithms. The mechanism is chosen before the report
and tape law. E already contains measurable state, observation, and continuation
contracts. -/
noncomputable def FixedRealBlackBoxExecutionSchemaQuestion
    (E : RealBlackBoxSchema) (mode : RuntimeConvention) : Prop :=
  ∃ program : Code, ∃ budget : ℕ → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial id budget ∧
    ∀ n : ℕ, 0 < n → ∀ O : RealOracle n,
      ∀ algorithm : RealProfile n → Allocation n, IsFixedRealAlgorithm O algorithm →
      Nonempty (FixedRealSampleLaw O) ∧
      ∃ M : Mechanism (RealProfile n) n,
        MeetsRealSpecification O M ∧
        ∀ report : RealProfile n, ∀ L : FixedRealSampleLaw O,
          ∃ W : FixedRealExecutionWitness E program algorithm report L,
            Measure.map W.output L.measure = M.outcome report ∧
              W.Within mode (budget n)

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

/-- Extra fuel after termination cannot select a different output or cost. -/
theorem runFrom_add_fuel_of_halts (width : ℕ) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (tape : RealSampleTape n)
    (fuel extra : ℕ) (state : State) (sampleCursor bitCursor : ℕ) (outcome : Outcome n)
    (halts : (runFrom width program algorithm tape fuel state sampleCursor bitCursor).1 =
      some outcome) :
    runFrom width program algorithm tape (fuel + extra) state sampleCursor bitCursor =
      runFrom width program algorithm tape fuel state sampleCursor bitCursor := by
  induction fuel generalizing state sampleCursor bitCursor with
  | zero => simp [runFrom] at halts
  | succ fuel ih =>
      cases status : (ExactRealController.step width program state).status with
      | running =>
          simp only [Nat.succ_add, runFrom, status] at halts ⊢
          rw [ih _ _ _ halts]
      | faulted => simp [Nat.succ_add, runFrom, status]
      | halted words reals => simp [Nat.succ_add, runFrom, status]
      | request operation a b c d =>
          cases operation with
          | algorithm =>
              simp only [Nat.succ_add, runFrom, status] at halts ⊢
              split at halts
              next fits =>
                simp only [if_pos fits]
                split at halts
                next nonnegative =>
                  simp only [dif_pos nonnegative]
                  rw [ih _ _ _ halts]
                next invalid => simp at halts
              next invalid => simp at halts
          | prior =>
              simp only [Nat.succ_add, runFrom, status] at halts ⊢
              split at halts
              next fits =>
                simp only [if_pos fits]
                rw [ih _ _ _ halts]
              next invalid => simp at halts
          | randomBit =>
              simp only [Nat.succ_add, runFrom, status] at halts ⊢
              rw [ih _ _ _ halts]

/-- Initialization and its fixed validation cost are independent of fuel. -/
theorem run_add_fuel_of_halts (model : WordRAM.Model) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (report : RealProfile n)
    (tape : RealSampleTape n) (fuel extra : ℕ) (outcome : Outcome n)
    (halts : (run model program algorithm report tape fuel).1 = some outcome) :
    run model program algorithm report tape (fuel + extra) =
      run model program algorithm report tape fuel := by
  simp only [run] at halts ⊢
  split at halts
  next fits =>
    simp only [if_pos fits]
    rw [runFrom_add_fuel_of_halts _ _ _ _ _ _ _ _ _ _ halts]
  next invalid => simp at halts

end ExactReal
end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Finite-prefix causality of the concrete black-box interpreter

A fuel-bounded run reads only the corresponding finite prefixes of the prior and coin
streams. The conclusion covers both actual output and charged cost. This deterministic
statement uses no probability or measurability assumptions and does not assert a
conditional fresh-sampling theorem.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
namespace ExactReal
open ExactRealController

/-- Agreement on the two source intervals reachable within the given fuel. -/
structure SourcePrefixAgreement {n : ℕ} (left right : RealSampleTape n)
    (sampleCursor bitCursor fuel : ℕ) : Prop where
  prior : ∀ serial, sampleCursor ≤ serial → serial < sampleCursor + fuel →
    left.1 serial = right.1 serial
  bit : ∀ serial, bitCursor ≤ serial → serial < bitCursor + fuel →
    left.2 serial = right.2 serial

/-- Restrict each agreed interval to a smaller interval. -/
theorem SourcePrefixAgreement.restrict {n : ℕ} {left right : RealSampleTape n}
    {sampleCursor bitCursor fuel nextSample nextBit nextFuel : ℕ}
    (h : SourcePrefixAgreement left right sampleCursor bitCursor fuel)
    (sampleLower : sampleCursor ≤ nextSample)
    (sampleUpper : nextSample + nextFuel ≤ sampleCursor + fuel)
    (bitLower : bitCursor ≤ nextBit)
    (bitUpper : nextBit + nextFuel ≤ bitCursor + fuel) :
    SourcePrefixAgreement left right nextSample nextBit nextFuel where
  prior serial lower upper := h.prior serial (by omega) (by omega)
  bit serial lower upper := h.bit serial (by omega) (by omega)

/-- No fuel-bounded execution can inspect sources beyond either agreed prefix. -/
theorem runFrom_eq_of_sourcePrefixAgreement (width : ℕ) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n)
    (left right : RealSampleTape n) (fuel : ℕ) (state : State)
    (sampleCursor bitCursor : ℕ)
    (agree : SourcePrefixAgreement left right sampleCursor bitCursor fuel) :
    runFrom width program algorithm left fuel state sampleCursor bitCursor =
      runFrom width program algorithm right fuel state sampleCursor bitCursor := by
  induction fuel generalizing state sampleCursor bitCursor with
  | zero => rfl
  | succ fuel ih =>
      have rest : SourcePrefixAgreement left right sampleCursor bitCursor fuel :=
        agree.restrict (by omega) (by omega) (by omega) (by omega)
      cases status : (ExactRealController.step width program state).status with
      | running =>
          simp only [runFrom, status]
          rw [ih _ _ _ rest]
      | faulted => simp only [runFrom, status]
      | halted words reals => simp only [runFrom, status]
      | request operation a b c d =>
          cases operation with
          | algorithm =>
              simp only [runFrom, status]
              split
              next fits =>
                split
                next nonnegative =>
                  rw [ih _ _ _ rest]
                next invalid => rfl
              next invalid => rfl
          | prior =>
              simp only [runFrom, status]
              split
              next fits =>
                rw [agree.prior sampleCursor (by omega) (by omega)]
                rw [ih _ _ _ (agree.restrict (by omega) (by omega) (by omega) (by omega))]
              next invalid => rfl
          | randomBit =>
              simp only [runFrom, status]
              rw [agree.bit bitCursor (by omega) (by omega)]
              rw [ih _ _ _ (agree.restrict (by omega) (by omega) (by omega) (by omega))]

/-- Public initialization does not add any prior or coin access. -/
theorem run_eq_of_prefix (model : WordRAM.Model) (program : Program)
    {n : ℕ} (algorithm : RealProfile n → Allocation n) (report : RealProfile n)
    (left right : RealSampleTape n) (fuel : ℕ)
    (prior : ∀ serial < fuel, left.1 serial = right.1 serial)
    (bits : ∀ serial < fuel, left.2 serial = right.2 serial) :
    run model program algorithm report left fuel =
      run model program algorithm report right fuel := by
  have agree : SourcePrefixAgreement left right 0 0 fuel :=
    ⟨fun serial _ upper => prior serial (by simpa using upper),
      fun serial _ upper => bits serial (by simpa using upper)⟩
  simp only [run]
  split
  next fits =>
    rw [runFrom_eq_of_sourcePrefixAgreement _ _ _ _ _ _ _ _ _ agree]
  next invalid => rfl

end ExactReal
end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Existence of the independent real sample law

The dependent infinite product supplies all prior and coin coordinates. Measurable
repacking preserves every marginal and their joint independence. Thus law nonemptiness
in the execution question imposes no extra prior promise.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open MeasureTheory ProbabilityTheory

/-- Every valid real oracle admits the exact product-tape law required by the interpreter,
without finite-support or additional regularity assumptions. -/
theorem FixedRealSampleLaw.nonempty {n : ℕ} (O : RealOracle n) :
    Nonempty (FixedRealSampleLaw O) := by
  classical
  letI : IsProbabilityMeasure O.prior := O.probability
  have bitProbability : IsProbabilityMeasure fairBitMeasure := by
    constructor
    norm_num [fairBitMeasure, Measure.add_apply, Measure.smul_apply]
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure fairBitMeasure := bitProbability
  letI sourceSpace : (source : RealRandomSource) → MeasurableSpace (source.Value n) :=
    fun source => RealRandomSource.valueMeasurableSpace n source
  let marginal : (source : RealRandomSource) → Measure (source.Value n) :=
    fun source => match source with
      | .prior _ => O.prior
      | .bit _ => fairBitMeasure
  have marginalProbability : ∀ source, IsProbabilityMeasure (marginal source) := by
    intro source
    cases source with
    | prior serial => exact O.probability
    | bit serial => exact bitProbability
  letI : ∀ source, IsProbabilityMeasure (marginal source) := marginalProbability
  let pack : ((source : RealRandomSource) → source.Value n) → RealSampleTape n :=
    fun sample => (fun serial => sample (.prior serial), fun serial => sample (.bit serial))
  have packMeasurable : Measurable pack := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun serial => measurable_pi_apply (RealRandomSource.prior serial))
    · exact measurable_pi_lambda _ (fun serial => measurable_pi_apply (RealRandomSource.bit serial))
  have observeMeasurable : ∀ source,
      Measurable (fun tape : RealSampleTape n => RealRandomSource.observe source tape) := by
    intro source
    cases source with
    | prior serial => exact (measurable_pi_apply serial).comp measurable_fst
    | bit serial => exact (measurable_pi_apply serial).comp measurable_snd
  let law := (Measure.infinitePi marginal).map pack
  have lawProbability : IsProbabilityMeasure law :=
    Measure.isProbabilityMeasure_map packMeasurable.aemeasurable
  letI : IsProbabilityMeasure law := lawProbability
  have lawMarginal : ∀ source,
      law.map (fun tape => RealRandomSource.observe source tape) = marginal source := by
    intro source
    dsimp [law]
    rw [Measure.map_map (observeMeasurable source) packMeasurable]
    convert Measure.infinitePi_map_eval marginal source using 1
    congr 1
    funext sample
    cases source <;> rfl
  have lawIndependent : iIndepFun
      (m := fun source => RealRandomSource.valueMeasurableSpace n source)
      (fun source tape => RealRandomSource.observe source tape) law := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map observeMeasurable]
    simp_rw [lawMarginal]
    dsimp [law]
    rw [Measure.map_map (measurable_pi_lambda _ observeMeasurable) packMeasurable]
    have inverse : (fun tape source => RealRandomSource.observe source tape) ∘ pack = id := by
      funext sample source
      cases source <;> rfl
    rw [inverse, Measure.map_id]
  exact ⟨{
    measure := law
    probability := lawProbability
    independent := lawIndependent
    prior_measurable := fun serial => (measurable_pi_apply serial).comp measurable_fst
    prior_law := fun serial => lawMarginal (.prior serial)
    bit_measurable := fun serial => (measurable_pi_apply serial).comp measurable_snd
    bit_law := fun serial => lawMarginal (.bit serial)
  }⟩

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end


section

/-!
## Uniqueness of the fresh-sample law

Joint independence and the specified marginals determine the entire tape measure. The
law witness cannot encode additional correlations or choose a different execution
distribution. This is distinct from a stopping-time conditional-sampling theorem for a
concrete adaptive interpreter.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign
open MeasureTheory ProbabilityTheory

/-- Repack the dependent source coordinates into the two interpreter streams. -/
def packRealSources {n : ℕ} (sample : (source : RealRandomSource) → source.Value n) :
    RealSampleTape n :=
  (fun serial => sample (.prior serial), fun serial => sample (.bit serial))

/-- Every source is observable by its fixed coordinate projection. -/
theorem measurable_observe {n : ℕ} (source : RealRandomSource) :
    @Measurable _ _ _ (RealRandomSource.valueMeasurableSpace n source)
      (fun tape : RealSampleTape n => RealRandomSource.observe source tape) := by
  cases source with
  | prior serial => exact (measurable_pi_apply serial).comp measurable_fst
  | bit serial => exact (measurable_pi_apply serial).comp measurable_snd

/-- No freedom remains in the joint law after all independent marginals are fixed. -/
theorem FixedRealSampleLaw.measure_eq {n : ℕ} {O : RealOracle n}
    (L R : FixedRealSampleLaw O) : L.measure = R.measure := by
  classical
  letI : IsProbabilityMeasure L.measure := L.probability
  letI : IsProbabilityMeasure R.measure := R.probability
  letI sourceSpace : (source : RealRandomSource) → MeasurableSpace (source.Value n) :=
    fun source => RealRandomSource.valueMeasurableSpace n source
  let observe : RealSampleTape n → (source : RealRandomSource) → source.Value n :=
    fun tape source => RealRandomSource.observe source tape
  have observeMeasurable : Measurable observe :=
    measurable_pi_lambda _ (fun source => measurable_observe source)
  have packMeasurable : Measurable (packRealSources (n := n)) := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun serial => measurable_pi_apply (RealRandomSource.prior serial))
    · exact measurable_pi_lambda _ (fun serial => measurable_pi_apply (RealRandomSource.bit serial))
  have leftLaw := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun source => measurable_observe (n := n) source)).mp L.independent
  have rightLaw := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun source => measurable_observe (n := n) source)).mp R.independent
  have marginals : ∀ source,
      L.measure.map (fun tape => RealRandomSource.observe source tape) =
        R.measure.map (fun tape => RealRandomSource.observe source tape) := by
    intro source
    cases source with
    | prior serial => exact (L.prior_law serial).trans (R.prior_law serial).symm
    | bit serial => exact (L.bit_law serial).trans (R.bit_law serial).symm
  have observed : L.measure.map observe = R.measure.map observe := by
    dsimp [observe]
    rw [leftLaw, rightLaw]
    simp_rw [marginals]
  have packed := congrArg (Measure.map (packRealSources (n := n))) observed
  rw [Measure.map_map packMeasurable observeMeasurable,
    Measure.map_map packMeasurable observeMeasurable] at packed
  have inverse : packRealSources ∘ observe = id := by
    funext tape
    cases tape
    rfl
  simpa only [inverse, Measure.map_id] using packed

/-- Proof fields add no extra mathematical choice to the unique product law. -/
instance {n : ℕ} (O : RealOracle n) : Subsingleton (FixedRealSampleLaw O) where
  allEq L R := by
    have h := L.measure_eq R
    cases L
    cases R
    cases h
    rfl

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

/-- A uniform rational fresh-sampling simulator with a public reply-size bound. The
promise B is not part of the hidden algorithm or prior. -/
noncomputable def BlackBoxDSICBoundedRationalSampleStatement
    (convention : RuntimeConvention) : Prop :=
  ∃ S : Simulator, ∃ costBound : Code → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
      (bitSize S.model) costBound ∧
    ∀ n : ℕ, 0 < n → ∀ O : RationalOracle n,
      ∀ B : ℕ, O.HasResponseBitBound B →
        Nonempty (LegalLaw O) ∧
        ∃ M : Mechanism (RationalProfile n) n,
          MeetsSpecification O.semantic M ∧
          ∀ r : RationalProfile n, ∀ L : LegalLaw O,
            ∃ W : ExecutionWitness S B r L,
              W.outputLaw = M.outcome r ∧
              W.Within convention (costBound (requestCode B r))

end EconCSLib.OpenProblem.New.EconCSBench.BlackBoxDSICMechanismDesign

end
