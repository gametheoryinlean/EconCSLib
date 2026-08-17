/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Probability.Independence.Basic

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.BlackBoxDSICMechanismDesign

open MeasureTheory ProbabilityTheory

/-- The advertised nonnegative single-parameter report domain. -/
abbrev NonnegativeProfile (I : Type*) :=
  {values : I → ℝ // ∀ i, 0 ≤ values i}

/-- Replace one coordinate while staying inside the nonnegative report domain. -/
def updateNonnegativeProfile
    {I : Type*} [DecidableEq I]
    (values : NonnegativeProfile I) (i : I) (fake : ℝ) (hfake : 0 ≤ fake) :
    NonnegativeProfile I :=
  ⟨Function.update values.1 i fake, by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hfake
    · simpa [Function.update, hji] using values.2 j⟩

/-- The information genuinely visible to a black-box simulator: independent
nonnegative single-parameter values, their prior, and oracle access to an
allocation algorithm.  The feasibility set is intentionally absent. -/
structure BlackBoxWelfareOracle
    (I : Type*) [Fintype I] [DecidableEq I] where
  /-- Joint prior over real-valued type profiles. -/
  prior : Measure (NonnegativeProfile I)
  /-- The prior has total mass one. -/
  probability : IsProbabilityMeasure prior
  /-- Agent values are independent. -/
  independent : iIndepFun (fun i values => values.1 i) prior
  /-- Report-dependent output law of the allocation algorithm available
  through oracle calls.  This includes the internal randomness explicitly,
  as required by the Markdown. -/
  algorithm : NonnegativeProfile I → Measure (I → ℝ)
  /-- Every oracle call returns a probability law. -/
  algorithm_probability :
    ∀ reports, IsProbabilityMeasure (algorithm reports)
  /-- Allocation coordinates are probabilities/fractions almost surely. -/
  allocation_mem_unit :
    ∀ reports, ∀ᵐ allocation ∂algorithm reports,
      ∀ i, 0 ≤ allocation i ∧ allocation i ≤ 1
  /-- The original algorithm's welfare is integrable under the prior. -/
  welfare_integrable :
    Integrable
      (fun values =>
        ∫ allocation, ∑ i, values.1 i * allocation i
          ∂algorithm values)
      prior

/-- A hidden feasibility set compatible with the observed allocation oracle.
The simulator never receives this object. -/
structure CompatibleFeasibility
    {I : Type*} [Fintype I] [DecidableEq I]
    (oracle : BlackBoxWelfareOracle I) where
  /-- Hidden feasibility constraint. -/
  Feasible : Set (I → ℝ)
  /-- Every realized oracle answer is feasible. -/
  algorithm_feasible :
    ∀ reports, ∀ᵐ allocation ∂oracle.algorithm reports,
      allocation ∈ Feasible

/-- Welfare of a fractional allocation at a value profile. -/
noncomputable def fractionalWelfare
    {I : Type*} [Fintype I]
    (types allocation : I → ℝ) : ℝ :=
  ∑ i, types i * allocation i

/-- Expected welfare of the original black-box algorithm. -/
noncomputable def algorithmExpectedWelfare
    {I : Type*} [Fintype I] [DecidableEq I]
    (problem : BlackBoxWelfareOracle I) : ℝ :=
  ∫ types,
    ∫ allocation, fractionalWelfare types.1 allocation
      ∂problem.algorithm types ∂problem.prior

/-- A randomized direct single-parameter mechanism.  A report profile induces
an arbitrary probability measure on fractional allocations; this does not add
the unmentioned restriction that one finite seed space must work uniformly for
every oracle instance. -/
structure RandomizedSingleParameterMechanism
    (I : Type*) [Fintype I] where
  /-- Report-dependent distribution over realized allocations. -/
  allocation : NonnegativeProfile I → Measure (I → ℝ)
  /-- Internal randomization has total mass one. -/
  allocation_probability :
    ∀ reports, IsProbabilityMeasure (allocation reports)
  /-- Every allocation coordinate has a well-defined finite expectation. -/
  allocation_integrable :
    ∀ reports i, Integrable (fun x : I → ℝ => x i) (allocation reports)
  /-- Expected payment charged to each agent. -/
  payment : NonnegativeProfile I → I → ℝ

/-- Expected allocated fraction of one agent. -/
noncomputable def RandomizedSingleParameterMechanism.expectedAllocation
    {I : Type*} [Fintype I]
    (mechanism : RandomizedSingleParameterMechanism I)
    (reports : NonnegativeProfile I) (i : I) : ℝ :=
  ∫ allocation, allocation i ∂mechanism.allocation reports

/-- DSIC in expected utility for a randomized direct mechanism produced by the
simulator.  Both truthful and deviating reports remain in the nonnegative
single-parameter domain. -/
noncomputable def IsSingleParameterDSIC
    {I : Type*} [Fintype I] [DecidableEq I]
    (mechanism : RandomizedSingleParameterMechanism I) : Prop :=
  ∀ trueTypes i fake, ∀ hfake : 0 ≤ fake,
      trueTypes.1 i * mechanism.expectedAllocation trueTypes i -
          mechanism.payment trueTypes i ≥
        trueTypes.1 i *
            mechanism.expectedAllocation
              (updateNonnegativeProfile trueTypes i fake hfake) i -
          mechanism.payment
            (updateNonnegativeProfile trueTypes i fake hfake) i

/-- Expected welfare of a direct mechanism under truthful reports. -/
noncomputable def mechanismExpectedWelfare
    {I : Type*} [Fintype I] [DecidableEq I]
    (problem : BlackBoxWelfareOracle I)
    (mechanism : RandomizedSingleParameterMechanism I) : ℝ :=
  ∫ types,
    ∫ allocation, fractionalWelfare types.1 allocation
      ∂mechanism.allocation types ∂problem.prior

/-! ## Uniform mathematical reduction -/

/-- A single mathematical black-box reduction for all finite dimensions.
Using `Fin n` is only a canonical labeling of an arbitrary finite agent set;
it also makes the dimension part of the operational input instead of choosing
one unrelated program for every finite type. -/
structure WelfarePreservingBlackBoxReduction where
  /-- Simulator output on an oracle instance of any finite dimension. -/
  simulate :
    (n : ℕ) → BlackBoxWelfareOracle (Fin n) →
      RandomizedSingleParameterMechanism (Fin n)
  /-- The same simulator output is feasible for every hidden feasibility set
  compatible with the observed oracle. -/
  feasible :
    ∀ n, 0 < n →
      ∀ (problem : BlackBoxWelfareOracle (Fin n))
        (hidden : CompatibleFeasibility problem) reports,
        ∀ᵐ allocation ∂(simulate n problem).allocation reports,
          allocation ∈ hidden.Feasible
  /-- The simulated allocation is fractional almost surely. -/
  allocation_mem_unit :
    ∀ n, 0 < n →
      ∀ (problem : BlackBoxWelfareOracle (Fin n)) reports,
        ∀ᵐ allocation ∂(simulate n problem).allocation reports,
          ∀ i, 0 ≤ allocation i ∧ allocation i ≤ 1
  /-- The simulated direct mechanism is DSIC. -/
  dsic :
    ∀ n, 0 < n → ∀ problem,
      IsSingleParameterDSIC (simulate n problem)
  /-- The simulated welfare is integrable, so the Bochner integral does not
  silently collapse a nonintegrable objective to Lean's default value. -/
  output_integrable :
    ∀ n, 0 < n →
      ∀ problem,
        Integrable
          (fun values =>
            ∫ allocation, fractionalWelfare values.1 allocation
              ∂(simulate n problem).allocation values)
          problem.prior
  /-- Expected welfare is not below that of the oracle algorithm. -/
  preservesExpectedWelfare :
    ∀ n, 0 < n →
      ∀ problem,
        algorithmExpectedWelfare problem ≤
          mechanismExpectedWelfare problem (simulate n problem)

/-! ## Canonical online interface for the strict RAM program -/

/-- The only external capabilities available to the simulator: sample the
allocation algorithm at an encoded report, or sample the known prior. -/
inductive BlackBoxExternalOperation
  | algorithmSample
  | priorSample

/-- Structural exact-real words for a finite vector. -/
def profileWords {n : ℕ} (values : Fin n → ℝ) : List UnitCostRAM.Word :=
  List.ofFn fun i => .real (values i)

private theorem profileWords_injective {n : ℕ} :
    Function.Injective (@profileWords n) := by
  intro left right hwords
  have hfunctions :
      (fun i : Fin n => UnitCostRAM.Word.real (left i)) =
        fun i : Fin n => UnitCostRAM.Word.real (right i) :=
    List.ofFn_injective hwords
  funext i
  exact UnitCostRAM.Word.real.inj (congrFun hfunctions i)

private theorem nonnegativeProfileWords_injective {n : ℕ} :
    Function.Injective
      (fun values : NonnegativeProfile (Fin n) => profileWords values.1) := by
  intro left right hwords
  exact Subtype.ext (profileWords_injective hwords)

/-- Fixed decoder for a canonically encoded nonnegative profile.  The
classical inverse is used only to recognize the structural word format; the
strict program still pays for every transferred word. -/
noncomputable def decodeNonnegativeProfileWords
    (n : ℕ) (words : List UnitCostRAM.Word) :
    Option (NonnegativeProfile (Fin n)) := by
  classical
  exact
    if h : ∃ values : NonnegativeProfile (Fin n),
        profileWords values.1 = words then
      some (Classical.choose h)
    else
      none

@[simp] theorem decodeNonnegativeProfileWords_profileWords
    {n : ℕ} (values : NonnegativeProfile (Fin n)) :
    decodeNonnegativeProfileWords n (profileWords values.1) = some values := by
  classical
  unfold decodeNonnegativeProfileWords
  split
  next h =>
    congr 1
    exact nonnegativeProfileWords_injective (Classical.choose_spec h)
  next h => exact False.elim (h ⟨values, rfl⟩)

/-- Canonical argument of a numbered allocation-algorithm sample. -/
def algorithmSampleQueryWords
    {n : ℕ} (sampleNumber : ℕ)
    (reports : NonnegativeProfile (Fin n)) : List UnitCostRAM.Word :=
  .integer sampleNumber :: profileWords reports.1

/-- Decode only canonical algorithm-sample arguments. -/
noncomputable def decodeAlgorithmSampleQuery
    (n : ℕ) (words : List UnitCostRAM.Word) :
    Option (ℕ × NonnegativeProfile (Fin n)) :=
  match words with
  | .integer sampleNumber :: reports =>
      if 0 ≤ sampleNumber then
        (decodeNonnegativeProfileWords n reports).map
          (fun profile => (sampleNumber.toNat, profile))
      else
        none
  | _ => none

@[simp] theorem decodeAlgorithmSampleQuery_queryWords
    {n : ℕ} (sampleNumber : ℕ)
    (reports : NonnegativeProfile (Fin n)) :
    decodeAlgorithmSampleQuery n
        (algorithmSampleQueryWords sampleNumber reports) =
      some (sampleNumber, reports) := by
  simp [decodeAlgorithmSampleQuery, algorithmSampleQueryWords]

/-- Decode the one-word argument of a prior sample. -/
def decodePriorSampleQuery : List UnitCostRAM.Word → Option ℕ
  | [.integer sampleNumber] =>
      if 0 ≤ sampleNumber then some sampleNumber.toNat else none
  | _ => none

/-- The ordinary machine input is one report vector.  Its explicit dimension
is retained even for malformed inputs, so the choice/oracle type is fixed
before the program witness. -/
structure BlackBoxMachineRequest where
  agentCount : ℕ
  reports : List ℝ

/-- Canonical structural encoding of a mechanism invocation. -/
def blackBoxMachineRequestWords
    (request : BlackBoxMachineRequest) : List UnitCostRAM.Word :=
  .integer request.agentCount :: request.reports.map .real

private theorem blackBoxMachineRequestWords_injective :
    Function.Injective blackBoxMachineRequestWords := by
  intro left right hwords
  have hhead := (List.cons.inj hwords).1
  have htail := (List.cons.inj hwords).2
  have hcountInt := UnitCostRAM.Word.integer.inj hhead
  have hcount : left.agentCount = right.agentCount := by
    exact_mod_cast hcountInt
  have realWord_injective :
      Function.Injective
        (UnitCostRAM.Word.real : ℝ → UnitCostRAM.Word) := by
    intro x y h
    exact UnitCostRAM.Word.real.inj h
  have hreports : left.reports = right.reports :=
    (List.map_injective_iff.2 realWord_injective) htail
  cases left
  cases right
  simp_all

/-- The fixed lossless request encoding used by the strict certificate. -/
noncomputable def blackBoxMachineRequestEncoding :
    UnitCostRAM.Encoding BlackBoxMachineRequest := by
  classical
  refine
    { encode := blackBoxMachineRequestWords
      decode := fun words =>
        if h : ∃ request, blackBoxMachineRequestWords request = words then
          some (Classical.choose h)
        else
          none
      decode_encode := ?_ }
  intro request
  split
  next h =>
    congr 1
    exact blackBoxMachineRequestWords_injective (Classical.choose_spec h)
  next h => exact False.elim (h ⟨request, rfl⟩)

/-- A complete table of answers selected for one execution.  Numbered sample
coordinates make repeated calls explicit instead of letting one opaque
callback hide an adaptive transcript. -/
structure BlackBoxOracleTranscript (n : ℕ) where
  algorithmAnswer :
    ℕ → NonnegativeProfile (Fin n) → Fin n → ℝ
  priorAnswer : ℕ → NonnegativeProfile (Fin n)
  randomTape : ℕ → Bool

/-- Product/cylinder measurable structure generated by all observable
algorithm-answer, prior-answer, and random-bit coordinates.  In particular,
this is not the full powerset measurable space, which would rule out ordinary
continuous transcript laws on standard set-theoretic foundations. -/
instance instMeasurableSpaceBlackBoxOracleTranscript (n : ℕ) :
    MeasurableSpace (BlackBoxOracleTranscript n) :=
  MeasurableSpace.comap
    (fun transcript =>
      (transcript.algorithmAnswer,
        transcript.priorAnswer, transcript.randomTape))
    inferInstance

/-- One coordinate of all randomness visible to the simulator. -/
inductive BlackBoxRandomSource (n : ℕ)
  | algorithm
      (sampleNumber : ℕ) (reports : NonnegativeProfile (Fin n))
  | prior (sampleNumber : ℕ)
  | bit (bitNumber : ℕ)

/-- Observable type carried by each random-source coordinate. -/
def BlackBoxRandomSource.Value {n : ℕ} :
    BlackBoxRandomSource n → Type
  | .algorithm _ _ => Fin n → ℝ
  | .prior _ => NonnegativeProfile (Fin n)
  | .bit _ => Bool

/-- The ordinary measurable structure on each observable coordinate. -/
@[reducible] def BlackBoxRandomSource.valueMeasurableSpace
    {n : ℕ} (source : BlackBoxRandomSource n) :
    MeasurableSpace source.Value :=
  match source with
  | .algorithm _ _ =>
      (inferInstance : MeasurableSpace (Fin n → ℝ))
  | .prior _ =>
      (inferInstance : MeasurableSpace (NonnegativeProfile (Fin n)))
  | .bit _ => (inferInstance : MeasurableSpace Bool)

/-- A machine choice contains at most one oracle instance of the request's
dimension and the full external-answer transcript.  `none` supplies a
harmless choice for malformed inputs; legal execution laws are concentrated
on `some problem`. -/
structure BlackBoxExecutionChoice (request : BlackBoxMachineRequest) where
  problem : Option (BlackBoxWelfareOracle (Fin request.agentCount))
  transcript : BlackBoxOracleTranscript request.agentCount

/-- The execution-choice sigma algebra is the product of a discrete problem
tag and the transcript's cylinder sigma algebra.  Legal laws put a Dirac mass
on the problem tag, while continuous randomness remains confined to the
ordinary product-measurable transcript coordinates. -/
instance instMeasurableSpaceBlackBoxExecutionChoice
    (request : BlackBoxMachineRequest) :
    MeasurableSpace (BlackBoxExecutionChoice request) :=
  MeasurableSpace.comap
    (fun choice => (choice.problem, choice.transcript))
    ((⊤ : MeasurableSpace
      (Option (BlackBoxWelfareOracle (Fin request.agentCount)))).prod
        inferInstance)

/-- Read one coordinate from a transcript. -/
def BlackBoxRandomSource.observe
    {request : BlackBoxMachineRequest}
    (source : BlackBoxRandomSource request.agentCount)
    (choice : BlackBoxExecutionChoice request) : source.Value :=
  match source with
  | .algorithm sampleNumber reports =>
      choice.transcript.algorithmAnswer sampleNumber reports
  | .prior sampleNumber => choice.transcript.priorAnswer sampleNumber
  | .bit bitNumber => choice.transcript.randomTape bitNumber

/-- The fair law of one machine random bit. -/
noncomputable def fairBitMeasure : Measure Bool :=
  (2 : ENNReal)⁻¹ • Measure.dirac false +
    (2 : ENNReal)⁻¹ • Measure.dirac true

/-- A default transcript used only to establish that the strict certificate's
choice type is nonempty on every (including malformed) request. -/
def emptyBlackBoxOracleTranscript (n : ℕ) : BlackBoxOracleTranscript n where
  algorithmAnswer := fun _ _ _ => 0
  priorAnswer := fun _ => ⟨fun _ => 0, fun _ => le_rfl⟩
  randomTape := fun _ => false

theorem blackBoxExecutionChoice_nonempty (request : BlackBoxMachineRequest) :
    Nonempty (BlackBoxExecutionChoice request) :=
  ⟨⟨none, emptyBlackBoxOracleTranscript request.agentCount⟩⟩

/-- Fixed external semantics.  Malformed calls return no words; well-formed
calls can reveal only the corresponding advertised algorithm/prior sample.
This definition is outside the program witness. -/
noncomputable def blackBoxMachineEnvironment
    (request : BlackBoxMachineRequest)
    (choice : BlackBoxExecutionChoice request) :
    UnitCostRAM.MachineEnvironment BlackBoxExternalOperation where
  external operation argument :=
    match operation with
    | .algorithmSample =>
        match decodeAlgorithmSampleQuery request.agentCount argument with
        | some (sampleNumber, reports) =>
            profileWords
              (choice.transcript.algorithmAnswer sampleNumber reports)
        | none => []
    | .priorSample =>
        match decodePriorSampleQuery argument with
        | some sampleNumber =>
            profileWords (choice.transcript.priorAnswer sampleNumber).1
        | none => []
  randomTape := choice.transcript.randomTape

/-- A probability law on transcripts is legal for `problem` when it selects
that problem almost surely and every numbered oracle/prior answer has exactly
the advertised law.  This is the bridge between deterministic interpreter
executions and the continuously randomized mathematical oracle. -/
structure LegalBlackBoxExecutionLaw
    (request : BlackBoxMachineRequest)
    (problem : BlackBoxWelfareOracle (Fin request.agentCount)) where
  law : Measure (BlackBoxExecutionChoice request)
  probability : IsProbabilityMeasure law
  problem_fixed :
    ∀ᵐ choice ∂law, choice.problem = some problem
  /-- All oracle samples, prior samples, and random bits are mutually
  independent coordinates; correlations cannot be used as a hidden advice
  channel. -/
  sources_independent :
    iIndepFun
      (m := fun source : BlackBoxRandomSource request.agentCount =>
        BlackBoxRandomSource.valueMeasurableSpace source)
      (fun (source : BlackBoxRandomSource request.agentCount)
        (choice : BlackBoxExecutionChoice request) =>
        BlackBoxRandomSource.observe source choice) law
  algorithm_answer_measurable :
    ∀ sampleNumber reports,
      Measurable
        (fun choice : BlackBoxExecutionChoice request =>
          choice.transcript.algorithmAnswer sampleNumber reports)
  algorithm_answer_law :
    ∀ sampleNumber reports,
      Measure.map
          (fun choice : BlackBoxExecutionChoice request =>
            choice.transcript.algorithmAnswer sampleNumber reports)
          law =
        problem.algorithm reports
  prior_answer_measurable :
    ∀ sampleNumber,
      Measurable
        (fun choice : BlackBoxExecutionChoice request =>
          choice.transcript.priorAnswer sampleNumber)
  prior_answer_law :
    ∀ sampleNumber,
      Measure.map
          (fun choice : BlackBoxExecutionChoice request =>
            choice.transcript.priorAnswer sampleNumber)
          law =
        problem.prior
  random_bit_measurable :
    ∀ bitNumber,
      Measurable
        (fun choice : BlackBoxExecutionChoice request =>
          choice.transcript.randomTape bitNumber)
  random_bit_law :
    ∀ bitNumber,
      Measure.map
          (fun choice : BlackBoxExecutionChoice request =>
            choice.transcript.randomTape bitNumber)
          law =
        fairBitMeasure

/-- Canonical request corresponding to a truthful or deviating report. -/
def blackBoxMachineRequest
    {n : ℕ} (reports : NonnegativeProfile (Fin n)) :
    BlackBoxMachineRequest where
  agentCount := n
  reports := List.ofFn reports.1

/-- A realized allocation and the mechanism's expected payment vector are
returned as two consecutive length-`n` real vectors. -/
def blackBoxOutcomeWords
    {n : ℕ} (allocation payment : Fin n → ℝ) :
    List UnitCostRAM.Word :=
  profileWords allocation ++ profileWords payment

/-- Fixed identity output representation.  The interpreter itself must
produce every allocation/payment word; the decoder performs no computation. -/
def blackBoxOutcomeEncoding :
    UnitCostRAM.ChoiceDependentEncoding
      (fun (_request : BlackBoxMachineRequest)
        (_choice : BlackBoxExecutionChoice _request) =>
        List UnitCostRAM.Word) where
  encode := fun _ _ => id
  decode := fun _ _ => some
  decode_encode := fun _ _ _ => rfl

/-- External operation kinds have fixed resource meanings.  A call to the
allocation algorithm is a black-box query, whereas drawing from the known
prior is a distribution sample.  Rejecting the two crossed cases prevents a
program from moving work between the query and sampling counters. -/
def BlackBoxInstructionUsesExternalOperationCorrectly :
    UnitCostRAM.Instruction BlackBoxExternalOperation → Prop
  | .call .algorithmSample _ _ _ _ => True
  | .call .priorSample _ _ _ _ => False
  | .sample .algorithmSample _ _ _ _ => False
  | .sample .priorSample _ _ _ _ => True
  | _ => True

/-- Every external instruction in the finite program uses the counter
assigned to its advertised operation. -/
def BlackBoxProgramUsesExternalOperationsCorrectly
    (program : UnitCostRAM.Program BlackBoxExternalOperation) : Prop :=
  ∀ instruction ∈ program.code.toList,
    BlackBoxInstructionUsesExternalOperationCorrectly instruction

/-- Instruction-enforced realization of a mathematical black-box reduction.
One finite program handles every dimension.  Its external environment and
input/output encodings are fixed above; the witness cannot replace the oracle
by a callback that returns the desired mechanism. -/
structure StrictBlackBoxImplementation
    (reduction : WelfarePreservingBlackBoxReduction) where
  /-- Exact output words on each deterministic transcript. -/
  outputWords :
    (request : BlackBoxMachineRequest) →
      BlackBoxExecutionChoice request → List UnitCostRAM.Word
  /-- One strict program and one explicit polynomial for all dimensions and
  transcripts. -/
  certificate :
    StrictRAMComputableInPolyTimeWithFixedEnvironment
      blackBoxMachineRequestEncoding
      blackBoxOutcomeEncoding
      BlackBoxExternalOperation
      blackBoxMachineEnvironment
      outputWords
  /-- The program cannot invoke an algorithm sample through `sample`, or a
  prior sample through `call`. -/
  externalOperationsCorrect :
    BlackBoxProgramUsesExternalOperationsCorrectly certificate.program
  /-- Allocation-algorithm calls made by that same interpreter execution are
  polynomial. -/
  polynomialQueries : certificate.HasPolynomialQueries
  /-- Exact-real prior samples made by that execution are polynomial. -/
  polynomialSamples : certificate.UsesPolynomialSamples
  /-- Finite random-bit use is polynomial as a separate resource. -/
  polynomialRandomBits : certificate.UsesPolynomialRandomBits
  /-- Peak RAM usage is polynomial. -/
  polynomialSpace : certificate.UsesPolynomialSpace
  /-- Every genuine oracle instance/report has a legal transcript law. -/
  executionLaw :
    ∀ n, 0 < n →
      ∀ (problem : BlackBoxWelfareOracle (Fin n))
        (reports : NonnegativeProfile (Fin n)),
        LegalBlackBoxExecutionLaw
          (blackBoxMachineRequest reports) problem
  /-- Under the legal transcript law, the words produced by the strict run
  realize exactly the allocation law and payment rule of `simulate`. -/
  realizes :
    ∀ n (hn : 0 < n) (problem : BlackBoxWelfareOracle (Fin n))
      (reports : NonnegativeProfile (Fin n)),
      ∃ realizedAllocation :
          BlackBoxExecutionChoice (blackBoxMachineRequest reports) →
            Fin n → ℝ,
        Measurable realizedAllocation ∧
          Measure.map realizedAllocation
              (executionLaw n hn problem reports).law =
            (reduction.simulate n problem).allocation reports ∧
          ∀ᵐ choice ∂(executionLaw n hn problem reports).law,
            outputWords (blackBoxMachineRequest reports) choice =
              blackBoxOutcomeWords (realizedAllocation choice)
                ((reduction.simulate n problem).payment reports)

/-- Open-problem statement: a semantically welfare-preserving black-box DSIC
reduction has one uniform strict-RAM implementation with fixed representations
and fixed oracle semantics. -/
def WelfarePreservingBlackBoxDSICStatement : Prop :=
  ∃ reduction : WelfarePreservingBlackBoxReduction,
    Nonempty (StrictBlackBoxImplementation reduction)

/-- English version: "Can black-box access to any single-parameter allocation
algorithm be converted into a feasible DSIC mechanism with at least the same
expected welfare?" -/
theorem welfarePreservingBlackBoxDSIC :
    answer(sorry) ↔ WelfarePreservingBlackBoxDSICStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.BlackBoxDSICMechanismDesign
