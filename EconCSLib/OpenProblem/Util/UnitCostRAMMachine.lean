/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.UnitCostRAM
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# An instruction-level unit-cost real-RAM

`CostM` is convenient for compositional proofs, but its annotations are
necessarily trusted: an author could put an expensive Lean term inside
`Cost.pure`.  This file supplies the stricter alternative promised by the
`UnitCostRAM` documentation.  A program is a finite list of instructions; the
interpreter, rather than the program author, charges every executed
instruction.

The word type is the exact-real unit-cost model: an integer, Boolean, or exact
real occupies one word.  Integer/real arithmetic, comparison, indirect load,
indirect store, and control transfer each cost one local step.  Allocating or
freeing a block of `k` words costs `k + 1` local steps; hence a single bulk
instruction cannot hide exponential working space in a polynomial-time run.
An external
call additionally increments the oracle counter and charges every argument
and answer word transferred.  Likewise, `halt` charges every output word read
from RAM.  Thus a one-instruction bulk transfer cannot hide an exponentially
long answer.  A random-bit instruction increments the randomness counter.
The interpreter is fuelled only to make
its Lean definition total.  A complexity certificate must prove that the
fuelled execution actually halts and bound the cost returned by the
interpreter.

This is a RAM/BSS-style operational semantics, not a Turing-machine encoding.
It complements rather than replaces the higher-level `CostM` API: algorithms
may first be verified compositionally with `CostM`, and particularly sensitive
claims can additionally be compiled to this syntax.

The finite-program/random-access organization follows Cook--Reckhow's RAM
framework; exact-real arithmetic follows Blum--Shub--Smale.  The separation
between local steps, oracle calls, samples, and random bits reflects the
distinct resource measures used in oracle and randomized algorithms rather
than pretending that a continuously distributed real sample is a finite bit
string.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM

universe u v w

noncomputable section

namespace Word

/-- Canonical zero word used for initially empty registers and memory. -/
def zero : Word := .integer 0

/-- Read a nonnegative integer word as a RAM address. -/
def asAddress : Word → Option ℕ
  | .integer value => if 0 ≤ value then some value.toNat else none
  | _ => none

/-- Integer addition is defined only on integer words. -/
def integerAdd : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left + right))
  | _, _ => none

def integerSub : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left - right))
  | _, _ => none

def integerMul : Word → Word → Option Word
  | .integer left, .integer right => some (.integer (left * right))
  | _, _ => none

def integerDiv : Word → Word → Option Word
  | .integer left, .integer right =>
      if right = 0 then none else some (.integer (left / right))
  | _, _ => none

def integerMod : Word → Word → Option Word
  | .integer left, .integer right =>
      if right = 0 then none else some (.integer (left % right))
  | _, _ => none

/-- BSS/real-RAM exact real arithmetic. -/
def realAdd : Word → Word → Option Word
  | .real left, .real right => some (.real (left + right))
  | _, _ => none

def realSub : Word → Word → Option Word
  | .real left, .real right => some (.real (left - right))
  | _, _ => none

def realMul : Word → Word → Option Word
  | .real left, .real right => some (.real (left * right))
  | _, _ => none

def realDiv : Word → Word → Option Word
  | .real left, .real right =>
      if right = 0 then none else some (.real (left / right))
  | _, _ => none

def realLE : Word → Word → Option Word
  | .real left, .real right => some (.bit (decide (left ≤ right)))
  | _, _ => none

def integerLE : Word → Word → Option Word
  | .integer left, .integer right => some (.bit (decide (left ≤ right)))
  | _, _ => none

def booleanNot : Word → Option Word
  | .bit value => some (.bit (!value))
  | _ => none

def booleanAnd : Word → Word → Option Word
  | .bit left, .bit right => some (.bit (left && right))
  | _, _ => none

def booleanOr : Word → Word → Option Word
  | .bit left, .bit right => some (.bit (left || right))
  | _, _ => none

end Word

/-- Infinite mathematical register/memory maps.  Only finitely many cells are
reachable in any fuel-bounded execution. -/
abbrev RegisterFile := ℕ → Word
abbrev RAMMemory := ℕ → Word

/-- Read `count` consecutive words. -/
def readWords (memory : RAMMemory) (start count : ℕ) : List Word :=
  List.ofFn fun index : Fin count => memory (start + index)

/-- Write a consecutive list of words. -/
def writeWords : RAMMemory → ℕ → List Word → RAMMemory
  | memory, _, [] => memory
  | memory, address, word :: words =>
      writeWords (Function.update memory address word) (address + 1) words

/-- Load a finite input into memory starting at address zero. -/
def inputMemory (input : List Word) : RAMMemory :=
  fun address => (input[address]?).getD Word.zero

/-- Complete machine configuration. -/
structure MachineState where
  pc : ℕ
  registers : RegisterFile
  memory : RAMMemory
  /-- Number of currently live allocated words. -/
  liveCells : ℕ
  /-- Next fresh address for the simple bump allocator. -/
  nextFresh : ℕ
  /-- Position in the external random-bit tape. -/
  randomCursor : ℕ

/-- Initial state: input words occupy the first memory cells and register `0`
contains the input length. -/
def MachineState.initial (input : List Word) : MachineState where
  pc := 0
  registers := Function.update (fun _ => Word.zero) 0 (.integer input.length)
  memory := inputMemory input
  liveCells := input.length
  nextFresh := input.length
  randomCursor := 0

/-- Instructions of the finite real-RAM program.  Register operands are named
by natural indices.  `call` reads/writes consecutive memory blocks whose
addresses and lengths are stored in registers. -/
inductive Instruction (ExternalOperation : Type u)
  | halt (startRegister lengthRegister : ℕ)
  | constant (destination : ℕ) (value : Word)
  | move (destination source : ℕ)
  | load (destination addressRegister : ℕ)
  | store (addressRegister source : ℕ)
  | integerAdd (destination left right : ℕ)
  | integerSub (destination left right : ℕ)
  | integerMul (destination left right : ℕ)
  | integerDiv (destination left right : ℕ)
  | integerMod (destination left right : ℕ)
  | realAdd (destination left right : ℕ)
  | realSub (destination left right : ℕ)
  | realMul (destination left right : ℕ)
  | realDiv (destination left right : ℕ)
  | integerLE (destination left right : ℕ)
  | realLE (destination left right : ℕ)
  | booleanNot (destination source : ℕ)
  | booleanAnd (destination left right : ℕ)
  | booleanOr (destination left right : ℕ)
  | jump (target : ℕ)
  | branch (conditionRegister ifTrue ifFalse : ℕ)
  | allocate (amountRegister destinationAddressRegister : ℕ)
  | free (amountRegister : ℕ)
  | randomBit (destination : ℕ)
  | call (operation : ExternalOperation)
      (argumentStartRegister argumentLengthRegister : ℕ)
      (resultStartRegister resultLengthDestination : ℕ)
  | sample (operation : ExternalOperation)
      (parameterStartRegister parameterLengthRegister : ℕ)
      (resultStartRegister resultLengthDestination : ℕ)

/-- A finite program.  Falling past the code is a fault, never an implicit
successful halt. -/
structure Program (ExternalOperation : Type u) where
  code : Array (Instruction ExternalOperation)

/-- One plus the greatest register index mentioned by an instruction (with
`1` as the harmless minimum for instructions mentioning no register). -/
def Instruction.registerCount {ExternalOperation : Type u} :
    Instruction ExternalOperation → ℕ
  | .halt start length => max start length + 1
  | .constant destination _ => destination + 1
  | .move destination source => max destination source + 1
  | .load destination address => max destination address + 1
  | .store address source => max address source + 1
  | .integerAdd destination left right
  | .integerSub destination left right
  | .integerMul destination left right
  | .integerDiv destination left right
  | .integerMod destination left right
  | .realAdd destination left right
  | .realSub destination left right
  | .realMul destination left right
  | .realDiv destination left right
  | .integerLE destination left right
  | .realLE destination left right
  | .booleanAnd destination left right
  | .booleanOr destination left right => max destination (max left right) + 1
  | .booleanNot destination source => max destination source + 1
  | .jump _ => 1
  | .branch condition _ _ => condition + 1
  | .allocate amount destination => max amount destination + 1
  | .free amount => amount + 1
  | .randomBit destination => destination + 1
  | .call _ argumentStart argumentLength resultStart resultLength =>
      max argumentStart (max argumentLength (max resultStart resultLength)) + 1
  | .sample _ parameterStart parameterLength resultStart resultLength =>
      max parameterStart (max parameterLength (max resultStart resultLength)) + 1

/-- Static number of registers required by the finite program. -/
def Program.registerCount {ExternalOperation : Type u}
    (program : Program ExternalOperation) : ℕ :=
  program.code.foldl
    (fun current instruction => max current instruction.registerCount) 1

/-- Semantics of explicitly declared external/oracle operations and of the
random tape.  Oracle answers are charged by the interpreter, not by this
function. -/
structure MachineEnvironment (ExternalOperation : Type u) where
  external : ExternalOperation → List Word → List Word
  randomTape : ℕ → Bool

inductive StepStatus
  | running
  | halted (output : List Word)
  | faulted

structure StepOutcome where
  state : MachineState
  status : StepStatus

private def advance (state : MachineState) : MachineState :=
  { state with pc := state.pc + 1 }

private def writeRegister (state : MachineState) (register : ℕ)
    (value : Word) : MachineState :=
  { state with
    pc := state.pc + 1
    registers := Function.update state.registers register value }

private def binaryRegisterOperation (state : MachineState)
    (destination left right : ℕ)
    (operation : Word → Word → Option Word) : StepOutcome :=
  match operation (state.registers left) (state.registers right) with
  | some value => ⟨writeRegister state destination value, .running⟩
  | none => ⟨state, .faulted⟩

private def localOutcome (outcome : StepOutcome) : ProfiledCost StepOutcome :=
  ⟨outcome, (ResourceCounts.localStep, 0)⟩

private def fault (state : MachineState) : ProfiledCost StepOutcome :=
  localOutcome ⟨state, .faulted⟩

/-- Execute exactly one fetched instruction.  Type/address errors produce a
charged fault. -/
def executeInstruction {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (state : MachineState) (instruction : Instruction ExternalOperation) :
    ProfiledCost StepOutcome :=
  match instruction with
  | .halt startRegister lengthRegister =>
      match (state.registers startRegister).asAddress,
          (state.registers lengthRegister).asAddress with
      | some start, some length =>
          if start + length ≤ state.nextFresh then
            ⟨⟨state, .halted (readWords state.memory start length)⟩,
              (ResourceCounts.localSteps (length + 1), 0)⟩
          else fault state
      | _, _ => fault state
  | .constant destination value =>
      localOutcome ⟨writeRegister state destination value, .running⟩
  | .move destination source =>
      localOutcome
        ⟨writeRegister state destination (state.registers source), .running⟩
  | .load destination addressRegister =>
      match (state.registers addressRegister).asAddress with
      | some address =>
          if address < state.nextFresh then
            localOutcome
              ⟨writeRegister state destination (state.memory address), .running⟩
          else fault state
      | none => fault state
  | .store addressRegister source =>
      match (state.registers addressRegister).asAddress with
      | some address =>
          if address < state.nextFresh then
            localOutcome
              ⟨advance { state with
                  memory := Function.update state.memory address
                    (state.registers source) }, .running⟩
          else fault state
      | none => fault state
  | .integerAdd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerAdd)
  | .integerSub destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerSub)
  | .integerMul destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerMul)
  | .integerDiv destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerDiv)
  | .integerMod destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerMod)
  | .realAdd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realAdd)
  | .realSub destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realSub)
  | .realMul destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realMul)
  | .realDiv destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realDiv)
  | .integerLE destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.integerLE)
  | .realLE destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.realLE)
  | .booleanNot destination source =>
      match Word.booleanNot (state.registers source) with
      | some value =>
          localOutcome ⟨writeRegister state destination value, .running⟩
      | none => fault state
  | .booleanAnd destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.booleanAnd)
  | .booleanOr destination left right =>
      localOutcome (binaryRegisterOperation state destination left right Word.booleanOr)
  | .jump target => localOutcome ⟨{ state with pc := target }, .running⟩
  | .branch conditionRegister ifTrue ifFalse =>
      match state.registers conditionRegister with
      | .bit condition =>
          localOutcome
            ⟨{ state with pc := if condition then ifTrue else ifFalse }, .running⟩
      | _ => fault state
  | .allocate amountRegister destinationAddressRegister =>
      match (state.registers amountRegister).asAddress with
      | some amount =>
          let start := state.nextFresh
          let nextState :=
            writeRegister
              { state with
                liveCells := state.liveCells + amount
                nextFresh := state.nextFresh + amount }
              destinationAddressRegister (.integer start)
          ⟨⟨nextState, .running⟩,
            (ResourceCounts.localSteps (amount + 1), Cells.alloc amount)⟩
      | none => fault state
  | .free amountRegister =>
      match (state.registers amountRegister).asAddress with
      | some amount =>
          if amount ≤ state.liveCells then
            ⟨⟨advance { state with
                  liveCells := state.liveCells - amount
                  nextFresh := state.nextFresh - amount },
                .running⟩,
              (ResourceCounts.localSteps (amount + 1), Cells.free amount)⟩
          else fault state
      | none => fault state
  | .randomBit destination =>
      let bit := environment.randomTape state.randomCursor
      let nextState := writeRegister
        { state with randomCursor := state.randomCursor + 1 }
        destination (.bit bit)
      ⟨⟨nextState, .running⟩,
        (ResourceCounts.randomness 1, 0)⟩
  | .call operation argumentStartRegister argumentLengthRegister
      resultStartRegister resultLengthDestination =>
      match (state.registers argumentStartRegister).asAddress,
          (state.registers argumentLengthRegister).asAddress,
          (state.registers resultStartRegister).asAddress with
      | some argumentStart, some argumentLength, some resultStart =>
          let answer := environment.external operation
            (readWords state.memory argumentStart argumentLength)
          if argumentStart + argumentLength ≤ state.nextFresh ∧
              resultStart + answer.length ≤ state.nextFresh then
            let nextState := writeRegister
              { state with memory := writeWords state.memory resultStart answer }
              resultLengthDestination (.integer answer.length)
            ⟨⟨nextState, .running⟩,
              (ResourceCounts.oracleQueryTransfer
                argumentLength answer.length, 0)⟩
          else fault state
      | _, _, _ => fault state
  | .sample operation parameterStartRegister parameterLengthRegister
      resultStartRegister resultLengthDestination =>
      match (state.registers parameterStartRegister).asAddress,
          (state.registers parameterLengthRegister).asAddress,
          (state.registers resultStartRegister).asAddress with
      | some parameterStart, some parameterLength, some resultStart =>
          let answer := environment.external operation
            (readWords state.memory parameterStart parameterLength)
          if parameterStart + parameterLength ≤ state.nextFresh ∧
              resultStart + answer.length ≤ state.nextFresh then
            let nextState := writeRegister
              { state with memory := writeWords state.memory resultStart answer }
              resultLengthDestination (.integer answer.length)
            ⟨⟨nextState, .running⟩,
              (ResourceCounts.distributionSampleTransfer
                parameterLength answer.length, 0)⟩
          else fault state
      | _, _, _ => fault state

/-- Fetch and execute one instruction. -/
def step {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) (state : MachineState) :
    ProfiledCost StepOutcome :=
  match program.code[state.pc]? with
  | some instruction => executeInstruction environment state instruction
  | none => fault state

inductive ExecutionResult
  | halted (output : List Word) (state : MachineState)
  | faulted (state : MachineState)
  | outOfFuel (state : MachineState)

/-- Fuelled reflexive execution.  All actual resource counts come from
`step`; fuel exhaustion itself adds no fictitious machine instruction. -/
def execute {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) : ℕ → MachineState →
      ProfiledCost ExecutionResult
  | 0, state => ⟨.outOfFuel state, 0⟩
  | fuel + 1, state =>
      let one := step environment program state
      match one.ret.status with
      | .running =>
          let rest := execute environment program fuel one.ret.state
          ⟨rest.ret, one.cost + rest.cost⟩
      | .halted output => ⟨.halted output one.ret.state, one.cost⟩
      | .faulted => ⟨.faulted one.ret.state, one.cost⟩

/-- Run a program from its canonical input state. -/
def run {ExternalOperation : Type u}
    (environment : MachineEnvironment ExternalOperation)
    (program : Program ExternalOperation) (fuel : ℕ)
    (input : List Word) : ProfiledCost ExecutionResult :=
  execute environment program fuel (MachineState.initial input)

/-- Environment for a program with no external operations and a fixed random
tape. -/
def closedEnvironment (randomTape : ℕ → Bool) :
    MachineEnvironment Empty where
  external operation := nomatch operation
  randomTape := randomTape

/-- Lossless output representation for an execution whose output type depends
on both the ordinary input and an auxiliary seed/oracle/adversarial choice. -/
structure ChoiceDependentEncoding
    {Input : Type u} {Choice : Input → Type v}
    (Output : (input : Input) → Choice input → Type w) where
  encode : (input : Input) → (choice : Choice input) →
    Output input choice → List Word
  decode : (input : Input) → (choice : Choice input) →
    List Word → Option (Output input choice)
  decode_encode : ∀ input choice output,
    decode input choice (encode input choice output) = some output

/-!
## Fixed-representation polynomial-time certificates

The encodings in this section are parameters, not fields chosen by the
implementation witness.  This follows the design of mathlib's
`Turing.TM2ComputableInPolyTime`, used in OpenAI's `ten-proofs`: the
representation is fixed before the finite program is exhibited, the time
majorant is an explicit polynomial, and the bound is imposed on the actual
interpreter trace.  Fixing the encodings prevents a purported implementation
from hiding the mathematical computation in a witness-specific decoder.
-/

/-- A finite closed real-RAM program computing `function` in time bounded by
an explicit natural-coefficient polynomial in a *fixed* lossless input
encoding.  The dependent output encoding is also fixed outside the witness.

The same interpreter execution appears in both `correct` and `time_bound`, so
the polynomial certificate cannot count a cheaper execution than the one that
produces the advertised output. -/
structure StrictRAMComputableInPolyTime
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (function : (input : Input) → Output input) where
  program : Program Empty
  fuel : Input → ℕ
  time : Polynomial ℕ
  correct : ∀ input,
    ∃ outputWords finalState,
      (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input outputWords = some (function input)
  time_bound : ∀ input,
    ProfiledCost.steps
        (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)) ≤
      time.eval (inputEncoding.size input)

/-- Compatibility certificate for a seed, legal oracle, adversarial
tie-breaking rule, or other execution choice.  One finite program and one
explicit polynomial must work for every input and every choice, but the
external environment is still selected inside this witness.  Complexity-class
definitions should use
`StrictRAMComputableInPolyTimeWithFixedEnvironment` instead.

External operations are still problem-specific primitives.  A caller using
this interface must separately verify that `environment` implements exactly
the advertised oracle/sampling contract; an external call is not permission
to hide arbitrary local computation. -/
structure StrictRAMComputableInPolyTimeWithChoice
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (inputEncoding : Encoding Input)
    (outputEncoding : ChoiceDependentEncoding Output)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  ExternalOperation : Type
  environment : (input : Input) →
    Choice input → MachineEnvironment ExternalOperation
  program : Program ExternalOperation
  fuel : (input : Input) → Choice input → ℕ
  time : Polynomial ℕ
  correct : ∀ input choice,
    ∃ outputWords finalState,
      (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input choice outputWords =
        some (function input choice)
  time_bound : ∀ input choice,
    ProfiledCost.steps
        (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)) ≤
      time.eval (inputEncoding.size input)

/-- Preferred choice/oracle certificate with the external-operation type and
semantics fixed by the surrounding problem statement.  Keeping `environment`
outside the witness prevents a purported implementation from installing an
ad-hoc oracle that simply returns the desired mathematical answer. -/
structure StrictRAMComputableInPolyTimeWithFixedEnvironment
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (inputEncoding : Encoding Input)
    (outputEncoding : ChoiceDependentEncoding Output)
    (ExternalOperation : Type*)
    (environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation)
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  program : Program ExternalOperation
  fuel : (input : Input) → Choice input → ℕ
  time : Polynomial ℕ
  correct : ∀ input choice,
    ∃ outputWords finalState,
      (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input choice outputWords =
        some (function input choice)
  time_bound : ∀ input choice,
    ProfiledCost.steps
        (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)) ≤
      time.eval (inputEncoding.size input)

/-- A fixed-representation polynomial-time solver for a dependent search
relation on a promise domain.  Unlike `CostedSearchImplementation`, both the
answer and its running time come from the same finite instruction-level
execution.  Correctness may select any valid output; no canonical choice
function is built into the statement. -/
structure StrictRAMSearchableInPolyTime
    {Input : Type u} {Output : Input → Type v}
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (valid : Input → Prop)
    (solution : (input : Input) → Output input → Prop) where
  program : Program Empty
  fuel : Input → ℕ
  time : Polynomial ℕ
  correct : ∀ input, valid input →
    ∃ output outputWords finalState,
      (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input outputWords = some output ∧
      solution input output
  time_bound : ∀ input, valid input →
    ProfiledCost.steps
        (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)) ≤
      time.eval (inputEncoding.size input)

namespace StrictRAMComputableInPolyTimeWithChoice

def execution
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithChoice
      inputEncoding outputEncoding function)
    (input : Input) (choice : Choice input) : ProfiledCost ExecutionResult :=
  run (certificate.environment input choice) certificate.program
    (certificate.fuel input choice) (inputEncoding.encode input)

def HasPolynomialQueries
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithChoice
      inputEncoding outputEncoding function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.oracleQueries (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialRandomBits
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithChoice
      inputEncoding outputEncoding function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.randomBits (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialSamples
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithChoice
      inputEncoding outputEncoding function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.distributionSamples (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialSpace
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithChoice
      inputEncoding outputEncoding function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    certificate.program.registerCount + inputEncoding.size input +
        ProfiledCost.peakCells (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

end StrictRAMComputableInPolyTimeWithChoice

namespace StrictRAMComputableInPolyTimeWithFixedEnvironment

def execution
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function)
    (input : Input) (choice : Choice input) : ProfiledCost ExecutionResult :=
  run (environment input choice) certificate.program
    (certificate.fuel input choice) (inputEncoding.encode input)

def HasPolynomialQueries
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.oracleQueries (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialRandomBits
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.randomBits (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialSamples
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    ProfiledCost.distributionSamples (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

def UsesPolynomialSpace
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {inputEncoding : Encoding Input}
    {outputEncoding : ChoiceDependentEncoding Output}
    {ExternalOperation : Type*}
    {environment : (input : Input) →
      Choice input → MachineEnvironment ExternalOperation}
    {function : (input : Input) → (choice : Choice input) →
      Output input choice}
    (certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      inputEncoding outputEncoding ExternalOperation environment function) : Prop :=
  ∃ bound : Polynomial ℕ, ∀ input choice,
    certificate.program.registerCount + inputEncoding.size input +
        ProfiledCost.peakCells (certificate.execution input choice) ≤
      bound.eval (inputEncoding.size input)

end StrictRAMComputableInPolyTimeWithFixedEnvironment

/-- Instruction-enforced implementation of a deterministic mathematical
function.  Unlike a bare `CostedImplementation`, the returned cost can only be
generated by interpreting the finite `program`. -/
structure StrictRAMImplementation
    {Input : Type u} {Output : Input → Type v}
    (function : (input : Input) → Output input) where
  inputEncoding : Encoding Input
  outputEncoding : DependentEncoding Output
  program : Program Empty
  fuel : Input → ℕ
  correct : ∀ input,
    ∃ outputWords finalState,
      (run (closedEnvironment fun _ => false) program (fuel input)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input outputWords = some (function input)

/-- Polynomial time of an instruction-enforced implementation. -/
def StrictRAMImplementation.IsPolynomial
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : StrictRAMImplementation function) : Prop :=
  IsPolyBound implementation.inputEncoding.size fun input =>
    ProfiledCost.steps
      (run (closedEnvironment fun _ => false)
        implementation.program (implementation.fuel input)
        (implementation.inputEncoding.encode input))

/-- Simultaneous polynomial time and peak-space bounds for the strict run. -/
def StrictRAMImplementation.IsPolynomialTimeAndSpace
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (implementation : StrictRAMImplementation function) : Prop :=
  implementation.IsPolynomial ∧
    IsPolyBound implementation.inputEncoding.size fun input =>
      implementation.program.registerCount +
        implementation.inputEncoding.size input + ProfiledCost.peakCells
        (run (closedEnvironment fun _ => false)
          implementation.program (implementation.fuel input)
          (implementation.inputEncoding.encode input))

/-- Instruction-enforced implementation uniform over a random seed, an
oracle, a tie-breaking rule, or another execution choice.  `environment` is
part of the public certificate, so an oracle problem must prove that its
external operations are exactly the advertised legal oracle calls. -/
structure StrictRAMImplementationWithChoice
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    (function : (input : Input) →
      (choice : Choice input) → Output input choice) where
  choice_nonempty : ∀ input, Nonempty (Choice input)
  inputEncoding : Encoding Input
  outputEncoding : ChoiceDependentEncoding Output
  ExternalOperation : Type
  environment : (input : Input) →
    Choice input → MachineEnvironment ExternalOperation
  program : Program ExternalOperation
  fuel : (input : Input) → Choice input → ℕ
  correct : ∀ input choice,
    ∃ outputWords finalState,
      (run (environment input choice) program (fuel input choice)
          (inputEncoding.encode input)).ret =
        .halted outputWords finalState ∧
      outputEncoding.decode input choice outputWords =
        some (function input choice)

namespace StrictRAMImplementationWithChoice

def time
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function)
    (input : Input) (choice : Choice input) : ℕ :=
  ProfiledCost.steps
    (run (implementation.environment input choice) implementation.program
      (implementation.fuel input choice)
      (implementation.inputEncoding.encode input))

def queries
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function)
    (input : Input) (choice : Choice input) : ℕ :=
  ProfiledCost.oracleQueries
    (run (implementation.environment input choice) implementation.program
      (implementation.fuel input choice)
      (implementation.inputEncoding.encode input))

def randomness
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function)
    (input : Input) (choice : Choice input) : ℕ :=
  ProfiledCost.randomBits
    (run (implementation.environment input choice) implementation.program
      (implementation.fuel input choice)
      (implementation.inputEncoding.encode input))

def samples
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function)
    (input : Input) (choice : Choice input) : ℕ :=
  ProfiledCost.distributionSamples
    (run (implementation.environment input choice) implementation.program
      (implementation.fuel input choice)
      (implementation.inputEncoding.encode input))

def space
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function)
    (input : Input) (choice : Choice input) : ℕ :=
  implementation.program.registerCount +
    implementation.inputEncoding.size input + ProfiledCost.peakCells
    (run (implementation.environment input choice) implementation.program
      (implementation.fuel input choice)
      (implementation.inputEncoding.encode input))

/-- One polynomial bound valid for all inputs and all execution choices. -/
def IsPolynomialTime
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function) : Prop :=
  IsUniformPolyBound implementation.inputEncoding.size implementation.time

def HasPolynomialQueries
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function) : Prop :=
  IsUniformPolyBound implementation.inputEncoding.size implementation.queries

def UsesPolynomialRandomness
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function) : Prop :=
  IsUniformPolyBound implementation.inputEncoding.size implementation.randomness

def UsesPolynomialSamples
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function) : Prop :=
  IsUniformPolyBound implementation.inputEncoding.size implementation.samples

def UsesPolynomialSpace
    {Input : Type u} {Choice : Input → Type v}
    {Output : (input : Input) → Choice input → Type w}
    {function : (input : Input) →
      (choice : Choice input) → Output input choice}
    (implementation : StrictRAMImplementationWithChoice function) : Prop :=
  IsUniformPolyBound implementation.inputEncoding.size implementation.space

end StrictRAMImplementationWithChoice

end

end EconCSLib.OpenProblem.UnitCostRAM
