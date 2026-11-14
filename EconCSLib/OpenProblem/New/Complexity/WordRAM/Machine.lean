/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log



section

/-!
# Bounded Word-RAM

A deterministic machine with arithmetic, comparisons, Boolean operations,
random-access memory, and control flow on unsigned bounded words. The instruction set
follows Open Data Structures, Section 1.4.

For an input of `m` words, `Model` fixes a positive logarithmic width factor.
Arithmetic is modulo `2 ^ wordWidth`. Ordinary instructions cost one; emitting `k`
output words costs `k + 1`. Execution starts from the encoded input and
zero-initialized registers and working memory.

`Encoding` and `DependentEncoding` specify lossless input and output representations.
`Implementation` consists of a program, a fuel bound, and correctness for the fixed
encodings. Input size is the array's bit capacity, `m * wordWidth`.
-/

namespace EconCSLib.OpenProblem.New.WordRAM

universe u v

/-!
## Words and fixed representations
-/

/-- Width used on an input of `inputWords` words. A fixed positive factor makes this
`Theta(log inputWords)` while allowing polynomially many addresses. -/
def wordWidth (widthFactor inputWords : ℕ) : ℕ :=
  widthFactor * (Nat.log2 (inputWords + 1) + 1)

/-- Number of values representable by one word of the given width. -/
def wordModulus (width : ℕ) : ℕ := 2 ^ width

/-- Canonical unsigned value stored in a bounded word. -/
def normalizeWord (width value : ℕ) : ℕ :=
  value % wordModulus width

/-- A natural number fits in one word without truncation. -/
def FitsInWord (width value : ℕ) : Prop :=
  value < wordModulus width

/-- One transdichotomous Word-RAM width convention. The factor is constant for the whole
execution and independent of the input. Fixing a `Model` outside an `Implementation`
makes algorithms compared at that model use the same width; the full complexity class
may quantify over a fixed factor together with the chosen implementation. -/
structure Model where
  widthFactor : ℕ
  widthFactor_pos : 0 < widthFactor

/-- A fixed lossless representation as a finite list of unsigned words. -/
structure Encoding (Input : Type u) where
  encode : Input → List ℕ
  decode : List ℕ → Option Input
  decode_encode : ∀ input, decode (encode input) = some input

/-- Input length measured in words. -/
def Encoding.size {Input : Type u} (encoding : Encoding Input)
    (input : Input) : ℕ :=
  (encoding.encode input).length

/-- Width used by an implementation with the selected fixed factor. -/
def Encoding.width {Input : Type u} (encoding : Encoding Input)
    (model : Model) (input : Input) : ℕ :=
  wordWidth model.widthFactor (encoding.size input)

/-- Bit capacity of the encoded word array, including within-word padding; not necessarily
the shortest binary representation of the mathematical object. -/
def Encoding.bitSize {Input : Type u} (encoding : Encoding Input)
    (model : Model) (input : Input) : ℕ :=
  encoding.size input * encoding.width model input

/-- A lossless output representation whose type may depend on the input. -/
structure DependentEncoding {Input : Type u} (Output : Input → Type v) where
  encode : (input : Input) → Output input → List ℕ
  decode : (input : Input) → List ℕ → Option (Output input)
  decode_encode : ∀ input output,
    decode input (encode input output) = some output

/-!
## Additional conventions of this model

Words are unsigned. Comparisons return zero or one; branching treats every nonzero
word as true. Subtraction is modular, not saturating natural subtraction.
Multiplication retains the low word; a two-word product requires an implementation.
Division or remainder by zero faults. Logical shifts by at least the word width return
zero. NOT complements exactly the word width. An out-of-code jump faults at the next
fetch.

Open Data Structures requires words large enough for addresses; the logarithmic
formula and these overflow, fault, and shift rules are specific model choices. Memory
is a pre-existing address space: writing or clearing `k` cells requires `k` stores
plus control cost. Halting outputs a contiguous block at cost `k+1`, without wrapping
around the address-space boundary.

Register identifiers, literal constants and jump targets are finite program metadata.
The natural numbers in the Lean interpreter are not additional unbounded-integer
primitives available to the simulated program.
-/

/-!
Ordinary instructions and fetch faults cost one; halting with `k` output words costs
`k+1`. `step` records cost directly, without a duplicate event type.
-/

/-!
## Finite programs and deterministic execution
-/

/-- The full Word-RAM instruction set. Arithmetic results are reduced modulo `2 ^
wordWidth`; division or remainder by zero faults. Shifts by at least the word width
return zero. -/
inductive Instruction
  | halt (startRegister lengthRegister : ℕ)
  | constant (destination value : ℕ)
  | move (destination source : ℕ)
  | load (destination addressRegister : ℕ)
  | store (addressRegister source : ℕ)
  | add (destination left right : ℕ)
  | sub (destination left right : ℕ)
  | mul (destination left right : ℕ)
  | div (destination left right : ℕ)
  | mod (destination left right : ℕ)
  | equal (destination left right : ℕ)
  | notEqual (destination left right : ℕ)
  | lessThan (destination left right : ℕ)
  | lessEqual (destination left right : ℕ)
  | greaterThan (destination left right : ℕ)
  | greaterEqual (destination left right : ℕ)
  | bitNot (destination source : ℕ)
  | bitAnd (destination left right : ℕ)
  | bitOr (destination left right : ℕ)
  | bitXor (destination left right : ℕ)
  | shiftLeft (destination value amount : ℕ)
  | shiftRight (destination value amount : ℕ)
  | jump (target : ℕ)
  | branch (conditionRegister ifTrue ifFalse : ℕ)
  deriving DecidableEq

/-- A single finite program, independent of the input. -/
structure Program where
  code : Array Instruction

/-- Total-map states need not be bounded or default-initialized in isolation.
`Implementation` starts from `MachineState.initial`, where transitions preserve
bounded words and modify finitely many cells. Runtime claims must not replace this
canonical input state with arbitrary preloaded memory. -/
structure MachineState where
  pc : ℕ
  registers : ℕ → ℕ
  memory : ℕ → ℕ

private def inputMemory (input : List ℕ) : ℕ → ℕ :=
  fun address => (input[address]?).getD 0

/-- Initial state: input word `i` is stored at memory address `i`, and register zero
contains the number of input words. -/
def MachineState.initial (width : ℕ) (input : List ℕ) : MachineState where
  pc := 0
  registers := Function.update (fun _ ↦ 0) 0
    (normalizeWord width input.length)
  memory := inputMemory (input.map (normalizeWord width))

private def advance (state : MachineState) : MachineState :=
  { state with pc := state.pc + 1 }

private def writeRegister (width : ℕ) (state : MachineState)
    (destination value : ℕ) : MachineState :=
  let registers := Function.update state.registers destination
    (normalizeWord width value)
  advance { state with registers := registers }

private def readWords (memory : ℕ → ℕ) (start length : ℕ) : List ℕ :=
  (List.range length).map fun offset => memory (start + offset)

inductive StepStatus
  | running
  | halted (output : List ℕ)
  | faulted

structure StepOutcome where
  state : MachineState
  status : StepStatus
  cost : ℕ

private def running (state : MachineState) : StepOutcome :=
  { state, status := .running, cost := 1 }

private def fault (state : MachineState) : StepOutcome :=
  { state, status := .faulted, cost := 1 }

private def binary (width : ℕ) (state : MachineState)
    (destination left right : ℕ)
    (operation : ℕ → ℕ → Option ℕ) : StepOutcome :=
  match operation (state.registers left) (state.registers right) with
  | some value => running (writeRegister width state destination value)
  | none => fault state

/-- Execute one fetched instruction. -/
def step (width : ℕ) (program : Program) (state : MachineState) : StepOutcome :=
  match program.code[state.pc]? with
  | none => fault state
  | some instruction =>
      let modulus := wordModulus width
      match instruction with
      | .halt startRegister lengthRegister =>
          let start := state.registers startRegister
          let length := state.registers lengthRegister
          if start + length ≤ modulus then
            { state, status := .halted (readWords state.memory start length),
              cost := length + 1 }
          else fault state
      | .constant destination value =>
          running (writeRegister width state destination value)
      | .move destination source =>
          running
            (writeRegister width state destination (state.registers source))
      | .load destination addressRegister =>
          running
            (writeRegister width state destination
              (state.memory (state.registers addressRegister)))
      | .store addressRegister source =>
          let memory := Function.update state.memory
            (state.registers addressRegister) (state.registers source)
          running (advance { state with memory := memory })
      | .add destination left right =>
          binary width state destination left right
            (fun a b => some (a + b))
      | .sub destination left right =>
          binary width state destination left right
            (fun a b => some (a + modulus - b))
      | .mul destination left right =>
          binary width state destination left right
            (fun a b => some (a * b))
      | .div destination left right =>
          binary width state destination left right
            (fun a b => if b = 0 then none else some (a / b))
      | .mod destination left right =>
          binary width state destination left right
            (fun a b => if b = 0 then none else some (a % b))
      | .equal destination left right =>
          binary width state destination left right
            (fun a b => some (if a = b then 1 else 0))
      | .notEqual destination left right =>
          binary width state destination left right
            (fun a b => some (if a ≠ b then 1 else 0))
      | .lessThan destination left right =>
          binary width state destination left right
            (fun a b => some (if a < b then 1 else 0))
      | .lessEqual destination left right =>
          binary width state destination left right
            (fun a b => some (if a ≤ b then 1 else 0))
      | .greaterThan destination left right =>
          binary width state destination left right
            (fun a b => some (if b < a then 1 else 0))
      | .greaterEqual destination left right =>
          binary width state destination left right
            (fun a b => some (if b ≤ a then 1 else 0))
      | .bitNot destination source =>
          running (writeRegister width state destination
            (modulus - 1 - state.registers source))
      | .bitAnd destination left right =>
          binary width state destination left right
            (fun a b => some (Nat.land a b))
      | .bitOr destination left right =>
          binary width state destination left right
            (fun a b => some (Nat.lor a b))
      | .bitXor destination left right =>
          binary width state destination left right
            (fun a b => some (Nat.xor a b))
      | .shiftLeft destination value amount =>
          binary width state destination value amount
            (fun a b => some (if width ≤ b then 0 else Nat.shiftLeft a b))
      | .shiftRight destination value amount =>
          binary width state destination value amount
            (fun a b => some (if width ≤ b then 0 else Nat.shiftRight a b))
      | .jump target =>
          running { state with pc := target }
      | .branch conditionRegister ifTrue ifFalse =>
          running
            { state with pc :=
                if state.registers conditionRegister = 0 then ifFalse else ifTrue }

inductive Termination
  | halted (output : List ℕ)
  | faulted
  | outOfFuel
  deriving DecidableEq

structure ExecutionResult where
  termination : Termination
  state : MachineState
  cost : ℕ

/-- Fuelled deterministic execution. Fuel is a proof device and is not charged; every
fetched instruction contributes its primitive price. -/
def execute (width : ℕ) (program : Program) : ℕ → MachineState → ExecutionResult
  | 0, state => { termination := .outOfFuel, state, cost := 0 }
  | fuel + 1, state =>
      let one := step width program state
      match one.status with
      | .running =>
          let rest := execute width program fuel one.state
          { rest with cost := one.cost + rest.cost }
      | .halted output =>
          { termination := .halted output, state := one.state, cost := one.cost }
      | .faulted =>
          { termination := .faulted, state := one.state, cost := one.cost }

/-- Run from the canonical encoded-input state. -/
def run (width : ℕ) (program : Program) (fuel : ℕ)
    (input : List ℕ) : ExecutionResult :=
  execute width program fuel (MachineState.initial width input)

/-!
## Fixed-representation implementations
-/

/-- A deterministic program computing a fixed mathematical function. Encodings are fixed
parameters of the problem, not fields chosen by the implementation. Their
computational adequacy is a separate obligation of the problem statement; losslessness
alone does not establish it. The positive width factor is fixed before the input. -/
structure Implementation
    {Input : Type u} {Output : Input → Type v}
    (model : Model)
    (inputEncoding : Encoding Input)
    (outputEncoding : DependentEncoding Output)
    (function : (input : Input) → Output input) where
  program : Program
  fuel : Input → ℕ
  input_fits : ∀ input word, word ∈ inputEncoding.encode input →
    FitsInWord (inputEncoding.width model input) word
  output_fits : ∀ input word,
    word ∈ outputEncoding.encode input (function input) →
      FitsInWord (inputEncoding.width model input) word
  correct : ∀ input,
    (run (inputEncoding.width model input) program (fuel input)
      (inputEncoding.encode input)).termination =
        .halted (outputEncoding.encode input (function input))

namespace Implementation

variable {Input : Type u} {Output : Input → Type v}
  {model : Model}
  {inputEncoding : Encoding Input}
  {outputEncoding : DependentEncoding Output}
  {function : (input : Input) → Output input}

/-- Exact interpreter execution selected by an implementation. -/
def execution
    (implementation : Implementation model inputEncoding outputEncoding function)
    (input : Input) : ExecutionResult :=
  run (inputEncoding.width model input)
    implementation.program (implementation.fuel input)
    (inputEncoding.encode input)

/-- Exact number of charged Word-RAM steps on one input. -/
def operationCount
    (implementation : Implementation model inputEncoding outputEncoding function)
    (input : Input) : ℕ :=
  (implementation.execution input).cost

end Implementation

end EconCSLib.OpenProblem.New.WordRAM

end
