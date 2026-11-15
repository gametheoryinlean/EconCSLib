/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.Search
import Mathlib.Data.Fintype.Basic



section

/-!
# Interaction for problems explicitly allowing oracles or randomness

The deterministic mini core is unchanged: `core` invokes `WordRAM.step` with its
original arithmetic, overflow, memory, and halting semantics. The additional `call`,
`sample`, and `randomBit` instructions require explicit permission in the problem's
model; this runtime is not unrelativized deterministic P.

Oracle boundaries exchange bounded natural-word arrays, not arbitrary reals or
unbounded integers. Both requests and responses incur length-dependent cost. The
problem fixes the environment before the program. The interpreter supplies call and
sample serial numbers; they are not free computational callbacks.
-/
namespace EconCSLib.OpenProblem.New.WordRAM.Interaction
open FiniteData
universe u

/-- Core instructions together with explicitly permitted interaction operations. -/
inductive Instruction (Operation : Type u)
  | core (instruction : WordRAM.Instruction)
  | call (operation : Operation)
      (argumentStart argumentLength answerStart answerLength : ℕ)
  | sample (operation : Operation)
      (argumentStart argumentLength answerStart answerLength : ℕ)
  | randomBit (destination : ℕ)

/-- A program over a problem-fixed finite operation alphabet. Dynamic arguments are
request words, not arbitrary functions or reals embedded in operation names. -/
structure Program (Operation : Type u) [Fintype Operation] where
  code : Array (Instruction Operation)

/-- Preserve instruction positions for the core branch. Its execution never uses the
placeholder instructions at external-operation positions. -/
def Program.localProgram {Operation : Type u} [Fintype Operation] (program : Program Operation) :
    WordRAM.Program where
  code := program.code.map fun instruction =>
    match instruction with
    | .core i => i
    | _ => .jump 0

/-- A problem-fixed environment. A problem using sampling or random tapes must specify
their laws, independence, and success criteria. -/
structure Environment (Operation : Type u) where
  query : Operation → ℕ → List ℕ → Option (List ℕ)
  sample : Operation → ℕ → List ℕ → Option (List ℕ)
  randomTape : ℕ → Option Bool

/-- Machine state and interpreter-maintained interaction counters. -/
structure State where
  machine : MachineState
  queries : ℕ := 0
  samples : ℕ := 0
  randomBits : ℕ := 0

/-- One interactive transition, its status, and its charged cost. -/
structure StepResult where
  state : State
  status : StepStatus
  cost : ℕ

private def fault (state : State) (cost : ℕ := 1) : StepResult :=
  ⟨state, .faulted, cost⟩

private def readBlock (memory : ℕ → ℕ) (start length : ℕ) : List ℕ :=
  (List.range length).map fun offset => memory (start + offset)

private def writeBlock : (ℕ → ℕ) → ℕ → List ℕ → (ℕ → ℕ)
  | memory, _, [] => memory
  | memory, start, value :: tail =>
      writeBlock (Function.update memory start value) (start + 1) tail

/-- Bound addresses and returned word values before writing memory. An invalid response
faults rather than silently truncating. -/
private def exchange (width : ℕ) (state : State)
    (isSample : Bool) (answer : ℕ → List ℕ → Option (List ℕ))
    (argumentStart argumentLength answerStart answerLength : ℕ) : StepResult :=
  let machine := state.machine
  let start := machine.registers argumentStart
  let length := machine.registers argumentLength
  let destination := machine.registers answerStart
  let modulus := wordModulus width
  if start + length ≤ modulus then
    let serial := if isSample then state.samples else state.queries
    let queried := if isSample then { state with samples := state.samples + 1 }
      else { state with queries := state.queries + 1 }
    match answer serial (readBlock machine.memory start length) with
    | none => fault queried (1 + length)
    | some values =>
        if values.length < modulus ∧ destination + values.length ≤ modulus ∧
            values.all (fun v => decide (v < modulus)) = true then
          let memory := writeBlock machine.memory destination values
          let registers := Function.update machine.registers answerLength values.length
          let next : MachineState :=
            { pc := machine.pc + 1, registers, memory }
          ⟨{ queried with machine := next }, .running, 1 + length + values.length⟩
        else fault queried (1 + length + values.length)
  else fault state

/-- The core branch reuses the original mini core's arithmetic semantics. -/
def step {Operation : Type u} [Fintype Operation] (width : ℕ)
    (environment : Environment Operation) (program : Program Operation)
    (state : State) : StepResult :=
  match program.code[state.machine.pc]? with
  | none => fault state
  | some (.core _) =>
      let result := WordRAM.step width program.localProgram state.machine
      ⟨{ state with machine := result.state }, result.status, result.cost⟩
  | some (.call operation a l d n) =>
      exchange width state false (environment.query operation) a l d n
  | some (.sample operation a l d n) =>
      exchange width state true (environment.sample operation) a l d n
  | some (.randomBit destination) =>
      match environment.randomTape state.randomBits with
      | none => fault state
      | some value =>
          let machine := state.machine
          let registers := Function.update machine.registers destination
            (normalizeWord width (if value then 1 else 0))
          ⟨{ machine := { machine with pc := machine.pc + 1, registers },
              queries := state.queries, samples := state.samples,
              randomBits := state.randomBits + 1 }, .running, 1⟩

/-- Termination, final interactive state, and cumulative execution cost. -/
structure Result where
  termination : Termination
  state : State
  cost : ℕ

/-- Fuel-bounded execution; fuel is not visible to the interpreted program. -/
def execute {Operation : Type u} [Fintype Operation] (width : ℕ)
    (environment : Environment Operation) (program : Program Operation) :
    ℕ → State → Result
  | 0, state => ⟨.outOfFuel, state, 0⟩
  | fuel + 1, state =>
      let one := step width environment program state
      match one.status with
      | .running =>
          let rest := execute width environment program fuel one.state
          { rest with cost := one.cost + rest.cost }
      | .halted output => ⟨.halted output, one.state, one.cost⟩
      | .faulted => ⟨.faulted, one.state, one.cost⟩

/-- Execute from the canonical bitstream input state and its fixed model width. -/
def run {Operation : Type u} [Fintype Operation] (model : Model)
    (environment : Environment Operation) (program : Program Operation)
    (fuel : ℕ) (input : Code) : Result :=
  execute (encoding.width model input) environment program fuel
    { machine := MachineState.initial (encoding.width model input) (words input) }

/-- An oracle-free random-tape environment. Exhausting the tape faults; it does not supply
synthetic bits or an undeclared advice channel. -/
def randomOnly (tape : ℕ → Option Bool) : Environment Empty where
  query op := nomatch op
  sample op := nomatch op
  randomTape := tape

/-- Wrap a problem-fixed oracle in the finite-table protocol. This is external oracle
semantics. -/
noncomputable def tableReply
    (oracle : Table → Option Table) (argument : List ℕ) : Option (List ℕ) := do
  let code ← ofWords argument
  let table ← FiniteData.decodeSpec code
  let result ← oracle table
  let encoded ← FiniteData.encodeSpec result
  pure (words encoded)

end EconCSLib.OpenProblem.New.WordRAM.Interaction

end
