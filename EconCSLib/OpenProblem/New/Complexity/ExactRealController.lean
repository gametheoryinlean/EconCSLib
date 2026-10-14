/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.Machine
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic



section

/-!
# A finite exact-real arithmetic controller

This model is distinct from bounded Word-RAM. Word instructions use `WordRAM.step`;
real instructions use rational literals, field arithmetic, and comparisons. Division
by zero faults. There are no arbitrary callbacks, arbitrary real literals, floor
operations, or transcendental primitives.

Each problem fixes the interpreter for its finite external-operation alphabet. An
external instruction emits only a tag and four register identifiers, without a
continuation or cost function. The interpreter specifies the operation and charges
request and response copying. Unit-cost exact-real arithmetic is a model convention.
-/
namespace EconCSLib.OpenProblem.New.ExactRealController

/-- Finite syntax with rational, not arbitrary-real, literals. -/
inductive Instruction (Operation : Type)
  | word (instruction : WordRAM.Instruction)
  | rational (destination : ℕ) (value : ℚ)
  | move (destination source : ℕ)
  | load (destination addressRegister : ℕ)
  | store (addressRegister source : ℕ)
  | add (destination left right : ℕ)
  | sub (destination left right : ℕ)
  | mul (destination left right : ℕ)
  | div (destination left right : ℕ)
  | less (wordDestination left right : ℕ)
  | equal (wordDestination left right : ℕ)
  | fromWord (destination wordSource : ℕ)
  | external (operation : Operation) (a b c d : ℕ)
  | haltReal (wordStart wordLength realStart realLength : ℕ)

/-- One finite instruction array, uniform across public input dimensions. -/
structure Program (Operation : Type) [Fintype Operation] where
  code : Array (Instruction Operation)

/-- Preserve positions and jump targets when invoking the original word core. -/
def Program.wordProgram {Operation : Type} [Fintype Operation]
    (program : Program Operation) : WordRAM.Program where
  code := program.code.map fun instruction =>
    match instruction with
    | .word i => i
    | _ => .jump 0

/-- Natural cells use the bounded word core. Real registers and memory are separate banks;
dynamic real-memory addresses come from word registers. -/
structure State where
  machine : WordRAM.MachineState
  registers : ℕ → ℝ
  memory : ℕ → ℝ

/-- Canonical public inputs only; all remaining cells start at zero. -/
noncomputable def State.initial (width : ℕ)
    (wordInput : List ℕ) (realInput : List ℝ) : State where
  machine := WordRAM.MachineState.initial width wordInput
  registers := fun _ => 0
  memory := fun address => (realInput[address]?).getD 0

/-- Copying the finite code and both public input arrays is charged. -/
def initialCost {Operation : Type} [Fintype Operation]
    (program : Program Operation) (wordInput : List ℕ) (realInput : List ℝ) : ℕ :=
  program.code.size + wordInput.length + realInput.length + 1

def State.advance (state : State) : State :=
  { state with machine := { state.machine with pc := state.machine.pc + 1 } }

/-- A single bounded word write, without advancing the program counter. -/
def State.setWord (width : ℕ) (state : State) (destination value : ℕ) : State :=
  { state with machine := { state.machine with
      registers := Function.update state.machine.registers destination
        (WordRAM.normalizeWord width value) } }

/-- A single real-register write, without advancing the program counter. -/
def State.setReal (state : State) (destination : ℕ) (value : ℝ) : State :=
  { state with registers := Function.update state.registers destination value }

def readWords (memory : ℕ → ℕ) (start length : ℕ) : List ℕ :=
  (List.range length).map fun offset => memory (start + offset)

def readReals (memory : ℕ → ℝ) (start length : ℕ) : List ℝ :=
  (List.range length).map fun offset => memory (start + offset)

/-- Adapters must check the destination range and charge the written cells. -/
def writeWords : (ℕ → ℕ) → ℕ → List ℕ → (ℕ → ℕ)
  | memory, _, [] => memory
  | memory, start, value :: tail =>
      writeWords (Function.update memory start value) (start + 1) tail

/-- A request pauses at a fixed external instruction. Its four operands are program
metadata, not arbitrary input-dependent functions. -/
inductive Status (Operation : Type)
  | running
  | halted (words : List ℕ) (reals : List ℝ)
  | faulted
  | request (operation : Operation) (a b c d : ℕ)

structure StepResult (Operation : Type) where
  state : State
  status : Status Operation
  cost : ℕ

private def continuing {Operation : Type} (state : State) : StepResult Operation :=
  ⟨state.advance, .running, 1⟩

private def fault {Operation : Type} (state : State) (cost : ℕ := 1) :
    StepResult Operation := ⟨state, .faulted, cost⟩

@[simp] theorem continuing_state {Operation : Type} (state : State) :
    (continuing (Operation := Operation) state).state = state.advance := rfl

@[simp] theorem continuing_status {Operation : Type} (state : State) :
    (continuing (Operation := Operation) state).status = .running := rfl

@[simp] theorem continuing_cost {Operation : Type} (state : State) :
    (continuing (Operation := Operation) state).cost = 1 := rfl

@[simp] theorem fault_state {Operation : Type} (state : State) (cost : ℕ) :
    (fault (Operation := Operation) state cost).state = state := rfl

@[simp] theorem fault_status {Operation : Type} (state : State) (cost : ℕ) :
    (fault (Operation := Operation) state cost).status = .faulted := rfl

@[simp] theorem fault_cost {Operation : Type} (state : State) (cost : ℕ) :
    (fault (Operation := Operation) state cost).cost = cost := rfl

/-- All local computation is defined by the finite instruction constructors. The external
branch advances once before the fixed adapter supplies its reply. -/
noncomputable def step {Operation : Type} [Fintype Operation] (width : ℕ)
    (program : Program Operation) (state : State) : StepResult Operation := by
  classical
  exact match program.code[state.machine.pc]? with
  | none => fault state
  | some (.word _) =>
      let result := WordRAM.step width program.wordProgram state.machine
      let status := match result.status with
        | .running => .running
        | .halted output => .halted output []
        | .faulted => .faulted
      ⟨{ state with machine := result.state }, status, result.cost⟩
  | some (.rational destination value) =>
      continuing (state.setReal destination (value : ℝ))
  | some (.move destination source) =>
      continuing (state.setReal destination (state.registers source))
  | some (.load destination address) =>
      continuing (state.setReal destination (state.memory (state.machine.registers address)))
  | some (.store address source) =>
      let memory := Function.update state.memory
        (state.machine.registers address) (state.registers source)
      continuing { state with memory }
  | some (.add destination left right) =>
      continuing (state.setReal destination (state.registers left + state.registers right))
  | some (.sub destination left right) =>
      continuing (state.setReal destination (state.registers left - state.registers right))
  | some (.mul destination left right) =>
      continuing (state.setReal destination (state.registers left * state.registers right))
  | some (.div destination left right) =>
      if state.registers right = 0 then fault state
      else continuing (state.setReal destination (state.registers left / state.registers right))
  | some (.less destination left right) =>
      continuing (state.setWord width destination
        (if state.registers left < state.registers right then 1 else 0))
  | some (.equal destination left right) =>
      continuing (state.setWord width destination
        (if state.registers left = state.registers right then 1 else 0))
  | some (.fromWord destination source) =>
      continuing (state.setReal destination (state.machine.registers source : ℝ))
  | some (.external operation a b c d) =>
      ⟨state.advance, .request operation a b c d, 1⟩
  | some (.haltReal wordStart wordLength realStart realLength) =>
      let ws := state.machine.registers wordStart
      let wn := state.machine.registers wordLength
      let rs := state.machine.registers realStart
      let rn := state.machine.registers realLength
      if ws + wn ≤ WordRAM.wordModulus width ∧ rs + rn ≤ WordRAM.wordModulus width then
        ⟨state, .halted (readWords state.machine.memory ws wn) (readReals state.memory rs rn),
          wn + rn + 1⟩
      else fault state

end EconCSLib.OpenProblem.New.ExactRealController

end
