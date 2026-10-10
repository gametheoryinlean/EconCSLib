/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fin.Tuple.Basic



section

/-!
# Boolean circuits and End-of-Line

Gates are evaluated in dependency order. This file defines circuits and the
End-of-Line relation; it does not assign solver-declared costs or prove a
complexity-model equivalence. The optional Word-RAM reduction in `PCPForPPAD` uses
structural bit encodings and `WordRAM.Search.Reduction`.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench

/-!
## Succinct Boolean circuits
-/

/-- A wire available to gate `previous`: either a primary input or an earlier gate. -/
inductive BooleanGateInput (inputs previous : ℕ)
  | input (index : Fin inputs)
  | previous (index : Fin previous)

/-- Constant-fan-in Boolean gate basis. -/
inductive BooleanGate (inputs previous : ℕ)
  | constant (value : Bool)
  | not (input : BooleanGateInput inputs previous)
  | and (left right : BooleanGateInput inputs previous)
  | or (left right : BooleanGateInput inputs previous)
  | xor (left right : BooleanGateInput inputs previous)

def BooleanGateInput.eval {inputs previous : ℕ}
    (primary : Fin inputs → Bool) (computed : Fin previous → Bool) :
    BooleanGateInput inputs previous → Bool
  | .input index => primary index
  | .previous index => computed index

def BooleanGate.eval {inputs previous : ℕ}
    (primary : Fin inputs → Bool) (computed : Fin previous → Bool) :
    BooleanGate inputs previous → Bool
  | .constant value => value
  | .not input => !(input.eval primary computed)
  | .and left right =>
      (left.eval primary computed) && (right.eval primary computed)
  | .or left right =>
      (left.eval primary computed) || (right.eval primary computed)
  | .xor left right =>
      Bool.xor (left.eval primary computed) (right.eval primary computed)

/-- A topologically ordered acyclic Boolean circuit. -/
structure BooleanCircuit (inputs outputs : ℕ) where
  gateCount : ℕ
  gate : (index : Fin gateCount) → BooleanGate inputs index.val
  output : Fin outputs → BooleanGateInput inputs gateCount

/-- Evaluate the first `count` gates. -/
def BooleanCircuit.evalPrefix {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs)
    (primary : Fin inputs → Bool) :
    (count : ℕ) → count ≤ circuit.gateCount → Fin count → Bool
  | 0, _ => Fin.elim0
  | count + 1, hcount =>
      let prior := circuit.evalPrefix primary count
        (Nat.le_trans (Nat.le_succ count) hcount)
      let gateIndex : Fin circuit.gateCount :=
        ⟨count, Nat.lt_of_succ_le hcount⟩
      let value := (circuit.gate gateIndex).eval primary prior
      Fin.snoc prior value

/-- Evaluate every output wire. -/
def BooleanCircuit.eval {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs)
    (primary : Fin inputs → Bool) : Fin outputs → Bool :=
  let computed := circuit.evalPrefix primary circuit.gateCount le_rfl
  fun output => (circuit.output output).eval primary computed

/-- Structural size, not encoded bit length. Runtime interfaces must also encode wire
indices. -/
def BooleanCircuit.wordSize {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs) : ℕ :=
  inputs + outputs + circuit.gateCount

/-!
## End-of-Line
-/

def zeroBitVector (bits : ℕ) : Fin bits → Bool := fun _ => false

/-- Succinct End-of-Line instance with the designated source promise `P(0)=0`, `S(0)≠0`,
`P(S(0))=0`. -/
structure EndOfLineInput where
  bits : ℕ
  successor : BooleanCircuit bits bits
  predecessor : BooleanCircuit bits bits
  predecessor_source : predecessor.eval (zeroBitVector bits) =
    zeroBitVector bits
  successor_source : successor.eval (zeroBitVector bits) ≠
    zeroBitVector bits
  /-- The predecessor must recognize the distinguished outgoing edge. -/
  source_edge : predecessor.eval (successor.eval (zeroBitVector bits)) =
    zeroBitVector bits

abbrev EndOfLineOutput (input : EndOfLineInput) :=
  Fin input.bits → Bool

/-- A non-source vertex where predecessor/successor consistency fails. -/
def IsEndOfLineSolution (input : EndOfLineInput)
    (vertex : EndOfLineOutput input) : Prop :=
  vertex ≠ zeroBitVector input.bits ∧
    (input.predecessor.eval (input.successor.eval vertex) ≠ vertex ∨
      input.successor.eval (input.predecessor.eval vertex) ≠ vertex)


end EconCSLib.OpenProblem.New.EconCSBench

end
