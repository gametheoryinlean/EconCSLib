/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity

/-!
# Explicit PPAD hardness through End-of-Line

This module replaces the former proposition-valued `PPADHard := True` hook.
The canonical source problem is succinct End-of-Line: predecessor and
successor maps on bit vectors are represented by finite acyclic Boolean
circuits.  A target is PPAD-hard exactly when an explicit polynomial search
reduction from this source problem exists.  `StrictPPADHard` is the preferred
instruction-enforced definition; the shorter `PPADHard` name is retained as a
trusted-instrumentation compatibility layer until each benchmark supplies
canonical encodings.

The circuit is a topologically ordered DAG.  Gate `i` may refer only to input
wires or gates with index strictly below `i`, so evaluation is structurally
total and no separate acyclicity oracle is needed.  Circuit size is measured
in unit-cost words: every constant-fan-in gate and wire reference occupies a
constant number of words.

This is the directed parity class introduced by Papadimitriou, *On the
Complexity of the Parity Argument and Other Inefficient Proofs of Existence*,
JCSS 48 (1994), 498--532.  The surrounding `SearchProblem` interface follows
the total-search-relation viewpoint of Megiddo and Papadimitriou (1991).
-/

namespace EconCSLib
namespace OpenProblem
namespace EconCSBench

/-! ## Succinct Boolean circuits -/

/-- A wire available to gate `previous`: either a primary input or an earlier
gate. -/
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

/-- Unit-cost word size of a circuit. -/
def BooleanCircuit.wordSize {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs) : ℕ :=
  inputs + outputs + circuit.gateCount

/-- Explicit operation count for evaluating every gate and reading every
output wire once. -/
def BooleanCircuit.evalCost {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs)
    (primary : Fin inputs → Bool) : UnitCostRAM.Cost (Fin outputs → Bool) :=
  ⟨circuit.eval primary, circuit.gateCount + outputs⟩

def BooleanCircuit.evalImplementation {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs) :
    UnitCostRAM.CostedImplementation circuit.eval where
  run := circuit.evalCost
  correct := fun _ => rfl

/-! ## End-of-Line -/

def zeroBitVector (bits : ℕ) : Fin bits → Bool := fun _ => false

/-- Succinct End-of-Line instance with the standard designated source
promise `P(0)=0 ≠ S(0)`. -/
structure EndOfLineInput where
  bits : ℕ
  successor : BooleanCircuit bits bits
  predecessor : BooleanCircuit bits bits
  predecessor_source : predecessor.eval (zeroBitVector bits) =
    zeroBitVector bits
  successor_source : successor.eval (zeroBitVector bits) ≠
    zeroBitVector bits

abbrev EndOfLineOutput (input : EndOfLineInput) :=
  Fin input.bits → Bool

/-- A non-source vertex where predecessor/successor consistency fails. -/
def IsEndOfLineSolution (input : EndOfLineInput)
    (vertex : EndOfLineOutput input) : Prop :=
  vertex ≠ zeroBitVector input.bits ∧
    (input.predecessor.eval (input.successor.eval vertex) ≠ vertex ∨
      input.successor.eval (input.predecessor.eval vertex) ≠ vertex)

/-- Succinct End-of-Line as a representation-aware search problem. -/
def endOfLineProblem : SearchProblem where
  Input := EndOfLineInput
  Output := EndOfLineOutput
  validInput := fun _ => True
  isSolution := IsEndOfLineSolution
  inputSize := fun input =>
    input.bits + input.successor.wordSize + input.predecessor.wordSize
  outputSize := fun input _ => input.bits

/-- Legacy audited/instrumented PPAD-hardness predicate.  This is retained for
existing benchmark statements, but its reduction programs use trusted
`CostM` annotations.  New complexity-class claims should use
`StrictPPADHard` below. -/
def PPADHard (target : SearchProblem) : Prop :=
  SearchReducesTo endOfLineProblem target

/-! ## Fixed-representation, instruction-enforced PPAD -/

/-- A fixed representation of succinct End-of-Line.  The representation is a
parameter of the surrounding development, not a field of an individual
reduction witness.  A concrete benchmark should define one canonical
gate-list encoding and reuse it for every hardness theorem. -/
structure EndOfLineFixedEncoding where
  input : UnitCostRAM.Encoding EndOfLineInput
  output : UnitCostRAM.DependentEncoding EndOfLineOutput

/-- Succinct End-of-Line equipped with a fixed unit-cost RAM presentation. -/
def fixedEndOfLineProblem
    (encoding : EndOfLineFixedEncoding) : FixedEncodingSearchProblem where
  Input := EndOfLineInput
  Output := EndOfLineOutput
  validInput := fun _ => True
  isSolution := IsEndOfLineSolution
  inputEncoding := encoding.input
  outputEncoding := encoding.output

/-- Instruction-enforced PPAD hardness.  Both the End-of-Line and target
representations are fixed before the finite reduction programs are chosen. -/
def StrictPPADHard
    (sourceEncoding : EndOfLineFixedEncoding)
    (target : FixedEncodingSearchProblem) : Prop :=
  FixedSearchReducesTo (fixedEndOfLineProblem sourceEncoding) target

end EconCSBench
end OpenProblem
end EconCSLib
