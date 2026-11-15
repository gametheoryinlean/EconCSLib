/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.PCPForPPAD.Problem

/-!
# PCPForPPAD: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Normalized generalized circuits

The nine-gate normalized convention follows DFHM (2026), Section 2.2.2. Each node has
exactly one producing gate, possibly with cyclic dependencies. Epsilon bounds local
gate error; delta bounds the fraction of violated gates (BPR, Definition 3), not
distance to a fixed point.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

/-- Increasing only the allowed fraction of failed gates weakens the target. No
corresponding monotonicity in epsilon is presumed for Boolean gates. -/
theorem IsApproximateSolution.mono_delta {nodes : ℕ} {ε δ δ' : ℝ}
    {circuit : GeneralizedCircuit nodes} {x : Fin nodes → ℝ}
    (h : IsApproximateSolution ε δ circuit x) (hδ : δ ≤ δ') :
    IsApproximateSolution ε δ' circuit x :=
  ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg nodes))⟩

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


section

/-!
## Fixed structural codes for the reduction endpoints

The End-of-Line input contains Boolean circuits, not its exponential graph. All wire
indices and rational numerators/denominators are encoded. The target assignment is
explicit and has no hidden fixed precision cap.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD
open WordRAM.FiniteData

/-- Length-framed gate records with unambiguous boundaries. -/
def blocksCode (blocks : List Code) : Code :=
  natCode blocks.length ++ blocks.flatMap (fun block => natCode block.length ++ block)

def booleanWireCode {inputs previous : ℕ} :
    BooleanGateInput inputs previous → Code
  | .input i => [false] ++ natCode i.val
  | .previous i => [true] ++ natCode i.val

def booleanGateCode {inputs previous : ℕ} : BooleanGate inputs previous → Code
  | .constant b => natCode 0 ++ [b]
  | .not a => natCode 1 ++ booleanWireCode a
  | .and a b => natCode 2 ++ booleanWireCode a ++ booleanWireCode b
  | .or a b => natCode 3 ++ booleanWireCode a ++ booleanWireCode b
  | .xor a b => natCode 4 ++ booleanWireCode a ++ booleanWireCode b

/-- Explicit arity and output wires. Only the source Boolean circuits are DAGs. -/
def booleanCircuitCode {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs) : Code :=
  natCode inputs ++ natCode outputs ++
    blocksCode (List.ofFn fun i => booleanGateCode (circuit.gate i)) ++
    blocksCode (List.ofFn fun i => booleanWireCode (circuit.output i))

def endOfLineInputCode (input : EndOfLineInput) : Code :=
  natCode input.bits ++
    pairCode (booleanCircuitCode input.successor) (booleanCircuitCode input.predecessor)

/-- A source vertex has exactly the declared number of bits. -/
def endOfLineOutputCode (input : EndOfLineInput) (vertex : EndOfLineOutput input) : Code :=
  List.ofFn vertex

/-- The gate tag determines its arity; record position determines its output. -/
def generalizedGateCode {nodes : ℕ} : GeneralizedGate (Fin nodes) → Code
  | .constant q => natCode 0 ++ ratCode q
  | .scale q a => natCode 1 ++ ratCode q ++ natCode a.val
  | .copy a => natCode 2 ++ natCode a.val
  | .add a b => natCode 3 ++ natCode a.val ++ natCode b.val
  | .sub a b => natCode 4 ++ natCode a.val ++ natCode b.val
  | .less a b => natCode 5 ++ natCode a.val ++ natCode b.val
  | .disj a b => natCode 6 ++ natCode a.val ++ natCode b.val
  | .conj a b => natCode 7 ++ natCode a.val ++ natCode b.val
  | .neg a => natCode 8 ++ natCode a.val

/-- The number of records is the node count, without value-dependent padding. -/
def generalizedCircuitCode (input : GeneralizedCircuitInput) : Code :=
  blocksCode (List.ofFn fun i => generalizedGateCode (input.2.gate i))

/-- The exact rational assignment, including its dimension and every
numerator/denominator. -/
def assignmentCode {nodes : ℕ} (x : Fin nodes → ℚ) : Code :=
  blocksCode (List.ofFn fun i => ratCode (x i))

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


section

/-!
## Auxiliary real-coefficient normalized generalized circuits

This extends the reference's rational coefficients to the real unit interval; it is
not the input convention of the main source-level conjecture. The nine gate
constraints and the exactly-one-producer convention are retained. Delta bounds the
fraction of violated gates. `CorrectRealReduction` requires correctness for every real
target assignment; it certifies neither polynomial runtime nor PPAD-hardness.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

inductive RealGeneralizedGate (Node : Type*)
  | constant (value : ℝ)
  | scale (factor : ℝ) (input : Node)
  | copy (input : Node)
  | add (left right : Node)
  | sub (left right : Node)
  | less (left right : Node)
  | disj (left right : Node)
  | conj (left right : Node)
  | neg (input : Node)

def RealGeneralizedGate.ParametersValid {Node : Type*} : RealGeneralizedGate Node → Prop
  | .constant q | .scale q _ => 0 ≤ q ∧ q ≤ 1
  | _ => True

def RealGeneralizedGate.IsSatisfied {Node : Type*}
    (ε : ℝ) (x : Node → ℝ) (output : Node) : RealGeneralizedGate Node → Prop
  | .constant q => Within ε (x output) q
  | .scale q input => Within ε (x output) (min (x input * q) 1)
  | .copy input => Within ε (x output) (x input)
  | .add left right => Within ε (x output) (min (x left + x right) 1)
  | .sub left right => Within ε (x output) (max (x left - x right) 0)
  | .less left right =>
      (x left < x right - ε → Within ε (x output) 1) ∧
      (x right + ε < x left → Within ε (x output) 0)
  | .disj left right =>
      ((1 - ε ≤ x left ∨ 1 - ε ≤ x right) → Within ε (x output) 1) ∧
      ((x left ≤ ε ∧ x right ≤ ε) → Within ε (x output) 0)
  | .conj left right =>
      ((1 - ε ≤ x left ∧ 1 - ε ≤ x right) → Within ε (x output) 1) ∧
      ((x left ≤ ε ∨ x right ≤ ε) → Within ε (x output) 0)
  | .neg input =>
      (x input ≤ ε → Within ε (x output) 1) ∧
      (1 - ε ≤ x input → Within ε (x output) 0)

/-- Cast coefficients exactly without rounding or changing gate constraints. -/
noncomputable def GeneralizedGate.realView {Node : Type*} : GeneralizedGate Node → RealGeneralizedGate Node
  | .constant q => .constant (q : ℝ)
  | .scale q input => .scale (q : ℝ) input
  | .copy input => .copy input
  | .add left right => .add left right
  | .sub left right => .sub left right
  | .less left right => .less left right
  | .disj left right => .disj left right
  | .conj left right => .conj left right
  | .neg input => .neg input

structure RealGeneralizedCircuit (nodes : ℕ) where
  gate : Fin nodes → RealGeneralizedGate (Fin nodes)
  parameters_valid : ∀ i, (gate i).ParametersValid

noncomputable def realViolatedGates {nodes : ℕ} (ε : ℝ)
    (circuit : RealGeneralizedCircuit nodes) (x : Fin nodes → ℝ) : Finset (Fin nodes) := by
  classical
  exact Finset.univ.filter fun i => ¬ (circuit.gate i).IsSatisfied ε x i

noncomputable def IsRealApproximateSolution {nodes : ℕ} (ε δ : ℝ)
    (circuit : RealGeneralizedCircuit nodes) (x : Fin nodes → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ((realViolatedGates ε circuit x).card : ℝ) ≤ δ * (nodes : ℝ)

abbrev RealGeneralizedCircuitInput := Σ nodes : ℕ, RealGeneralizedCircuit nodes

/-- Every real target solution must map to a source solution. This condition alone makes
no runtime assertion. -/
noncomputable def CorrectRealReduction (ε δ : ℝ)
    (mapInput : EndOfLineInput → RealGeneralizedCircuitInput)
    (mapOutput : (I : EndOfLineInput) →
      (Fin (mapInput I).1 → ℝ) → EndOfLineOutput I) : Prop :=
  ∀ I x, IsRealApproximateSolution ε δ (mapInput I).2 x →
    IsEndOfLineSolution I (mapOutput I x)

/-- A real correctness contract at admissible positive constants. The maps are not
required to be effective, so this is not a hardness claim. -/
noncomputable def ReferenceRealReduction (ε δ : ℝ)
    (mapInput : EndOfLineInput → RealGeneralizedCircuitInput)
    (mapOutput : (I : EndOfLineInput) →
      (Fin (mapInput I).1 → ℝ) → EndOfLineOutput I) : Prop :=
  ReferenceTolerances ε δ ∧ CorrectRealReduction ε δ mapInput mapOutput

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


section

/-!
## Optional rational-assignment Word-RAM reduction

Both maps run on fixed structural encodings and preserve every encoded target
solution. This separate machine-level question is not the definition of the
source-level PCP-for-PPAD conjecture, and no equivalence with standard PPAD or with
the original quasilinear reduction is asserted.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD
open WordRAM.FiniteData

/-- Reuse the shared End-of-Line source with a valid distinguished outgoing edge. -/
def canonicalEndOfLineProblem : WordRAM.Search.Problem where
  valid code := ∃ input : EndOfLineInput, code = endOfLineInputCode input
  solution code output := ∃ input : EndOfLineInput,
    code = endOfLineInputCode input ∧
      ∃ vertex : EndOfLineOutput input,
        output = endOfLineOutputCode input vertex ∧ IsEndOfLineSolution input vertex

/-- The fixed encoded search relation uses one shared rational assignment for every gate;
it is distinct from the all-real mathematical relation. -/
noncomputable def generalizedCircuitProblem (ε δ : ℝ) : WordRAM.Search.Problem where
  valid code := ∃ input : GeneralizedCircuitInput, code = generalizedCircuitCode input
  solution code output := ∃ input : GeneralizedCircuitInput,
    code = generalizedCircuitCode input ∧
      ∃ x : Fin input.1 → ℚ,
        output = assignmentCode x ∧
          IsApproximateSolution ε δ input.2 (fun i => (x i : ℝ))

/-- Two positive unit-interval constants chosen before the reduction and all instances.
Both maps are actual Word-RAM programs; the backward map handles every encoded target
solution and is charged on the source/output pair. -/
noncomputable def ReferencePCPForPPADRationalWordRAMStatement : Prop :=
  ∃ ε δ : ℝ, ReferenceTolerances ε δ ∧
    WordRAM.Search.ReducesTo canonicalEndOfLineProblem (generalizedCircuitProblem ε δ)

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end
