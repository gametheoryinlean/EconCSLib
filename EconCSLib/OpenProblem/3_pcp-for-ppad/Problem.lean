/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

namespace EconCSLib.OpenProblem.EconCSBench.PCPForPPAD

/-! ## Canonical finite-word encodings -/

/-- Turn an injective structural word representation into a lossless fixed
encoding.  The decoder selects the unique preimage of a valid code; the
representation itself is fixed independently of any reduction witness. -/
noncomputable def structuralEncodingOfInjective {α : Type*}
    (encode : α → List UnitCostRAM.Word) (hinjective : Function.Injective encode) :
    UnitCostRAM.Encoding α := by
  classical
  exact
    { encode := encode
      decode := fun words =>
        if h : ∃ value, encode value = words then
          some (Classical.choose h)
        else
          none
      decode_encode := fun value => by
        rw [dif_pos ⟨value, rfl⟩]
        congr 1
        apply hinjective
        exact Classical.choose_spec
          (show ∃ candidate, encode candidate = encode value from ⟨value, rfl⟩) }

/-- Length-frame a list of structural records.  Framing prevents adjacent
variable-arity gate records from being confused. -/
def encodeWordBlocks : List (List UnitCostRAM.Word) → List UnitCostRAM.Word
  | [] => []
  | block :: blocks =>
      .integer block.length :: block ++ encodeWordBlocks blocks

theorem encodeWordBlocks_injective : Function.Injective encodeWordBlocks := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons block blocks =>
          simp [encodeWordBlocks] at h
  | cons block blocks ih =>
      intro right h
      cases right with
      | nil =>
          simp [encodeWordBlocks] at h
      | cons otherBlock otherBlocks =>
          simp only [encodeWordBlocks] at h
          have hlength : block.length = otherBlock.length := by
            simpa using congrArg List.head? h
          have htail :
              block ++ encodeWordBlocks blocks =
                otherBlock ++ encodeWordBlocks otherBlocks := by
            simpa using congrArg List.tail h
          have hblock : block = otherBlock := by
            have := congrArg (List.take block.length) htail
            simpa [hlength] using this
          subst otherBlock
          have hblocks : blocks = otherBlocks := by
            apply ih
            exact List.append_right_injective block htail
          subst otherBlocks
          rfl

/-- One exact-real word per coordinate. -/
def encodeRealVector (dimension : ℕ) (value : Fin dimension → ℝ) :
    List UnitCostRAM.Word :=
  List.ofFn fun index => .real (value index)

theorem encodeRealVector_injective (dimension : ℕ) :
    Function.Injective (encodeRealVector dimension) := by
  intro left right h
  have hcoordinates :
      (fun index : Fin dimension => UnitCostRAM.Word.real (left index)) =
        fun index : Fin dimension => UnitCostRAM.Word.real (right index) :=
    List.ofFn_injective h
  funext index
  simpa using congrFun hcoordinates index

/-- One Boolean word per coordinate. -/
def encodeBoolVector (dimension : ℕ) (value : Fin dimension → Bool) :
    List UnitCostRAM.Word :=
  List.ofFn fun index => .bit (value index)

theorem encodeBoolVector_injective (dimension : ℕ) :
    Function.Injective (encodeBoolVector dimension) := by
  intro left right h
  have hcoordinates :
      (fun index : Fin dimension => UnitCostRAM.Word.bit (left index)) =
        fun index : Fin dimension => UnitCostRAM.Word.bit (right index) :=
    List.ofFn_injective h
  funext index
  simpa using congrFun hcoordinates index

/-- Canonical encoding of a fixed-length exact-real vector. -/
noncomputable def realVectorEncoding (dimension : ℕ) :
    UnitCostRAM.Encoding (Fin dimension → ℝ) :=
  structuralEncodingOfInjective
    (encodeRealVector dimension) (encodeRealVector_injective dimension)

/-- Canonical encoding of a fixed-length bit vector. -/
noncomputable def boolVectorEncoding (dimension : ℕ) :
    UnitCostRAM.Encoding (Fin dimension → Bool) :=
  structuralEncodingOfInjective
    (encodeBoolVector dimension) (encodeBoolVector_injective dimension)

/-! ### Canonical End-of-Line representation -/

/-- Structural encoding of a reference to either a primary input or an
earlier Boolean-circuit gate. -/
def encodeBooleanGateInput {inputs previous : ℕ} :
    BooleanGateInput inputs previous → List UnitCostRAM.Word
  | .input index => [.integer 0, .integer index.val]
  | .previous index => [.integer 1, .integer index.val]

theorem encodeBooleanGateInput_injective {inputs previous : ℕ} :
    Function.Injective
      (encodeBooleanGateInput (inputs := inputs) (previous := previous)) := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [encodeBooleanGateInput, Fin.ext_iff]

/-- Structural constant-fan-in record for a Boolean gate. -/
def encodeBooleanGate {inputs previous : ℕ} :
    BooleanGate inputs previous → List UnitCostRAM.Word
  | .constant value => encodeWordBlocks [[.integer 0], [.bit value]]
  | .not input => encodeWordBlocks [[.integer 1], encodeBooleanGateInput input]
  | .and left right =>
      encodeWordBlocks
        [[.integer 2], encodeBooleanGateInput left, encodeBooleanGateInput right]
  | .or left right =>
      encodeWordBlocks
        [[.integer 3], encodeBooleanGateInput left, encodeBooleanGateInput right]
  | .xor left right =>
      encodeWordBlocks
        [[.integer 4], encodeBooleanGateInput left, encodeBooleanGateInput right]

theorem encodeBooleanGate_injective {inputs previous : ℕ} :
    Function.Injective
      (encodeBooleanGate (inputs := inputs) (previous := previous)) := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [encodeBooleanGate, encodeWordBlocks_injective.eq_iff,
      encodeBooleanGateInput_injective.eq_iff]

/-- Canonical gate-list encoding of a topologically ordered Boolean circuit.
The redundant input/output wire declarations make the word length reflect the
wire dimensions used by `BooleanCircuit.wordSize`. -/
def encodeBooleanCircuit {inputs outputs : ℕ}
    (circuit : BooleanCircuit inputs outputs) : List UnitCostRAM.Word :=
  encodeWordBlocks
    [[.integer circuit.gateCount],
      List.ofFn (fun index : Fin inputs => .integer index.val),
      List.ofFn (fun index : Fin outputs => .integer index.val),
      encodeWordBlocks
        (List.ofFn fun index : Fin circuit.gateCount =>
          encodeBooleanGate (circuit.gate index)),
      encodeWordBlocks
        (List.ofFn fun index : Fin outputs =>
          encodeBooleanGateInput (circuit.output index))]

theorem encodeBooleanCircuit_injective {inputs outputs : ℕ} :
    Function.Injective
      (encodeBooleanCircuit (inputs := inputs) (outputs := outputs)) := by
  intro left right h
  have hrecords := encodeWordBlocks_injective h
  simp only [List.cons.injEq, and_true] at hrecords
  rcases hrecords with ⟨hcount, _hinputs, _houtputs, hgates, hresult⟩
  have hgateCount : left.gateCount = right.gateCount := by
    simpa using hcount
  cases left with
  | mk leftCount leftGate leftOutput =>
      cases right with
      | mk rightCount rightGate rightOutput =>
          dsimp at hgateCount hgates hresult ⊢
          subst rightCount
          have hgateCodes := encodeWordBlocks_injective hgates
          have hgateFunctions :
              (fun index : Fin leftCount => encodeBooleanGate (leftGate index)) =
                fun index : Fin leftCount => encodeBooleanGate (rightGate index) :=
            List.ofFn_injective hgateCodes
          have hgatesEqual : leftGate = rightGate := by
            funext index
            exact encodeBooleanGate_injective (congrFun hgateFunctions index)
          have houtputCodes := encodeWordBlocks_injective hresult
          have houtputFunctions :
              (fun index : Fin outputs => encodeBooleanGateInput (leftOutput index)) =
                fun index : Fin outputs => encodeBooleanGateInput (rightOutput index) :=
            List.ofFn_injective houtputCodes
          have houtputsEqual : leftOutput = rightOutput := by
            funext index
            exact encodeBooleanGateInput_injective
              (congrFun houtputFunctions index)
          cases hgatesEqual
          cases houtputsEqual
          rfl

/-- Canonical structural encoding of a succinct End-of-Line instance. -/
def encodeEndOfLineInput (input : EndOfLineInput) : List UnitCostRAM.Word :=
  encodeWordBlocks
    [[.integer input.bits],
      List.ofFn (fun index : Fin input.bits => .integer index.val),
      encodeBooleanCircuit input.successor,
      encodeBooleanCircuit input.predecessor]

theorem encodeEndOfLineInput_injective :
    Function.Injective encodeEndOfLineInput := by
  intro left right h
  have hrecords := encodeWordBlocks_injective h
  simp only [List.cons.injEq, and_true] at hrecords
  rcases hrecords with ⟨hbits, _hvertices, hsuccessor, hpredecessor⟩
  have hdimension : left.bits = right.bits := by
    simpa using hbits
  cases left with
  | mk leftBits leftSuccessor leftPredecessor leftPredecessorSource
      leftSuccessorSource =>
      cases right with
      | mk rightBits rightSuccessor rightPredecessor rightPredecessorSource
          rightSuccessorSource =>
          dsimp at hdimension hsuccessor hpredecessor ⊢
          subst rightBits
          have hsucc : leftSuccessor = rightSuccessor :=
            encodeBooleanCircuit_injective hsuccessor
          have hpred : leftPredecessor = rightPredecessor :=
            encodeBooleanCircuit_injective hpredecessor
          cases hsucc
          cases hpred
          rfl

/-- Fixed canonical input encoding for the End-of-Line benchmark. -/
noncomputable def canonicalEndOfLineInputEncoding :
    UnitCostRAM.Encoding EndOfLineInput :=
  structuralEncodingOfInjective
    encodeEndOfLineInput encodeEndOfLineInput_injective

/-- Fixed canonical output encoding for End-of-Line vertices. -/
noncomputable def canonicalEndOfLineOutputEncoding :
    UnitCostRAM.DependentEncoding EndOfLineOutput where
  encode input output := (boolVectorEncoding input.bits).encode output
  decode input words := (boolVectorEncoding input.bits).decode words
  decode_encode input output :=
    (boolVectorEncoding input.bits).decode_encode output

/-- Canonical fixed representation of the End-of-Line source problem. -/
noncomputable def canonicalEndOfLineEncoding : EndOfLineFixedEncoding where
  input := canonicalEndOfLineInputEncoding
  output := canonicalEndOfLineOutputEncoding

/-- The nine standard gate forms used by generalized circuits. -/
inductive GeneralizedGate (Node : Type*)
  | constant (α : ℝ) (output : Node)
  | scale (α : ℝ) (input output : Node)
  | copy (input output : Node)
  | add (left right output : Node)
  | sub (left right output : Node)
  | less (left right output : Node)
  | disj (left right output : Node)
  | conj (left right output : Node)
  | neg (input output : Node)

/-- Output node of a generalized-circuit gate. -/
def GeneralizedGate.output {Node : Type*} : GeneralizedGate Node → Node
  | .constant _ output
  | .scale _ _ output
  | .copy _ output
  | .add _ _ output
  | .sub _ _ output
  | .less _ _ output
  | .disj _ _ output
  | .conj _ _ output
  | .neg _ output => output

/-- Side conditions on the scalar parameters of standard generalized-circuit
gates.  Constants and scaling coefficients belong to `[0,1]`. -/
def GeneralizedGate.ParametersValid {Node : Type*} :
    GeneralizedGate Node → Prop
  | .constant α _ => 0 ≤ α ∧ α ≤ 1
  | .scale α _ _ => 0 ≤ α ∧ α ≤ 1
  | _ => True

/-- `a = b ± ε`. -/
def Within (ε a b : ℝ) : Prop :=
  |a - b| ≤ ε

/-- Approximate satisfaction of one standard generalized-circuit gate.  The
Boolean/comparison gates impose no condition in their indeterminate zone,
exactly as in the source definition of `(ε,δ)`-GCircuit. -/
def GeneralizedGate.IsSatisfied
    {Node : Type*} (ε : ℝ) (x : Node → ℝ) :
    GeneralizedGate Node → Prop
  | .constant α output =>
      Within ε (x output) α
  | .scale α input output =>
      Within ε (x output) (α * x input)
  | .copy input output =>
      Within ε (x output) (x input)
  | .add left right output =>
      Within ε (x output) (min (x left + x right) 1)
  | .sub left right output =>
      Within ε (x output) (max (x left - x right) 0)
  | .less left right output =>
      (x left < x right - ε → Within ε (x output) 1) ∧
      (x right + ε < x left → Within ε (x output) 0)
  | .disj left right output =>
      ((Within ε (x left) 1 ∨ Within ε (x right) 1) →
        Within ε (x output) 1) ∧
      ((Within ε (x left) 0 ∧ Within ε (x right) 0) →
        Within ε (x output) 0)
  | .conj left right output =>
      ((Within ε (x left) 1 ∧ Within ε (x right) 1) →
        Within ε (x output) 1) ∧
      ((Within ε (x left) 0 ∨ Within ε (x right) 0) →
        Within ε (x output) 0)
  | .neg input output =>
      (Within ε (x input) 0 → Within ε (x output) 1) ∧
      (Within ε (x input) 1 → Within ε (x output) 0)

/-- A generalized circuit is a finite family of standard local gates, with at
most one gate producing any given node. -/
structure GeneralizedCircuit (nodes gates : ℕ) where
  /-- Gate syntax. -/
  gate : Fin gates → GeneralizedGate (Fin nodes)
  /-- Every scalar gate has a legal unit-interval parameter. -/
  parameters_valid : ∀ g, (gate g).ParametersValid
  /-- Distinct gates have distinct output nodes. -/
  output_injective : Function.Injective (fun g => (gate g).output)

/-- Canonical structural record for a generalized-circuit gate.  Exact scalar
parameters use real words, while gate tags and wire references use integer
words. -/
def encodeGeneralizedGate {nodes : ℕ} :
    GeneralizedGate (Fin nodes) → List UnitCostRAM.Word
  | .constant α output =>
      encodeWordBlocks [[.integer 0], [.real α], [.integer output.val]]
  | .scale α input output =>
      encodeWordBlocks
        [[.integer 1], [.real α], [.integer input.val], [.integer output.val]]
  | .copy input output =>
      encodeWordBlocks [[.integer 2], [.integer input.val], [.integer output.val]]
  | .add left right output =>
      encodeWordBlocks
        [[.integer 3], [.integer left.val], [.integer right.val],
          [.integer output.val]]
  | .sub left right output =>
      encodeWordBlocks
        [[.integer 4], [.integer left.val], [.integer right.val],
          [.integer output.val]]
  | .less left right output =>
      encodeWordBlocks
        [[.integer 5], [.integer left.val], [.integer right.val],
          [.integer output.val]]
  | .disj left right output =>
      encodeWordBlocks
        [[.integer 6], [.integer left.val], [.integer right.val],
          [.integer output.val]]
  | .conj left right output =>
      encodeWordBlocks
        [[.integer 7], [.integer left.val], [.integer right.val],
          [.integer output.val]]
  | .neg input output =>
      encodeWordBlocks [[.integer 8], [.integer input.val], [.integer output.val]]

theorem encodeGeneralizedGate_injective {nodes : ℕ} :
    Function.Injective (encodeGeneralizedGate (nodes := nodes)) := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [encodeGeneralizedGate, encodeWordBlocks_injective.eq_iff,
      Fin.ext_iff]

/-- Gates not `ε`-satisfied by an assignment. -/
noncomputable def violatedGates
    {nodes gates : ℕ} (ε : ℝ)
    (circuit : GeneralizedCircuit nodes gates)
    (x : Fin nodes → ℝ) : Finset (Fin gates) := by
  classical
  exact Finset.univ.filter fun g => ¬ (circuit.gate g).IsSatisfied ε x

/-- An `(ε,δ)`-solution takes values in `[0,1]` and violates at most a
`δ`-fraction of the local gate constraints.  Here `δ` is not a fixed-point
distance; this is the definition in Babichenko–Papadimitriou–Rubinstein. -/
noncomputable def IsApproximateSolution
    {nodes gates : ℕ} (ε δ : ℝ)
    (circuit : GeneralizedCircuit nodes gates)
    (x : Fin nodes → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ((violatedGates ε circuit x).card : ℝ) ≤ δ * gates

/-- Input type of all finite generalized circuits. -/
abbrev GeneralizedCircuitInput :=
  Σ nodes gates : ℕ, GeneralizedCircuit nodes gates

/-- Output type packages a vector of the appropriate dimension. -/
abbrev GeneralizedCircuitOutput (input : GeneralizedCircuitInput) :=
  Fin input.1 → ℝ

/-- Canonical gate-list representation of a generalized-circuit instance.
The node declarations ensure that even isolated circuit nodes occupy words. -/
def encodeGeneralizedCircuitInput (input : GeneralizedCircuitInput) :
    List UnitCostRAM.Word :=
  encodeWordBlocks
    [[.integer input.1, .integer input.2.1],
      List.ofFn (fun index : Fin input.1 => .integer index.val),
      encodeWordBlocks
        (List.ofFn fun index : Fin input.2.1 =>
          encodeGeneralizedGate (input.2.2.gate index))]

theorem encodeGeneralizedCircuitInput_injective :
    Function.Injective encodeGeneralizedCircuitInput := by
  rintro ⟨leftNodes, leftGates, leftCircuit⟩
    ⟨rightNodes, rightGates, rightCircuit⟩ h
  have hrecords := encodeWordBlocks_injective h
  simp only [List.cons.injEq, and_true] at hrecords
  rcases hrecords with ⟨hdimensions, _hnodes, hgateRecords⟩
  have hdimensions' :
      leftNodes = rightNodes ∧ leftGates = rightGates := by
    simpa using hdimensions
  rcases hdimensions' with ⟨rfl, rfl⟩
  have hgateCodes := encodeWordBlocks_injective hgateRecords
  have hgateFunctions :
      (fun index : Fin leftGates =>
          encodeGeneralizedGate (leftCircuit.gate index)) =
        fun index : Fin leftGates =>
          encodeGeneralizedGate (rightCircuit.gate index) :=
    List.ofFn_injective hgateCodes
  have hgatesEqual : leftCircuit.gate = rightCircuit.gate := by
    funext index
    exact encodeGeneralizedGate_injective (congrFun hgateFunctions index)
  have hcircuitsEqual : leftCircuit = rightCircuit := by
    cases leftCircuit with
    | mk leftGate leftValid leftInjective =>
        cases rightCircuit with
        | mk rightGate rightValid rightInjective =>
            dsimp at hgatesEqual
            cases hgatesEqual
            rfl
  cases hcircuitsEqual
  rfl

/-- Fixed canonical input encoding for generalized circuits. -/
noncomputable def canonicalGeneralizedCircuitInputEncoding :
    UnitCostRAM.Encoding GeneralizedCircuitInput :=
  structuralEncodingOfInjective
    encodeGeneralizedCircuitInput encodeGeneralizedCircuitInput_injective

/-- Fixed canonical output encoding for generalized-circuit assignments. -/
noncomputable def canonicalGeneralizedCircuitOutputEncoding :
    UnitCostRAM.DependentEncoding GeneralizedCircuitOutput where
  encode input output := (realVectorEncoding input.1).encode output
  decode input words := (realVectorEncoding input.1).decode words
  decode_encode input output :=
    (realVectorEncoding input.1).decode_encode output

/-- The total-search relation at fixed approximation parameters. -/
noncomputable def GeneralizedCircuitSearch (ε δ : ℝ)
    (input : GeneralizedCircuitInput)
    (output : GeneralizedCircuitOutput input) : Prop :=
  IsApproximateSolution ε δ input.2.2 output

/-- Fixed-representation generalized-circuit search problem.  Each node,
constant-fan-in gate, and output coordinate occupies a constant number of
unit-cost real-RAM words. -/
noncomputable def generalizedCircuitProblem (ε δ : ℝ) :
    FixedEncodingSearchProblem where
  Input := GeneralizedCircuitInput
  Output := GeneralizedCircuitOutput
  validInput := fun _ => True
  isSolution := GeneralizedCircuitSearch ε δ
  inputEncoding := canonicalGeneralizedCircuitInputEncoding
  outputEncoding := canonicalGeneralizedCircuitOutputEncoding

/-- The PCP-for-PPAD conjecture. -/
noncomputable def PCPForPPADStatement : Prop :=
  ∃ ε δ : ℝ,
    0 < ε ∧ 0 < δ ∧
    StrictPPADHard canonicalEndOfLineEncoding
      (generalizedCircuitProblem ε δ)

/-- English version: "Is `(ε,δ)`-Generalized Circuit PPAD-hard for some
positive constants ε and δ?" -/
theorem pcpForPPAD :
    answer(sorry) ↔ PCPForPPADStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.PCPForPPAD
