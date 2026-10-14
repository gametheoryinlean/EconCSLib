/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.PolynomialTime
import Mathlib.Data.Rat.Cast.Order



section

/-!
# Fixed finite representations of data tables

`Value` describes mathematical tables, not machine words. In particular, `.real` does
not provide real arithmetic to a program. This codec represents real cells only when
rational, with multi-bit numerators, denominators, and integers.

`Represents` fixes order, tags, and framing independently of the program or answer.
Irrational cells are not representable: there is no rounding or fallback code. Each
problem must distinguish this represented domain from its full-real mathematical
semantics.

Each code bit occupies one machine word. An `L`-bit code has input capacity `L *
wordWidth`; neither a large integer nor a whole table is packed into one word.
-/

namespace EconCSLib.OpenProblem.New.WordRAM.FiniteData

/-- The fixed bitstream representation type. -/
abbrev Code := List Bool

/-- Mathematical table cells, not machine instructions. -/
inductive Value
  | integer (value : Int)
  | real (value : ℝ)
  | bit (value : Bool)

/-- An ordered mathematical table. -/
abbrev Table := List Value

/-- The codec's chosen domain: integers, normalized rationals, and bits. -/
inductive Atom
  | integer (value : Int)
  | rational (value : ℚ)
  | bit (value : Bool)

/-- Semantic interpretation of rational cells as reals. -/
noncomputable def Atom.denote : Atom → Value
  | .integer z => .integer z
  | .rational q => .real (q : ℝ)
  | .bit b => .bit b

/-- Self-delimiting natural code: `ℓ` ones, a zero, then `ℓ` low-bit-first bits of `n+1`,
where `ℓ=floor(log₂(n+1))+1`. Zero also has a nonempty code. -/
def natCode (n : ℕ) : Code :=
  let length := Nat.log2 (n + 1) + 1
  List.replicate length true ++ [false] ++
    List.ofFn (fun i : Fin length => Nat.testBit (n + 1) i.val)

/-- A sign bit followed by the magnitude; rational denominators are positive. -/
def intCode (z : Int) : Code :=
  [decide (z < 0)] ++ natCode z.natAbs

/-- Numerator-denominator code for Lean's normalized rational representation. -/
def ratCode (q : ℚ) : Code := intCode q.num ++ natCode q.den

/-- Cell codes with fixed two-bit tags. -/
def Atom.code : Atom → Code
  | .integer z => [false, false] ++ intCode z
  | .rational q => [false, true] ++ ratCode q
  | .bit b => [true, false, b]

/-- Encode the number of cells, then each tagged self-delimiting payload. -/
def tableCode (atoms : List Atom) : Code :=
  natCode atoms.length ++ atoms.flatMap Atom.code

/-- A structural representation relation with no algorithm-dependent codebook. -/
def Represents (code : Code) (table : Table) : Prop :=
  ∃ atoms : List Atom,
    atoms.map Atom.denote = table ∧ tableCode atoms = code

/-- Whether a mathematical table belongs to this codec's represented domain. -/
def Representable (table : Table) : Prop :=
  ∃ code, Represents code table

/-- A code-length bound, used to state an explicit finite sampler domain. -/
def HasBitBound (bound : ℕ) (table : Table) : Prop :=
  ∃ code, Represents code table ∧ code.length ≤ bound

/-- A semantic oracle-boundary encoder. Nonrational tables yield `none`. -/
noncomputable def encodeSpec (table : Table) : Option Code := by
  classical
  exact if h : ∃ atoms : List Atom, atoms.map Atom.denote = table then
    some (tableCode (Classical.choose h)) else none

/-- A nonconstructive parser specification for a fixed structural codebook. It describes
permitted oracle-boundary semantics. -/
noncomputable def decodeSpec (code : Code) : Option Table := by
  classical
  exact if h : ∃ atoms : List Atom, tableCode atoms = code then
    some ((Classical.choose h).map Atom.denote) else none

/-- Store only zero or one in each machine word, never a real or a long integer. -/
def words (code : Code) : List ℕ :=
  code.map (fun b => if b then 1 else 0)

/-- Reject word arrays containing values other than zero and one. -/
def ofWords : List ℕ → Option Code
  | [] => some []
  | 0 :: tail => (ofWords tail).map (false :: ·)
  | 1 :: tail => (ofWords tail).map (true :: ·)
  | _ :: _ => none

/-- A lossless bitstream encoding for the unmodified mini core. -/
def encoding : Encoding Code where
  encode := words
  decode := ofWords
  decode_encode code := by
    induction code with
    | nil => rfl
    | cons b tail ih =>
        cases b <;> simp_all [words, ofWords]

/-- Output is a bitstream; this decoder does not compute the semantic answer. -/
def outputEncoding {Input : Type*} :
    DependentEncoding (fun _ : Input => Code) where
  encode _ := words
  decode _ := ofWords
  decode_encode _ := encoding.decode_encode

/-- Input-array bit capacity `L*w`, with one code bit per word, not dense packing. -/
def bitSize (model : Model) (code : Code) : ℕ :=
  encoding.bitSize model code

/-- Frame two bitstreams using the first length, independently of any answer. -/
def pairCode (left right : Code) : Code :=
  natCode left.length ++ left ++ right

/-- Binary dimension header, without numerical-value padding. -/
def binaryDimensionCode (dimensions : List ℕ) : Code :=
  tableCode (dimensions.map fun n => Atom.integer (Int.ofNat n))

/-- Unary-padded header with length proportional to the sum of dimensions. Use only for
explicit object counts, not to claim polynomiality in their logarithms. -/
def unaryPaddedDimensionCode (dimensions : List ℕ) : Code :=
  binaryDimensionCode dimensions ++ List.replicate dimensions.sum false

/-- Compatibility name for the padded header; preserves existing size semantics. New code
should choose one of the explicit header names. -/
abbrev dimensionCode := unaryPaddedDimensionCode

end EconCSLib.OpenProblem.New.WordRAM.FiniteData

end
