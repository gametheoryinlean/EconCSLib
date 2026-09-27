/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.New.SharedConcepts.All
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

/-!
# 15. PCP for PPAD
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

/-- The conjecture uses fixed positive tolerances in the unit interval. -/
def ReferenceTolerances (ε δ : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1

/-- A gate whose output is its circuit index; parameters have finite rational codes. -/
inductive GeneralizedGate (Node : Type*)
  | constant (value : ℚ)
  | scale (factor : ℚ) (input : Node)
  | copy (input : Node)
  | add (left right : Node)
  | sub (left right : Node)
  | less (left right : Node)
  | disj (left right : Node)
  | conj (left right : Node)
  | neg (input : Node)
  deriving DecidableEq

/-- Valid parameters for the normalized circuit convention. -/
def GeneralizedGate.ParametersValid {Node : Type*} : GeneralizedGate Node → Prop
  | .constant q | .scale q _ => 0 ≤ q ∧ q ≤ 1
  | _ => True

/-- Absolute error, including equality at epsilon. -/
def Within (ε a b : ℝ) : Prop := |a - b| ≤ ε

/-- The nine local constraints. Comparators use strict premises and Boolean gates use
closed thresholds; values in the undefined region are unconstrained. -/
def GeneralizedGate.IsSatisfied {Node : Type*}
    (ε : ℝ) (x : Node → ℝ) (output : Node) : GeneralizedGate Node → Prop
  | .constant q => Within ε (x output) (q : ℝ)
  | .scale q input => Within ε (x output) (min (x input * (q : ℝ)) 1)
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

/-- Exactly one producer per node. Inputs may refer to any node, including the current
node; this is not an acyclic arithmetic circuit. -/
structure GeneralizedCircuit (nodes : ℕ) where
  gate : Fin nodes → GeneralizedGate (Fin nodes)
  parameters_valid : ∀ i, (gate i).ParametersValid

/-- Each violated gate is counted once, even if several implications fail. -/
noncomputable def violatedGates {nodes : ℕ} (ε : ℝ)
    (circuit : GeneralizedCircuit nodes) (x : Fin nodes → ℝ) : Finset (Fin nodes) := by
  classical
  exact Finset.univ.filter fun i => ¬ (circuit.gate i).IsSatisfied ε x i

/-- One assignment satisfies at least a 1-delta fraction of the gates. The denominator is
the number of gates, not encoded bits or wire occurrences. -/
noncomputable def IsApproximateSolution {nodes : ℕ} (ε δ : ℝ)
    (circuit : GeneralizedCircuit nodes) (x : Fin nodes → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ((violatedGates ε circuit x).card : ℝ) ≤ δ * (nodes : ℝ)

abbrev GeneralizedCircuitInput := Σ nodes : ℕ, GeneralizedCircuit nodes

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


section

/-!
## The concrete search relation and external PPAD-hardness notion

The input has finitely described rational gate coefficients, while a mathematical
solution assigns real values to every node [DFHM, Section 2.2.2]. Only the standard
PPAD-hardness notion is left external. Its intended polynomial-time reduction and
representation conventions must be fixed by the surrounding complexity theory; no
hardness predicate is chosen by an algorithm or existentially hidden in the
conjecture.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

/-- Search relations on the fixed normalized-circuit input and real-assignment output
types. The output dimension is determined by the supplied circuit. -/
abbrev GeneralizedCircuitSearchRelation :=
  (input : GeneralizedCircuitInput) → (Fin input.1 → ℝ) → Prop

/-- One shared unit-interval assignment violates at most a delta fraction of the actual
gates, each checked with local error epsilon. -/
noncomputable def approximateCircuitRelation (ε δ : ℝ) :
    GeneralizedCircuitSearchRelation :=
  fun input assignment => IsApproximateSolution ε δ input.2 assignment

/-- Externally fixed standard polynomial-time PPAD-hardness on this circuit domain.
Instantiating an arbitrary predicate does not establish that it has this intended
meaning; no PPAD definition or complexity equivalence is claimed. -/
abbrev PPADHardness := GeneralizedCircuitSearchRelation → Prop

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


section

/-!
## The source-level PCP-for-PPAD question

The main question uses an externally fixed standard PPAD-hardness notion, with
ordinary polynomial-time reductions [DFHM, Section 2.2.2]. The circuit relation itself
is concrete: rational coefficients and all real assignments. No reduction model,
output decoder, or hardness predicate is chosen inside the question. This is a formal
statement relative to the external notion.

The rational-assignment Word-RAM question and real-coefficient correctness contracts
remain available as separately named auxiliary interfaces. The main question does not
impose the stronger original quasilinear reduction bound.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

/-- Fixed positive constants make the concrete generalized-circuit search problem
PPAD-hard. The external hardness notion precedes both constants and all circuit
instances; it is not an existential algorithmic witness. -/
def PCPForPPADQuestion (hard : PPADHardness) : Prop :=
  ∃ ε δ : ℝ, ReferenceTolerances ε δ ∧
    hard (approximateCircuitRelation ε δ)

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD

/-- PCP-for-PPAD relative to the specified PPAD-hardness notion. -/
theorem pcpForPPAD (hard : PPADHardness) :
    answer(sorry) ↔ PCPForPPADQuestion hard := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.PCPForPPAD
