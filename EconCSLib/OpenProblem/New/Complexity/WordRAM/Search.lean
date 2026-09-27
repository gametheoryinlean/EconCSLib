/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.WordRAM.FiniteData



section

/-!
# Search interfaces for the mini core

The core's `Implementation` computes a fixed function. Search problems may permit many
outputs; this layer checks a solution relation using the original `WordRAM.run` and
its actual cost. It adds no machine, declared-cost callback, or axiom, and does not
formalize a Turing-machine simulation theorem.
-/
namespace EconCSLib.OpenProblem.New.WordRAM.Search
open FiniteData

/-- Execute the original mini core on the public bitstream input alone. -/
def execution (model : Model) (program : Program) (fuel : ℕ) (input : Code) :=
  WordRAM.run (encoding.width model input) program fuel (words input)

/-- A fixed bound uniform over valid inputs. Fuel only bounds simulation; the machine
cannot read it or witnesses in the semantic solution relation. -/
def SolvesWithin (model : Model) (program : Program)
    (coefficient exponent : ℕ)
    (valid : Code → Prop) (solution : Code → Code → Prop) : Prop :=
  ∀ input, valid input →
    ∃ fuel output,
      (execution model program fuel input).termination = .halted (words output) ∧
      solution input output ∧
      (execution model program fuel input).cost ≤
        coefficient * (bitSize model input + 1) ^ exponent

/-- An execution witness for a search relation, correct on promised inputs. Its program
cannot inspect the fuel witness. -/
structure Solver (model : Model)
    (valid : Code → Prop) (solution : Code → Code → Prop) where
  program : Program
  fuel : Code → ℕ
  correct : ∀ input, valid input → ∃ output,
    (execution model program (fuel input) input).termination = .halted (words output) ∧
      solution input output

/-- Reuse the core's eventual-polynomial predicate on actual execution cost. -/
def Solver.IsPolynomialTime
    {model : Model} {valid : Code → Prop} {solution : Code → Code → Prop}
    (solver : Solver model valid solution) : Prop :=
  StrictCostCore.IsEventuallyBoundedByPolynomial
    (fun input : { code : Code // valid code } => bitSize model input.val)
    (fun input : { code : Code // valid code } =>
      (execution model solver.program (solver.fuel input.val) input.val).cost)

/-- One model and finite program are chosen before every valid input. -/
def PolynomiallySolvable
    (valid : Code → Prop) (solution : Code → Code → Prop) : Prop :=
  ∃ model : Model, ∃ solver : Solver model valid solution,
    solver.IsPolynomialTime

/-- A code function genuinely computed by a program. -/
def ComputesWithin (model : Model) (program : Program)
    (coefficient exponent : ℕ) (function : Code → Code) : Prop :=
  SolvesWithin model program coefficient exponent (fun _ => True)
    (fun input output => output = function input)

/-- A table interface whose runtime guarantee covers only inputs representable by this
rational codec; it does not silently replace the full-real semantic domain. -/
def ComputesRepresentableTableWithin {Input : Type*}
    (model : Model) (program : Program) (coefficient exponent : ℕ)
    (inputTable : Input → Table) (outputTable : Input → Table) : Prop :=
  ∀ input code, Represents code (inputTable input) →
    ∃ fuel output,
      (execution model program fuel code).termination = .halted (words output) ∧
      Represents output (outputTable input) ∧
      (execution model program fuel code).cost ≤
        coefficient * (bitSize model code + 1) ^ exponent

/-- Compatibility name for the represented-domain guarantee. -/
abbrev ComputesTableWithin := @ComputesRepresentableTableWithin

/-- A promised bitstream search problem, without implicit totality or polynomial-time
verifiability of its solution relation. -/
structure Problem where
  valid : Code → Prop
  solution : Code → Code → Prop

/-- Both reduction maps have bounded Word-RAM implementations. Solution mapping receives a
framed source-input/target-output pair. -/
structure Reduction (source target : Problem) where
  mapInput : Code → Code
  mapOutput : Code → Code → Code
  maps_valid : ∀ input, source.valid input → target.valid (mapInput input)
  preserves_solution : ∀ input output,
    source.valid input → target.solution (mapInput input) output →
      source.solution input (mapOutput input output)
  input_model : Model
  input_program : Program
  input_coefficient : ℕ
  input_exponent : ℕ
  input_computed : ComputesWithin input_model input_program
    input_coefficient input_exponent mapInput
  output_model : Model
  output_program : Program
  output_coefficient : ℕ
  output_exponent : ℕ
  output_computed : ∀ input output,
    ∃ fuel result,
      (execution output_model output_program fuel (pairCode input output)).termination =
        .halted (words result) ∧
      result = mapOutput input output ∧
      (execution output_model output_program fuel (pairCode input output)).cost ≤
        output_coefficient *
          (bitSize output_model (pairCode input output) + 1) ^ output_exponent

/-- Existence of a reduction with implemented forward and backward maps. -/
def ReducesTo (source target : Problem) : Prop :=
  Nonempty (Reduction source target)

end EconCSLib.OpenProblem.New.WordRAM.Search

end
