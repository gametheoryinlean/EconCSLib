/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.BayesianSecurityGames.Problem

/-!
# BayesianSecurityGames: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Full-real security-game inputs and outputs

Priors, payoffs and strategies remain real. Only finite cardinalities and the resource
count are natural numbers. This section specifies mathematical data.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- Semantic correctness on every real instance; no efficiency follows from possessing
this function or from classical choice. -/
def IsRealSecurityGameSolver
    (solve : (I : RealSecurityGame) → I.Output) : Prop :=
  ∀ I, IsRealSecurityGameSolution I (solve I)

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Security-game search with a concrete exact-real program

Public dimensions and real input arrays have fixed order. Sparse output is explicit
incidence bits and real probabilities; no semantic answer decoder is chosen by the
solver. A uniform finite program uses field arithmetic and comparisons only. The model
is exact-real unit cost.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- The public size is exactly the number of input cells, not chosen advice. -/
theorem RealSecurityGame.input_length (I : RealSecurityGame) :
    I.wordInput.length + I.realInput.length = I.scalarCount := by
  simp [wordInput, realInput, scalarCount, List.length_flatten, List.sum_ofFn,
    Nat.mul_assoc]
  omega

/-- Every defended-set incidence bit is part of the emitted output. -/
theorem SparseEquilibriumProfile.wordOutput_length {m k : ℕ}
    (profile : SparseEquilibriumProfile m k) :
    profile.wordOutput.length = 3 + profile.defenderSupport.length * m := by
  simp [wordOutput, List.length_flatMap]
  omega

/-- No support weight or attacker probability is hidden in a decoder. -/
theorem SparseEquilibriumProfile.realOutput_length {m k : ℕ}
    (profile : SparseEquilibriumProfile m k) :
    profile.realOutput.length = profile.defenderSupport.length + k * m := by
  simp [realOutput, List.length_flatten, List.sum_ofFn]

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Fixed rational representation of security games

This adapter encodes rational priors, payoffs and sparse outputs structurally. The
real-domain semantics remain unchanged. Numerators and denominators are charged
through their bit representation; casting to reals is specification.
-/

open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

open WordRAM.FiniteData

/-- An explicit rational instance; dimensions are input, not program parameters. -/
structure RationalSecurityGame where
  targetCount : ℕ
  attackerTypeCount : ℕ
  targetCount_pos : 0 < targetCount
  attackerTypeCount_pos : 0 < attackerTypeCount
  resources : ℕ
  resources_le_targets : resources ≤ targetCount
  typePrior : Lottery ℚ (Fin attackerTypeCount)
  defenderUncovered : Fin targetCount → ℚ
  defenderCovered : Fin targetCount → ℚ
  attackerUncovered : Fin attackerTypeCount → Fin targetCount → ℚ
  attackerCovered : Fin attackerTypeCount → Fin targetCount → ℚ
  defender_prefers_coverage : ∀ t, defenderUncovered t ≤ defenderCovered t
  attacker_prefers_uncovered : ∀ θ t, attackerCovered θ t ≤ attackerUncovered θ t

/-- Interpret the same rational data over the reals. Proof fields are not input. -/
noncomputable def RationalSecurityGame.toReal (I : RationalSecurityGame) :
    BayesianSimpleSecurityGame (Fin I.targetCount) (Fin I.attackerTypeCount) where
  resources := I.resources
  resources_le_targets := by simpa using I.resources_le_targets
  typePrior := ⟨fun θ => (I.typePrior.val θ : ℝ), by
    constructor
    · intro θ
      change (0 : ℝ) ≤ (I.typePrior.val θ : ℝ)
      exact_mod_cast I.typePrior.property.1 θ
    · change (∑ θ, (I.typePrior.val θ : ℝ)) = 1
      exact_mod_cast I.typePrior.property.2⟩
  defenderUncovered t := (I.defenderUncovered t : ℝ)
  defenderCovered t := (I.defenderCovered t : ℝ)
  attackerUncovered θ t := (I.attackerUncovered θ t : ℝ)
  attackerCovered θ t := (I.attackerCovered θ t : ℝ)
  defender_prefers_coverage t := by
    exact_mod_cast I.defender_prefers_coverage t
  attacker_prefers_uncovered θ t := by
    exact_mod_cast I.attacker_prefers_uncovered θ t

/-- Input table: dimensions and resources, prior, defender payoffs, then attacker payoffs
in type-major order. No solution is included. -/
def RationalSecurityGame.inputAtoms (I : RationalSecurityGame) : List Atom :=
  [.integer (Int.ofNat I.targetCount), .integer (Int.ofNat I.attackerTypeCount),
    .integer (Int.ofNat I.resources)] ++
  List.ofFn (fun θ : Fin I.attackerTypeCount => .rational (I.typePrior.val θ)) ++
  List.ofFn (fun t : Fin I.targetCount => .rational (I.defenderUncovered t)) ++
  List.ofFn (fun t : Fin I.targetCount => .rational (I.defenderCovered t)) ++
  (List.ofFn (fun θ : Fin I.attackerTypeCount =>
    List.ofFn (fun t : Fin I.targetCount => .rational (I.attackerUncovered θ t)))).flatten ++
  (List.ofFn (fun θ : Fin I.attackerTypeCount =>
    List.ofFn (fun t : Fin I.targetCount => .rational (I.attackerCovered θ t)))).flatten

/-- The fixed structural bitstream of the input. -/
def RationalSecurityGame.code (I : RationalSecurityGame) : Code :=
  tableCode I.inputAtoms

/-- Raw rational sparse output; correctness checks normalization and equilibrium. -/
structure RationalSparseProfile (targetCount attackerTypeCount : ℕ) where
  defenderSupport : List (Finset (Fin targetCount) × ℚ)
  attackerProbability : Fin attackerTypeCount → Fin targetCount → ℚ

/-- Exact interpretation of rational sparse data in the real semantics. -/
noncomputable def RationalSparseProfile.toReal
    {m k : ℕ} (s : RationalSparseProfile m k) : SparseEquilibriumProfile m k where
  defenderSupport := s.defenderSupport.map (fun entry => (entry.1, (entry.2 : ℝ)))
  attackerProbability θ t := (s.attackerProbability θ t : ℝ)

/-- Dimensions and support length, weighted incidence vectors, then attacker
probabilities. No exponentially long dense defender distribution is required. -/
def RationalSparseProfile.outputAtoms
    {m k : ℕ} (s : RationalSparseProfile m k) : List Atom :=
  [.integer (Int.ofNat m), .integer (Int.ofNat k),
    .integer (Int.ofNat s.defenderSupport.length)] ++
  s.defenderSupport.flatMap (fun entry =>
    .rational entry.2 ::
      List.ofFn (fun t : Fin m => .bit (decide (t ∈ entry.1)))) ++
  (List.ofFn (fun θ : Fin k =>
    List.ofFn (fun t : Fin m => .rational (s.attackerProbability θ t)))).flatten

/-- Output encoding is independent of the input and of the selected equilibrium. -/
def RationalSparseProfile.code {m k : ℕ} (s : RationalSparseProfile m k) : Code :=
  tableCode s.outputAtoms

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Full-real security-game execution schema

The mathematical domain contains every real payoff table and real mixed strategy. The
access/execution semantics E are fixed before the program. They are a specification
parameter. Correctness and cost refer to the same execution. The full-real unit-cost
size is the fixed number of input scalars. The realization certificate checks actual
Word-RAM runs on represented inputs; that certificate does not cover arbitrary real
data.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

/-- A fixed execution specification. Real-data access and charged operations require
independent justification; this is not a machine certificate. -/
structure RealExecutionSemantics where
  execute : WordRAM.Model → WordRAM.Program →
    (I : RealSecurityGame) → Option (I.Output × ℕ)

/-- The same execution must return an exact solution on every real instance. -/
def RealExecutionSemantics.Correct (E : RealExecutionSemantics)
    (model : WordRAM.Model) (program : WordRAM.Program) : Prop :=
  ∀ I : RealSecurityGame, ∃ s : I.Output, ∃ c : ℕ,
    E.execute model program I = some (s, c) ∧ IsRealSecurityGameSolution I s

/-- Cost of the recorded execution. Correctness excludes the failure branch. -/
def RealExecutionSemantics.executionCost (E : RealExecutionSemantics)
    (model : WordRAM.Model) (program : WordRAM.Program)
    (I : RealSecurityGame) : ℕ :=
  match E.execute model program I with
  | none => 0
  | some result => result.2

/-- One model and program for all real instances, relative to fixed E. A scalar-count
polynomial budget bounds every execution, including small sizes. This is a unit-cost
real-access schema. -/
def BayesianSecurityGameRealPolynomialQuestion (E : RealExecutionSemantics) : Prop :=
  ∃ model : WordRAM.Model, ∃ program : WordRAM.Program,
    E.Correct model program ∧
      ExecutionContracts.HasUniformPolynomialEnvelope
        RealSecurityGame.scalarCount (E.executionCost model program)

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Actual execution on a fixed presentation

The full-real semantic schema and the finite Word-RAM certificate remain distinct. The
latter covers only inputs described by the chosen presentation. Neither interface
asserts that every real game has a finite code.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames
open WordRAM.FiniteData

/-- Pack output dimensions so decoding does not receive the input payoff table. -/
abbrev PackedRealEquilibrium :=
  Σ m : ℕ, Σ k : ℕ, SparseEquilibriumProfile m k

def IsPackedRealSecurityGameSolution (I : RealSecurityGame)
    (s : PackedRealEquilibrium) : Prop :=
  ∃ profile : I.Output,
    s = ⟨I.targetCount, I.attackerTypeCount, profile⟩ ∧
      IsRealSecurityGameSolution I profile

/-- On presented inputs, the same program returns the schema's output with exactly its
charged execution cost. -/
def RealExecutionSemantics.AgreesWithWordRAMOn (E : RealExecutionSemantics)
    (P : ExecutionContracts.Presentation RealSecurityGame PackedRealEquilibrium)
    (model : WordRAM.Model) (program : WordRAM.Program) : Prop :=
  ∀ code I, P.decodeInput code = some I →
    ∀ (s : I.Output) cost, E.execute model program I = some (s, cost) →
      ∃ fuel output,
        (WordRAM.Search.execution model program fuel code).termination =
          .halted (words output) ∧
        P.decodeOutput output = some ⟨I.targetCount, I.attackerTypeCount, s⟩ ∧
        (WordRAM.Search.execution model program fuel code).cost = cost

/-- Actual Word-RAM search on the stated presentation. Coverage and non-answer-hiding
decoding must be justified separately; an empty presentation makes this
represented-domain requirement vacuous. The canonical rational statement avoids an
arbitrary presentation. -/
def BayesianSecurityGamePresentedWordRAMQuestion
    (P : ExecutionContracts.Presentation RealSecurityGame PackedRealEquilibrium) : Prop :=
  let task := P.searchProblem (fun _ => True) IsPackedRealSecurityGameSolution
  WordRAM.Search.PolynomiallySolvable task.valid task.solution

/-- Output and cost agree with the actual interpreter on the presented domain. Input
capacity covers every explicit scalar. The full-real bound still uses scalarCount, so
padding the finite code cannot improve that bound. No full-real coverage or decoding
adequacy is inferred. -/
def RealExecutionSemantics.IsFaithfulOn (E : RealExecutionSemantics)
    (P : ExecutionContracts.Presentation RealSecurityGame PackedRealEquilibrium)
    (model : WordRAM.Model) (program : WordRAM.Program) : Prop :=
  E.AgreesWithWordRAMOn P model program ∧
    ∀ code I, P.decodeInput code = some I →
      I.scalarCount ≤ bitSize model code

/-- Full-real correctness and scalar-count runtime relative to E, with an actual execution
certificate on P. Outside P, execution remains a parameterized specification. Coverage
of a stated nonempty domain and decoding adequacy are separate obligations, not
consequences of this conditional interface. -/
def BayesianSecurityGameRealWithPresentedCertificateQuestion
    (E : RealExecutionSemantics)
    (P : ExecutionContracts.Presentation RealSecurityGame PackedRealEquilibrium) : Prop :=
  ∃ model : WordRAM.Model, ∃ program : WordRAM.Program,
    E.Correct model program ∧
    E.IsFaithfulOn P model program ∧
    ExecutionContracts.HasUniformPolynomialEnvelope
      RealSecurityGame.scalarCount (E.executionCost model program)

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end


section

/-!
## Rational security-game search on bounded Word-RAM

The explicit rational input and sparse output encodings are fixed independently of the
solver. Correctness is exact Bayesian Nash equilibrium. This is a represented-domain
specialization of Conitzer's question.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

open WordRAM.FiniteData

/-- Valid structural codes of rational instances; the promise contains no solution. -/
def IsCanonicalSecurityGameInput (input : Code) : Prop :=
  ∃ I : RationalSecurityGame, input = I.code

/-- The output is the fixed code of a rational sparse exact equilibrium of the game
encoded by the input. -/
def IsCanonicalSecurityGameEquilibrium (input output : Code) : Prop :=
  ∃ (I : RationalSecurityGame)
    (sparse : RationalSparseProfile I.targetCount I.attackerTypeCount)
    (profile : DefenderStrategy I.toReal ×
      AttackerStrategy (Fin I.targetCount) (Fin I.attackerTypeCount)),
      input = I.code ∧
      output = sparse.code ∧
      sparse.toReal.Represents I.toReal profile ∧
      IsBayesNashEquilibrium I.toReal profile

/-- The input promise and solution relation as a search problem. -/
def rationalSecurityGameSearchProblem : WordRAM.Search.Problem where
  valid := IsCanonicalSecurityGameInput
  solution := IsCanonicalSecurityGameEquilibrium

/-- A uniform bounded Word-RAM solver for the rational specialization. -/
def BayesianSecurityGameRationalWordRAMStatement : Prop :=
  WordRAM.Search.PolynomiallySolvable
    rationalSecurityGameSearchProblem.valid rationalSecurityGameSearchProblem.solution

end EconCSLib.OpenProblem.New.EconCSBench.BayesianSecurityGames

end
