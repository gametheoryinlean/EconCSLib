/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.StaticComplexity
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Programs with intrinsically derived cost expressions

StaticComplexity.AlgorithmShape can analyze a finite control-flow tree, but
using it next to an independently written Lean function duplicates the
algorithm: once as executable code and once as a complexity description. This
module removes that duplication for structured algorithms. A
StructuredProgram is executable syntax. Its interpreter supplies the actual
Cost run, while StructuredProgram.analyze traverses the same syntax to derive
its symbolic worst-case resource expression.

Assignment, branching, sequencing, counted iteration, and fuelled while loops
are charged by the interpreter itself. An opaque library or foreign primitive
can enter through external, but must carry a local proof that its instrumented
operation count is bounded by its advertised expression. Thus the analyzer
never infers a cost for an opaque Lean function merely from its name.

This follows the cost-semantics pattern of Danielsson (POPL 2008) and CSLib's
TimeM, while strengthening trusted annotations by linking every external
annotation to a local inequality. The asymptotic endpoint uses Mathlib's
Asymptotics.IsBigO; the executable polynomial checker remains the finite,
sound but intentionally incomplete front end.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity

open Filter Asymptotics

universe u v w

/-! ## Mathlib IsBigO bridge -/

/-- Standard asymptotic formulation of a polynomial upper bound for a natural
cost function. The hidden multiplicative constant belongs to IsBigO; only the
natural exponent is displayed here. -/
def IsAsymptoticallyPolynomial (cost : ℕ → ℕ) : Prop :=
  ∃ exponent : ℕ,
    (fun n => (cost n : ℝ)) =O[atTop]
      (fun n => ((n + 1 : ℕ) : ℝ) ^ exponent)

/-- The elementary coefficient/exponent definition used by the executable
analyzer implies the standard Mathlib IsBigO formulation. -/
theorem isAsymptoticallyPolynomial_of_isPolyBound
    {cost : ℕ → ℕ} (bound : IsPolyBound id cost) :
    IsAsymptoticallyPolynomial cost := by
  obtain ⟨coefficient, exponent, bound⟩ := bound
  refine ⟨exponent, isBigO_iff.mpr ⟨(coefficient : ℝ), ?_⟩⟩
  filter_upwards [] with n
  simp only [Real.norm_eq_abs, abs_pow]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact_mod_cast bound n

namespace GrowthExpr

/-- A checker-accepted expression also has the standard Mathlib asymptotic
polynomial bound. -/
theorem isPolynomial_sound_isBigO (expression : GrowthExpr)
    (accepted : expression.isPolynomial = true) :
    IsAsymptoticallyPolynomial expression.eval :=
  isAsymptoticallyPolynomial_of_isPolyBound
    (isPolynomial_sound expression accepted)

/-- A computable upper bound on the degree needed by the structural proof.
none means that this analyzer cannot certify the expression. Logarithms are
conservatively assigned the degree of their argument; coefficients are not
optimized. -/
def polynomialDegree? : GrowthExpr → Option ℕ
  | .constant _ => some 0
  | .inputSize => some 1
  | .add left right | .maximum left right =>
      return max (← left.polynomialDegree?) (← right.polynomialDegree?)
  | .mul left right =>
      return (← left.polynomialDegree?) + (← right.polynomialDegree?)
  | .pow base exponent =>
      return (← base.polynomialDegree?) * exponent
  | .logarithm _ argument => argument.polynomialDegree?
  | .exponential | .factorial | .unknown => none

/-- Human-readable rendering of the expression extracted from an algorithm.
This is presentation only; all proofs use eval and the original syntax tree. -/
def render : GrowthExpr → String
  | .constant value => toString value
  | .inputSize => "n"
  | .add left right => s!"({left.render} + {right.render})"
  | .mul left right => s!"({left.render} * {right.render})"
  | .pow base exponent => s!"({base.render} ^ {exponent})"
  | .maximum left right => s!"max({left.render}, {right.render})"
  | .logarithm base argument => s!"log_{base}({argument.render})"
  | .exponential => "2^n"
  | .factorial => "n!"
  | .unknown => "unknown"

/-- Executable summary returned to users after the analyzer reads an
algorithm. -/
structure Report where
  expression : String
  polynomial : Bool
  degreeUpperBound : Option ℕ
  deriving Repr, DecidableEq

def report (expression : GrowthExpr) : Report where
  expression := expression.render
  polynomial := expression.isPolynomial
  degreeUpperBound := expression.polynomialDegree?

theorem polynomialDegree?_isSome_iff (expression : GrowthExpr) :
    expression.polynomialDegree?.isSome = expression.isPolynomial := by
  induction expression with
  | constant value => rfl
  | inputSize => rfl
  | add left right leftIH rightIH =>
      cases hleft : left.polynomialDegree? <;>
        cases hright : right.polynomialDegree? <;>
          simp_all [polynomialDegree?, isPolynomial]
  | mul left right leftIH rightIH =>
      cases hleft : left.polynomialDegree? <;>
        cases hright : right.polynomialDegree? <;>
          simp_all [polynomialDegree?, isPolynomial]
  | pow base exponent baseIH =>
      simp [polynomialDegree?, isPolynomial, Option.isSome_bind, baseIH]
  | maximum left right leftIH rightIH =>
      cases hleft : left.polynomialDegree? <;>
        cases hright : right.polynomialDegree? <;>
          simp_all [polynomialDegree?, isPolynomial]
  | logarithm base argument argumentIH =>
      simpa [polynomialDegree?, isPolynomial] using argumentIH
  | exponential => rfl
  | factorial => rfl
  | unknown => rfl

/-- The degree returned by polynomialDegree? is not merely a classification
hint: it is the exponent of a genuine polynomial majorant. The coefficient is
also produced existentially, but is intentionally not optimized. -/
theorem polynomialDegree?_sound (expression : GrowthExpr) {degree : ℕ}
    (reported : expression.polynomialDegree? = some degree) :
    ∃ coefficient : ℕ, ∀ n,
      expression.eval n ≤ coefficient * (n + 1) ^ degree := by
  induction expression generalizing degree with
  | constant value =>
      simp only [polynomialDegree?, Option.some.injEq] at reported
      subst degree
      exact ⟨value, fun n => by simp [eval]⟩
  | inputSize =>
      simp only [polynomialDegree?, Option.some.injEq] at reported
      subst degree
      exact ⟨1, fun n => by simp [eval]⟩
  | add left right leftIH rightIH =>
      cases hLeftDegree : left.polynomialDegree? with
      | none => simp [polynomialDegree?, hLeftDegree] at reported
      | some dLeft =>
          cases hRightDegree : right.polynomialDegree? with
          | none =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
          | some dRight =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
              subst degree
              obtain ⟨leftCoefficient, leftBound⟩ :=
                leftIH hLeftDegree
              obtain ⟨rightCoefficient, rightBound⟩ :=
                rightIH hRightDegree
              refine ⟨leftCoefficient + rightCoefficient, fun n => ?_⟩
              have baseOne : 1 ≤ n + 1 := by omega
              have leftPower :
                  (n + 1) ^ dLeft ≤
                    (n + 1) ^ max dLeft dRight :=
                Nat.pow_le_pow_right baseOne (le_max_left _ _)
              have rightPower :
                  (n + 1) ^ dRight ≤
                    (n + 1) ^ max dLeft dRight :=
                Nat.pow_le_pow_right baseOne (le_max_right _ _)
              calc
                (GrowthExpr.add left right).eval n
                    = left.eval n + right.eval n := rfl
                _ ≤ leftCoefficient * (n + 1) ^ dLeft +
                      rightCoefficient * (n + 1) ^ dRight :=
                    Nat.add_le_add (leftBound n) (rightBound n)
                _ ≤ leftCoefficient *
                        (n + 1) ^ max dLeft dRight +
                      rightCoefficient *
                        (n + 1) ^ max dLeft dRight := by
                    gcongr
                _ = (leftCoefficient + rightCoefficient) *
                      (n + 1) ^ max dLeft dRight := by ring
  | mul left right leftIH rightIH =>
      cases hLeftDegree : left.polynomialDegree? with
      | none => simp [polynomialDegree?, hLeftDegree] at reported
      | some dLeft =>
          cases hRightDegree : right.polynomialDegree? with
          | none =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
          | some dRight =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
              subst degree
              obtain ⟨leftCoefficient, leftBound⟩ :=
                leftIH hLeftDegree
              obtain ⟨rightCoefficient, rightBound⟩ :=
                rightIH hRightDegree
              refine ⟨leftCoefficient * rightCoefficient, fun n => ?_⟩
              calc
                (GrowthExpr.mul left right).eval n
                    = left.eval n * right.eval n := rfl
                _ ≤ (leftCoefficient * (n + 1) ^ dLeft) *
                      (rightCoefficient * (n + 1) ^ dRight) :=
                    Nat.mul_le_mul (leftBound n) (rightBound n)
                _ = (leftCoefficient * rightCoefficient) *
                      (n + 1) ^ (dLeft + dRight) := by
                    rw [pow_add]
                    ring
  | pow base exponent baseIH =>
      cases hBaseDegree : base.polynomialDegree? with
      | none => simp [polynomialDegree?, hBaseDegree] at reported
      | some dBase =>
          simp [polynomialDegree?, hBaseDegree] at reported
          subst degree
          obtain ⟨coefficient, baseBound⟩ := baseIH hBaseDegree
          refine ⟨coefficient ^ exponent, fun n => ?_⟩
          calc
            (GrowthExpr.pow base exponent).eval n
                = (base.eval n) ^ exponent := rfl
            _ ≤ (coefficient * (n + 1) ^ dBase) ^ exponent :=
                Nat.pow_le_pow_left (baseBound n) exponent
            _ = coefficient ^ exponent *
                  (n + 1) ^ (dBase * exponent) := by
                rw [mul_pow, pow_mul]
  | maximum left right leftIH rightIH =>
      cases hLeftDegree : left.polynomialDegree? with
      | none => simp [polynomialDegree?, hLeftDegree] at reported
      | some dLeft =>
          cases hRightDegree : right.polynomialDegree? with
          | none =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
          | some dRight =>
              simp [polynomialDegree?, hLeftDegree, hRightDegree] at reported
              subst degree
              obtain ⟨leftCoefficient, leftBound⟩ :=
                leftIH hLeftDegree
              obtain ⟨rightCoefficient, rightBound⟩ :=
                rightIH hRightDegree
              refine ⟨leftCoefficient + rightCoefficient, fun n => ?_⟩
              have baseOne : 1 ≤ n + 1 := by omega
              have leftPower :
                  (n + 1) ^ dLeft ≤
                    (n + 1) ^ max dLeft dRight :=
                Nat.pow_le_pow_right baseOne (le_max_left _ _)
              have rightPower :
                  (n + 1) ^ dRight ≤
                    (n + 1) ^ max dLeft dRight :=
                Nat.pow_le_pow_right baseOne (le_max_right _ _)
              calc
                (GrowthExpr.maximum left right).eval n
                    = max (left.eval n) (right.eval n) := rfl
                _ ≤ left.eval n + right.eval n := by omega
                _ ≤ leftCoefficient * (n + 1) ^ dLeft +
                      rightCoefficient * (n + 1) ^ dRight :=
                    Nat.add_le_add (leftBound n) (rightBound n)
                _ ≤ leftCoefficient *
                        (n + 1) ^ max dLeft dRight +
                      rightCoefficient *
                        (n + 1) ^ max dLeft dRight := by
                    gcongr
                _ = (leftCoefficient + rightCoefficient) *
                      (n + 1) ^ max dLeft dRight := by ring
  | logarithm base argument argumentIH =>
      obtain ⟨coefficient, argumentBound⟩ := argumentIH reported
      refine ⟨coefficient, fun n => ?_⟩
      calc
        (GrowthExpr.logarithm base argument).eval n
            = Nat.log base (argument.eval n) := rfl
        _ ≤ argument.eval n := Nat.log_le_self _ _
        _ ≤ coefficient * (n + 1) ^ degree := argumentBound n
  | exponential => simp [polynomialDegree?] at reported
  | factorial => simp [polynomialDegree?] at reported
  | unknown => simp [polynomialDegree?] at reported

end GrowthExpr

/-! ## Typed primitive programs with exact extracted cost

This layer follows the free-monad/query-combinator architecture used by
Algolean.  It is complementary to StructuredProgram below.  PrimitiveProgram
supports arbitrary dependent data flow: the rest of a program may depend on
the result of an instruction.  Its interpreter reads the actually selected
continuation and produces an exact symbolic sum of primitive costs.

Because an input-indexed family may generate a different finite program for
every input, exact extraction alone does not establish one uniform asymptotic
bound.  StructuredProgram supplies compact, uniformly bounded loops for that
second task.
-/

/-- Semantics and symbolic unit-cost price of every instruction in a typed
primitive language.  Declaring the instruction family fixes the RAM model:
arithmetic, memory access, oracle access, or another intended primitive set. -/
structure PrimitiveModel (Instruction : Type u → Type v) where
  execute : {Result : Type u} → Instruction Result → Result
  cost : {Result : Type u} → Instruction Result → GrowthExpr

/-- A typed free program.  invokeBind performs one declared instruction and
then continues with the returned value.  There is no escape hatch containing
an uncharged hidden computation. -/
inductive PrimitiveProgram (Instruction : Type u → Type v) (Result : Type u) where
  | pure (value : Result)
  | invokeBind {Intermediate : Type u}
      (instruction : Instruction Intermediate)
      (next : Intermediate → PrimitiveProgram Instruction Result)

namespace PrimitiveProgram

variable {Instruction : Type u → Type v} {Result : Type u}

/-- Invoke one typed primitive and return its result. -/
def invoke (instruction : Instruction Result) :
    PrimitiveProgram Instruction Result :=
  .invokeBind instruction .pure

/-- Dependent sequencing for the primitive program language. -/
def bind (program : PrimitiveProgram Instruction Result)
    {Output : Type u}
    (next : Result → PrimitiveProgram Instruction Output) :
    PrimitiveProgram Instruction Output :=
  match program with
  | .pure value => next value
  | .invokeBind instruction continuation =>
      .invokeBind instruction fun value => (continuation value).bind next

/-- Apply a bookkeeping-only result transformation.  Any operation intended
to consume RAM time must instead be a constructor of Instruction. -/
def map (function : Result → Output)
    (program : PrimitiveProgram Instruction Result) :
    PrimitiveProgram Instruction Output :=
  program.bind (fun value => .pure (function value))

/-- Symbolic cost obtained by traversing the selected instruction path. -/
def costExpression (model : PrimitiveModel Instruction) :
    PrimitiveProgram Instruction Result → GrowthExpr
  | .pure _ => .constant 0
  | .invokeBind instruction next =>
      .add (model.cost instruction)
        ((next (model.execute instruction)).costExpression model)

/-- Execute a program under a primitive model and charge exactly the
evaluation of the extracted expression at the chosen aggregate input size. -/
def run (model : PrimitiveModel Instruction) (inputSize : ℕ) :
    PrimitiveProgram Instruction Result → Cost Result
  | .pure value => Cost.pure value
  | .invokeBind instruction next =>
      let value := model.execute instruction
      let tail := (next value).run model inputSize
      ⟨tail.value, (model.cost instruction).eval inputSize + tail.ops⟩

/-- Extraction is exact for the abstract primitive-machine semantics, not
merely an upper bound. -/
theorem run_ops_eq_costExpression (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction) (inputSize : ℕ) :
    (program.run model inputSize).ops =
      (program.costExpression model).eval inputSize := by
  induction program with
  | pure value => rfl
  | invokeBind instruction next nextIH =>
      simp only [run, costExpression, GrowthExpr.eval]
      rw [nextIH (model.execute instruction)]
      rfl

/-- Executable polynomial classification of the exact extracted expression. -/
def decidePolynomialTime (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction) : Bool :=
  (program.costExpression model).isPolynomial

/-- Optional degree bound of the exact extracted expression. -/
def polynomialDegree? (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction) : Option ℕ :=
  (program.costExpression model).polynomialDegree?

/-- Readable report of the exact primitive-level cost expression. -/
def report (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction) : GrowthExpr.Report :=
  (program.costExpression model).report

/-- The optional degree is a certified bound on every execution size, not
only metadata printed by report. -/
theorem polynomialDegree?_run_sound
    (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction) {degree : ℕ}
    (reported : program.polynomialDegree? model = some degree) :
    ∃ coefficient : ℕ, ∀ inputSize,
      (program.run model inputSize).ops ≤
        coefficient * (inputSize + 1) ^ degree := by
  obtain ⟨coefficient, expressionBound⟩ :=
    GrowthExpr.polynomialDegree?_sound
      (program.costExpression model) reported
  refine ⟨coefficient, fun inputSize => ?_⟩
  rw [program.run_ops_eq_costExpression model inputSize]
  exact expressionBound inputSize

/-- If the executable checker accepts, the exact extracted primitive cost has
a standard semantic polynomial bound. -/
theorem decidePolynomialTime_sound
    (program : PrimitiveProgram Instruction Result)
    (model : PrimitiveModel Instruction)
    (accepted : program.decidePolynomialTime model = true) :
    IsPolyBound id (program.costExpression model).eval ∧
      IsAsymptoticallyPolynomial (program.costExpression model).eval := by
  exact ⟨GrowthExpr.isPolynomial_sound _ accepted,
    GrowthExpr.isPolynomial_sound_isBigO _ accepted⟩

end PrimitiveProgram

/-! ## Executable structured-program syntax -/

/-- An executable, state-transforming algorithm whose cost expression is
derived by structurally reading the program.

The state may depend on the input, which is needed for algorithms over finite
types such as Fin input.vertexCount. Every constructor preserves that state
type. More general intermediate result types remain available through
AnalyzedComputation; this language deliberately targets imperative/stateful
algorithm structure. -/
inductive StructuredProgram
    {Input : Type u} (sizeOf : Input → ℕ) (State : Input → Type v) where
  /-- No state change and no charged work. -/
  | skip
  /-- One genuine unit-cost state update. -/
  | operation (update : (input : Input) → State input → State input)
  /-- An opaque operation with an audited local running-time contract. -/
  | external
      (run : (input : Input) → State input → Cost (State input))
      (bound : GrowthExpr)
      (time_le : ∀ input state,
        (run input state).ops ≤ bound.eval (sizeOf input))
  /-- Sequential composition. -/
  | sequential
      (first second : StructuredProgram sizeOf State)
  /-- Unit-cost predicate evaluation followed by a charged branch dispatch. -/
  | branch
      (condition : (input : Input) → State input → Bool)
      (ifTrue ifFalse : StructuredProgram sizeOf State)
  /-- A counted loop with a certified symbolic iteration bound. -/
  | repeat
      (iterations : Input → ℕ)
      (bound : GrowthExpr)
      (iterations_le : ∀ input,
        iterations input ≤ bound.eval (sizeOf input))
      (body : StructuredProgram sizeOf State)
  /-- A counted loop whose iteration count may depend on the state at loop
  entry. The bound is uniform over every reachable or unreachable state, so
  the static expression remains input-size only. -/
  | stateRepeat
      (iterations : (input : Input) → State input → ℕ)
      (bound : GrowthExpr)
      (iterations_le : ∀ input state,
        iterations input state ≤ bound.eval (sizeOf input))
      (body : StructuredProgram sizeOf State)
  /-- A total while loop. Fuel is both its termination witness and symbolic
  worst-case iteration bound. Evaluating the condition costs one operation. -/
  | whileFuel
      (fuel : Input → ℕ)
      (bound : GrowthExpr)
      (fuel_le : ∀ input, fuel input ≤ bound.eval (sizeOf input))
      (condition : (input : Input) → State input → Bool)
      (body : StructuredProgram sizeOf State)
  /-- State-dependent fuel variant for algorithms whose remaining iteration
  budget is computed during initialization. -/
  | stateWhileFuel
      (fuel : (input : Input) → State input → ℕ)
      (bound : GrowthExpr)
      (fuel_le : ∀ input state,
        fuel input state ≤ bound.eval (sizeOf input))
      (condition : (input : Input) → State input → Bool)
      (body : StructuredProgram sizeOf State)

namespace StructuredProgram

variable {Input : Type u} {sizeOf : Input → ℕ}
  {State : Input → Type v}

/-- Embed a typed primitive program as a structured state transition.  The
primitive path has an exact extracted cost; only the final, unavoidable
uniform comparison with an input-size expression is supplied by the user.
This is the bridge between arbitrary typed data flow and compact loop-level
worst-case analysis. -/
def ofPrimitiveProgram
    {Instruction : Type v → Type w}
    (model : PrimitiveModel Instruction)
    (program : (input : Input) → State input →
      PrimitiveProgram Instruction (State input))
    (bound : GrowthExpr)
    (cost_le : ∀ input state,
      ((program input state).costExpression model).eval (sizeOf input) ≤
        bound.eval (sizeOf input)) :
    StructuredProgram sizeOf State :=
  .external
    (fun input state => (program input state).run model (sizeOf input))
    bound (by
      intro input state
      rw [PrimitiveProgram.run_ops_eq_costExpression]
      exact cost_le input state)

/-- Static resource profile obtained solely by traversing the program syntax.
No separately authored AlgorithmShape is required. -/
def analyze : StructuredProgram sizeOf State → AlgorithmShape
  | .skip => .primitive ResourceProfile.zero
  | .operation _ => .primitive ResourceProfile.localOperation
  | .external _ bound _ =>
      .primitive (ResourceProfile.timeOnly bound)
  | .sequential first second =>
      .sequential first.analyze second.analyze
  | .branch _ ifTrue ifFalse =>
      .sequential
        (.primitive ResourceProfile.localOperation)
        (.conditional ifTrue.analyze ifFalse.analyze)
  | .repeat _ bound _ body => .repeat bound body.analyze
  | .stateRepeat _ bound _ body => .repeat bound body.analyze
  | .whileFuel _ bound _ _ body =>
      .repeat bound
        (.sequential
          (.primitive ResourceProfile.localOperation)
          body.analyze)
  | .stateWhileFuel _ bound _ _ body =>
      .repeat bound
        (.sequential
          (.primitive ResourceProfile.localOperation)
          body.analyze)

/-- The symbolic worst-case running-time expression read from a program. -/
def timeExpression (program : StructuredProgram sizeOf State) : GrowthExpr :=
  program.analyze.analyze.time

/-- Extract the state carried by either outcome of a total fuelled loop. -/
private def whileState {Value : Type v} : Cost.WhileResult Value → Value
  | .done state | .exhausted state => state

/-- Execute the structured algorithm. All non-external costs are generated
by this interpreter, rather than supplied by the algorithm author. -/
def run : StructuredProgram sizeOf State →
    (input : Input) → State input → Cost (State input)
  | .skip, _, state => Cost.pure state
  | .operation update, input, state =>
      Cost.liftUnary (update input) (Cost.pure state)
  | .external externalRun _ _, input, state => externalRun input state
  | .sequential first second, input, state =>
      Cost.bind (first.run input state) (second.run input)
  | .branch condition ifTrue ifFalse, input, state =>
      Cost.branch
        (Cost.liftUnary (condition input) (Cost.pure state))
        (fun _ => ifTrue.run input state)
        (fun _ => ifFalse.run input state)
  | .repeat iterations _ _ body, input, state =>
      Cost.iterate (iterations input) (body.run input) state
  | .stateRepeat iterations _ _ body, input, state =>
      Cost.iterate (iterations input state) (body.run input) state
  | .whileFuel fuel _ _ condition body, input, state =>
      Cost.map whileState <|
        Cost.whileFuel (fuel input)
          (fun current =>
            Cost.liftUnary (condition input) (Cost.pure current))
          (body.run input) state
  | .stateWhileFuel fuel _ _ condition body, input, state =>
      Cost.map whileState <|
        Cost.whileFuel (fuel input state)
          (fun current =>
            Cost.liftUnary (condition input) (Cost.pure current))
          (body.run input) state

/-- The interpreter's actual operation counter is bounded by the expression
obtained by structurally reading the same program. -/
theorem run_ops_le (program : StructuredProgram sizeOf State)
    (input : Input) (state : State input) :
    (program.run input state).ops ≤
      program.timeExpression.eval (sizeOf input) := by
  induction program generalizing state with
  | skip =>
      change 0 ≤ 0
      exact le_rfl
  | operation update =>
      change 1 ≤ 1
      exact le_rfl
  | external externalRun bound time_le =>
      simpa [run, timeExpression, analyze, AlgorithmShape.analyze,
        ResourceProfile.timeOnly, ResourceProfile.zero] using
        time_le input state
  | sequential first second firstIH secondIH =>
      rw [run, Cost.ops_bind]
      calc
        (first.run input state).ops +
              (second.run input (first.run input state).value).ops
            ≤ first.timeExpression.eval (sizeOf input) +
                second.timeExpression.eval (sizeOf input) :=
              Nat.add_le_add (firstIH state)
                (secondIH (first.run input state).value)
        _ = _ := by
          simp [timeExpression, analyze, AlgorithmShape.analyze,
            ResourceProfile.sequential, GrowthExpr.eval]
  | branch condition ifTrue ifFalse trueIH falseIH =>
      have htrue := trueIH state
      have hfalse := falseIH state
      unfold run
      unfold Cost.branch
      dsimp only
      split
      · calc
          1 + (ifTrue.run input state).ops + 1
              ≤ 1 + ifTrue.timeExpression.eval (sizeOf input) + 1 := by
                omega
          _ ≤ 1 +
                (1 + max
                  (ifTrue.timeExpression.eval (sizeOf input))
                  (ifFalse.timeExpression.eval (sizeOf input))) := by omega
          _ = _ := by
            simp [timeExpression, analyze, AlgorithmShape.analyze,
              ResourceProfile.sequential, ResourceProfile.conditional,
              ResourceProfile.localOperation, ResourceProfile.timeOnly,
              ResourceProfile.zero, GrowthExpr.eval]
      · calc
          1 + (ifFalse.run input state).ops + 1
              ≤ 1 + ifFalse.timeExpression.eval (sizeOf input) + 1 := by
                omega
          _ ≤ 1 +
                (1 + max
                  (ifTrue.timeExpression.eval (sizeOf input))
                  (ifFalse.timeExpression.eval (sizeOf input))) := by omega
          _ = _ := by
            simp [timeExpression, analyze, AlgorithmShape.analyze,
              ResourceProfile.sequential, ResourceProfile.conditional,
              ResourceProfile.localOperation, ResourceProfile.timeOnly,
              ResourceProfile.zero, GrowthExpr.eval]
  | «repeat» iterations bound iterations_le body bodyIH =>
      have loopBound := Cost.ops_iterate_le (iterations input)
        (body.timeExpression.eval (sizeOf input)) (body.run input) state
        bodyIH
      calc
        (Cost.iterate (iterations input) (body.run input) state).ops
            ≤ iterations input *
                (body.timeExpression.eval (sizeOf input) + 1) := loopBound
        _ ≤ bound.eval (sizeOf input) *
              (body.timeExpression.eval (sizeOf input) + 1) := by
            gcongr
            exact iterations_le input
        _ = _ := by
          simp [timeExpression, analyze, AlgorithmShape.analyze,
            ResourceProfile.iterate, GrowthExpr.eval]
  | stateRepeat iterations bound iterations_le body bodyIH =>
      have loopBound := Cost.ops_iterate_le (iterations input state)
        (body.timeExpression.eval (sizeOf input)) (body.run input) state
        bodyIH
      calc
        (Cost.iterate (iterations input state) (body.run input) state).ops
            ≤ iterations input state *
                (body.timeExpression.eval (sizeOf input) + 1) := loopBound
        _ ≤ bound.eval (sizeOf input) *
              (body.timeExpression.eval (sizeOf input) + 1) := by
            gcongr
            exact iterations_le input state
        _ = _ := by
          simp [timeExpression, analyze, AlgorithmShape.analyze,
            ResourceProfile.iterate, GrowthExpr.eval]
  | whileFuel fuel bound fuel_le condition body bodyIH =>
      rw [run, Cost.ops_map]
      have loopBound := Cost.ops_whileFuel_le (fuel input) 1
        (body.timeExpression.eval (sizeOf input))
        (fun current : State input =>
          Cost.liftUnary (condition input) (Cost.pure current))
        (body.run input) state (by
          intro current
          change 1 ≤ 1
          exact le_rfl) bodyIH
      calc
        (Cost.whileFuel (fuel input)
            (fun current : State input =>
              Cost.liftUnary (condition input) (Cost.pure current))
            (body.run input) state).ops
            ≤ fuel input *
                (1 + body.timeExpression.eval (sizeOf input) + 1) :=
              loopBound
        _ ≤ bound.eval (sizeOf input) *
              (1 + body.timeExpression.eval (sizeOf input) + 1) := by
            gcongr
            exact fuel_le input
        _ = _ := by
          simp [timeExpression, analyze, AlgorithmShape.analyze,
            ResourceProfile.iterate, ResourceProfile.sequential,
            ResourceProfile.localOperation, ResourceProfile.timeOnly,
            ResourceProfile.zero, GrowthExpr.eval]
  | stateWhileFuel fuel bound fuel_le condition body bodyIH =>
      rw [run, Cost.ops_map]
      have loopBound := Cost.ops_whileFuel_le (fuel input state) 1
        (body.timeExpression.eval (sizeOf input))
        (fun current : State input =>
          Cost.liftUnary (condition input) (Cost.pure current))
        (body.run input) state (by
          intro current
          change 1 ≤ 1
          exact le_rfl) bodyIH
      calc
        (Cost.whileFuel (fuel input state)
            (fun current : State input =>
              Cost.liftUnary (condition input) (Cost.pure current))
            (body.run input) state).ops
            ≤ fuel input state *
                (1 + body.timeExpression.eval (sizeOf input) + 1) :=
              loopBound
        _ ≤ bound.eval (sizeOf input) *
              (1 + body.timeExpression.eval (sizeOf input) + 1) := by
            gcongr
            exact fuel_le input state
        _ = _ := by
          simp [timeExpression, analyze, AlgorithmShape.analyze,
            ResourceProfile.iterate, ResourceProfile.sequential,
            ResourceProfile.localOperation, ResourceProfile.timeOnly,
            ResourceProfile.zero, GrowthExpr.eval]

/-- Execute the conservative polynomial-time decision procedure directly on
the program syntax. -/
def decidePolynomialTime (program : StructuredProgram sizeOf State) : Bool :=
  program.timeExpression.isPolynomial

/-- The optional degree report computed from the same derived expression. -/
def polynomialDegree? (program : StructuredProgram sizeOf State) : Option ℕ :=
  program.timeExpression.polynomialDegree?

/-- Readable executable report for the derived expression. -/
def report (program : StructuredProgram sizeOf State) : GrowthExpr.Report :=
  program.timeExpression.report

/-- A reported degree directly bounds the interpreter's operation counter for
every input and every initial state. -/
theorem polynomialDegree?_run_sound
    (program : StructuredProgram sizeOf State) {degree : ℕ}
    (reported : program.polynomialDegree? = some degree) :
    ∃ coefficient : ℕ, ∀ (input : Input) (state : State input),
      (program.run input state).ops ≤
        coefficient * (sizeOf input + 1) ^ degree := by
  obtain ⟨coefficient, expressionBound⟩ :=
    GrowthExpr.polynomialDegree?_sound program.timeExpression reported
  exact ⟨coefficient, fun input state =>
    (program.run_ops_le input state).trans
      (expressionBound (sizeOf input))⟩

/-- A positive Boolean answer yields both the elementary semantic bound and
the standard Mathlib IsBigO result for the derived cost expression. -/
theorem decidePolynomialTime_sound
    (program : StructuredProgram sizeOf State)
    (accepted : program.decidePolynomialTime = true) :
    IsPolyBound id program.timeExpression.eval ∧
      IsAsymptoticallyPolynomial program.timeExpression.eval := by
  exact ⟨GrowthExpr.isPolynomial_sound _ accepted,
    GrowthExpr.isPolynomial_sound_isBigO _ accepted⟩

end StructuredProgram

/-! ## Complete algorithms: initialization, body, and finalization -/

/-- A complete structured algorithm. Its state initialization is allowed to
depend on the input and therefore carries one local contract. The main body
is executable syntax read by the analyzer. Final projection is charged as one
ordinary operation. -/
structure StructuredAlgorithm
    {Input : Type u} (sizeOf : Input → ℕ)
    (State : Input → Type v) (Output : Input → Type w) where
  initial : (input : Input) → Cost (State input)
  initialBound : GrowthExpr
  initial_le : ∀ input,
    (initial input).ops ≤ initialBound.eval (sizeOf input)
  body : StructuredProgram sizeOf State
  finish : (input : Input) → State input → Output input

namespace StructuredAlgorithm

variable {Input : Type u} {sizeOf : Input → ℕ}
  {State : Input → Type v} {Output : Input → Type w}

/-- Execute initialization, the analyzed body, and one final projection. -/
def run (algorithm : StructuredAlgorithm sizeOf State Output)
    (input : Input) : Cost (Output input) :=
  Cost.bind (algorithm.initial input) fun state =>
    Cost.liftUnary (algorithm.finish input)
      (algorithm.body.run input state)

/-- Mathematical function computed by a structured algorithm. -/
def function (algorithm : StructuredAlgorithm sizeOf State Output) :
    (input : Input) → Output input :=
  fun input => (algorithm.run input).value

/-- Symbolic resource tree generated from initialization, the actual body
syntax, and finalization. -/
def shape (algorithm : StructuredAlgorithm sizeOf State Output) :
    AlgorithmShape :=
  .sequential
    (.primitive (ResourceProfile.timeOnly algorithm.initialBound))
    (.sequential algorithm.body.analyze
      (.primitive ResourceProfile.localOperation))

/-- Symbolic running-time expression generated for the complete algorithm. -/
def timeExpression (algorithm : StructuredAlgorithm sizeOf State Output) :
    GrowthExpr :=
  algorithm.shape.analyze.time

/-- The interpreter-generated operation count satisfies the generated cost
expression. -/
theorem run_ops_le (algorithm : StructuredAlgorithm sizeOf State Output)
    (input : Input) :
    (algorithm.run input).ops ≤
      algorithm.timeExpression.eval (sizeOf input) := by
  rw [run, Cost.ops_bind, Cost.ops_liftUnary]
  calc
    (algorithm.initial input).ops +
          ((algorithm.body.run input (algorithm.initial input).value).ops + 1)
        ≤ algorithm.initialBound.eval (sizeOf input) +
            (algorithm.body.timeExpression.eval (sizeOf input) + 1) :=
          Nat.add_le_add (algorithm.initial_le input)
            (Nat.add_le_add_right
              (algorithm.body.run_ops_le input
                (algorithm.initial input).value) 1)
    _ = _ := by
      simp [timeExpression, shape, StructuredProgram.timeExpression,
        AlgorithmShape.analyze, ResourceProfile.sequential,
        ResourceProfile.timeOnly, ResourceProfile.localOperation,
        ResourceProfile.zero, GrowthExpr.eval]

/-- Ordinary CostedImplementation obtained without a separate global cost
annotation. -/
def implementation (algorithm : StructuredAlgorithm sizeOf State Output) :
    CostedImplementation algorithm.function where
  run := algorithm.run
  correct := fun _ => rfl

/-- Read the body and decide whether the generated expression is polynomial. -/
def decidePolynomialTime
    (algorithm : StructuredAlgorithm sizeOf State Output) : Bool :=
  algorithm.timeExpression.isPolynomial

/-- Return the analyzer's conservative degree upper bound, when available. -/
def polynomialDegree?
    (algorithm : StructuredAlgorithm sizeOf State Output) : Option ℕ :=
  algorithm.timeExpression.polynomialDegree?

/-- Readable executable report for a complete algorithm. -/
def report
    (algorithm : StructuredAlgorithm sizeOf State Output) : GrowthExpr.Report :=
  algorithm.timeExpression.report

/-- A degree returned by the executable analyzer is a checked polynomial
majorant for the complete implementation, including initialization and
finalization. -/
theorem polynomialDegree?_run_sound
    (algorithm : StructuredAlgorithm sizeOf State Output) {degree : ℕ}
    (reported : algorithm.polynomialDegree? = some degree) :
    ∃ coefficient : ℕ, ∀ input,
      (algorithm.run input).ops ≤
        coefficient * (sizeOf input + 1) ^ degree := by
  obtain ⟨coefficient, expressionBound⟩ :=
    GrowthExpr.polynomialDegree?_sound algorithm.timeExpression reported
  exact ⟨coefficient, fun input =>
    (algorithm.run_ops_le input).trans
      (expressionBound (sizeOf input))⟩

/-- Soundness for the actual complete implementation, not merely its static
syntax. -/
theorem decidePolynomialTime_sound
    (algorithm : StructuredAlgorithm sizeOf State Output)
    (accepted : algorithm.decidePolynomialTime = true) :
    algorithm.implementation.IsPolynomial sizeOf := by
  apply IsPolyBound.of_le
    (GrowthExpr.lift_to_size
      (GrowthExpr.isPolynomial_sound algorithm.timeExpression accepted))
  exact algorithm.run_ops_le

end StructuredAlgorithm

end EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity
