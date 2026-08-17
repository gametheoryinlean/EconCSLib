/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.UnitCostRAM
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log

/-!
# Decidable static complexity analysis

This module provides an executable, conservative polynomial-growth checker for
the unit-cost RAM interface.  It does not attempt the impossible task of
deciding the asymptotic running time of an arbitrary Lean function.  Instead,
algorithms expose a finite `AlgorithmShape` assembled from primitive resource
bounds, sequencing, conditionals, and bounded iteration.  The analyzer
computes a symbolic upper bound and returns a `Bool`.

The executable result is connected to the semantic definition by a soundness
theorem: whenever `decidePolynomialTime` returns `true`, the operation counter
of a linked `CostedImplementation` satisfies `IsPolynomial`.  Thus users need
not guess a coefficient or exponent.  The one remaining proof obligation is
the unavoidable local instrumentation obligation that the declared symbolic
shape really bounds the implementation being analyzed.

The analyzer also tracks oracle queries, distribution samples, random bits,
communication, and peak auxiliary space.  A `false` result means "not
certified by this analyzer"; it is not, in general, a proof that no polynomial
implementation of the mathematical function exists.

`AnalyzedComputation` is an intrinsic EDSL for complex functions: dependent
sequencing, branches, counted loops, list folds, and total fuelled while loops
construct the run, the static shape, and their cost inequality simultaneously.
Only leaf primitives need an audited local resource contract.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity

universe u v

/-! ## Executable symbolic growth bounds -/

/-- Symbolic natural-valued upper bounds in one aggregate input size.

`exponential`, `factorial`, and `unknown` are deliberately rejected by the
polynomial checker.  The other constructors are closed under polynomial upper
bounds. -/
inductive GrowthExpr where
  | constant (value : ℕ)
  | inputSize
  | add (left right : GrowthExpr)
  | mul (left right : GrowthExpr)
  | pow (base : GrowthExpr) (exponent : ℕ)
  | maximum (left right : GrowthExpr)
  | logarithm (base : ℕ) (argument : GrowthExpr)
  | exponential
  | factorial
  | unknown
  deriving Repr, Inhabited, DecidableEq

namespace GrowthExpr

/-- Evaluate a symbolic resource bound at input size `n`. -/
def eval : GrowthExpr → ℕ → ℕ
  | .constant value, _ => value
  | .inputSize, n => n
  | .add left right, n => left.eval n + right.eval n
  | .mul left right, n => left.eval n * right.eval n
  | .pow base exponent, n => (base.eval n) ^ exponent
  | .maximum left right, n => max (left.eval n) (right.eval n)
  | .logarithm base argument, n => Nat.log base (argument.eval n)
  | .exponential, n => 2 ^ n
  | .factorial, n => n.factorial
  | .unknown, _ => 0

/-- Executable conservative test for polynomial growth.

The logarithm of a polynomially bounded expression is polynomially bounded;
the base is irrelevant for this upper-bound fact, including bases `0` and `1`.
-/
def isPolynomial : GrowthExpr → Bool
  | .constant _ | .inputSize => true
  | .add left right | .mul left right | .maximum left right =>
      left.isPolynomial && right.isPolynomial
  | .pow base _ => base.isPolynomial
  | .logarithm _ argument => argument.isPolynomial
  | .exponential | .factorial | .unknown => false

/-- A polynomially bounded natural function remains polynomially bounded
after taking any fixed natural power. -/
theorem isPolyBound_pow {f : ℕ → ℕ} (hf : IsPolyBound id f) :
    ∀ exponent : ℕ, IsPolyBound id (fun n => (f n) ^ exponent)
  | 0 => by
      simpa using (IsPolyBound.const (sizeOf := id) 1)
  | exponent + 1 => by
      simpa [pow_succ] using
        IsPolyBound.mul (isPolyBound_pow hf exponent) hf

/-- Soundness of the executable symbolic checker. -/
theorem isPolynomial_sound (expression : GrowthExpr)
    (accepted : expression.isPolynomial = true) :
    IsPolyBound id expression.eval := by
  induction expression with
  | constant value =>
      simpa [eval] using (IsPolyBound.const (sizeOf := id) value)
  | inputSize =>
      simpa [eval] using (IsPolyBound.self (sizeOf := id))
  | add left right leftIH rightIH =>
      simp only [isPolynomial, Bool.and_eq_true] at accepted
      simpa [eval] using IsPolyBound.add
        (leftIH accepted.1) (rightIH accepted.2)
  | mul left right leftIH rightIH =>
      simp only [isPolynomial, Bool.and_eq_true] at accepted
      simpa [eval] using IsPolyBound.mul
        (leftIH accepted.1) (rightIH accepted.2)
  | pow base exponent baseIH =>
      simp only [isPolynomial] at accepted
      simpa [eval] using isPolyBound_pow (baseIH accepted) exponent
  | maximum left right leftIH rightIH =>
      simp only [isPolynomial, Bool.and_eq_true] at accepted
      apply IsPolyBound.of_le
        (IsPolyBound.add (leftIH accepted.1) (rightIH accepted.2))
      intro n
      simp only [eval]
      omega
  | logarithm base argument argumentIH =>
      simp only [isPolynomial] at accepted
      apply IsPolyBound.of_le (argumentIH accepted)
      intro n
      simp only [eval]
      exact Nat.log_le_self base (argument.eval n)
  | exponential => simp [isPolynomial] at accepted
  | factorial => simp [isPolynomial] at accepted
  | unknown => simp [isPolynomial] at accepted

/-- Lift a polynomial bound in a scalar size to arbitrary inputs carrying that
size. -/
theorem lift_to_size {Input : Type u} {sizeOf : Input → ℕ} {f : ℕ → ℕ}
    (hf : IsPolyBound id f) :
    IsPolyBound sizeOf (fun input => f (sizeOf input)) := by
  obtain ⟨coefficient, exponent, bound⟩ := hf
  exact ⟨coefficient, exponent, fun input => bound (sizeOf input)⟩

end GrowthExpr

/-! ## Multi-resource algorithm syntax -/

/-- Symbolic upper bounds for resources used by one algorithm. -/
structure ResourceProfile where
  time : GrowthExpr
  oracleQueries : GrowthExpr
  distributionSamples : GrowthExpr
  randomBits : GrowthExpr
  communication : GrowthExpr
  auxiliarySpace : GrowthExpr
  deriving Repr, DecidableEq

namespace ResourceProfile

/-- No resource usage. -/
def zero : ResourceProfile where
  time := .constant 0
  oracleQueries := .constant 0
  distributionSamples := .constant 0
  randomBits := .constant 0
  communication := .constant 0
  auxiliarySpace := .constant 0

/-- A bound that only charges unit-cost RAM time. -/
def timeOnly (time : GrowthExpr) : ResourceProfile :=
  { zero with time := time }

/-- One ordinary unit-cost RAM operation. -/
def localOperation : ResourceProfile := timeOnly (.constant 1)

/-- One constant-time oracle invocation. -/
def oracleCall : ResourceProfile :=
  { zero with time := .constant 1, oracleQueries := .constant 1 }

/-- One constant-time call to an external distribution sampler. -/
def distributionSample : ResourceProfile :=
  { zero with time := .constant 1, distributionSamples := .constant 1 }

/-- Consume a symbolic number of random bits in one local operation. -/
def randomness (bits : GrowthExpr) : ResourceProfile :=
  { zero with time := .constant 1, randomBits := bits }

/-- Communicate a symbolic number of words or bits, according to the protocol's
declared communication unit. -/
def communicate (units : GrowthExpr) : ResourceProfile :=
  { zero with time := .constant 1, communication := units }

/-- Reserve a symbolic number of peak auxiliary cells. -/
def allocate (cells : GrowthExpr) : ResourceProfile :=
  { zero with time := .constant 1, auxiliarySpace := cells }

/-- Sequential composition.  Cumulative resources add, while peak auxiliary
space is bounded by the maximum of the two phases. -/
def sequential (left right : ResourceProfile) : ResourceProfile where
  time := .add left.time right.time
  oracleQueries := .add left.oracleQueries right.oracleQueries
  distributionSamples := .add left.distributionSamples right.distributionSamples
  randomBits := .add left.randomBits right.randomBits
  communication := .add left.communication right.communication
  auxiliarySpace := .maximum left.auxiliarySpace right.auxiliarySpace

/-- Worst-case resource bound for a conditional.  Testing the condition costs
one time unit; only the more expensive branch is charged. -/
def conditional (ifTrue ifFalse : ResourceProfile) : ResourceProfile where
  time := .add (.constant 1) (.maximum ifTrue.time ifFalse.time)
  oracleQueries := .maximum ifTrue.oracleQueries ifFalse.oracleQueries
  distributionSamples :=
    .maximum ifTrue.distributionSamples ifFalse.distributionSamples
  randomBits := .maximum ifTrue.randomBits ifFalse.randomBits
  communication := .maximum ifTrue.communication ifFalse.communication
  auxiliarySpace := .maximum ifTrue.auxiliarySpace ifFalse.auxiliarySpace

/-- Repeat a body a symbolically bounded number of times.  One time unit per
iteration is charged for loop control.  The other resources are cumulative;
peak auxiliary space is reused between iterations. -/
def iterate (iterations : GrowthExpr) (body : ResourceProfile) : ResourceProfile where
  time := .mul iterations (.add body.time (.constant 1))
  oracleQueries := .mul iterations body.oracleQueries
  distributionSamples := .mul iterations body.distributionSamples
  randomBits := .mul iterations body.randomBits
  communication := .mul iterations body.communication
  auxiliarySpace := body.auxiliarySpace

/-- Every tracked resource has a polynomial symbolic upper bound. -/
def allPolynomial (profile : ResourceProfile) : Bool :=
  profile.time.isPolynomial &&
    profile.oracleQueries.isPolynomial &&
    profile.distributionSamples.isPolynomial &&
    profile.randomBits.isPolynomial &&
    profile.communication.isPolynomial &&
    profile.auxiliarySpace.isPolynomial

/-- Soundness of the executable all-resource check. -/
theorem allPolynomial_sound (profile : ResourceProfile)
    (accepted : profile.allPolynomial = true) :
    IsPolyBound id profile.time.eval ∧
      IsPolyBound id profile.oracleQueries.eval ∧
      IsPolyBound id profile.distributionSamples.eval ∧
      IsPolyBound id profile.randomBits.eval ∧
      IsPolyBound id profile.communication.eval ∧
      IsPolyBound id profile.auxiliarySpace.eval := by
  change (profile.time.isPolynomial &&
    profile.oracleQueries.isPolynomial &&
    profile.distributionSamples.isPolynomial &&
    profile.randomBits.isPolynomial &&
    profile.communication.isPolynomial &&
    profile.auxiliarySpace.isPolynomial) = true at accepted
  have prefix₅ := (Bool.and_eq_true_iff.mp accepted).1
  have hspace := (Bool.and_eq_true_iff.mp accepted).2
  have prefix₄ := (Bool.and_eq_true_iff.mp prefix₅).1
  have hcommunication := (Bool.and_eq_true_iff.mp prefix₅).2
  have prefix₃ := (Bool.and_eq_true_iff.mp prefix₄).1
  have hrandom := (Bool.and_eq_true_iff.mp prefix₄).2
  have prefix₂ := (Bool.and_eq_true_iff.mp prefix₃).1
  have hsamples := (Bool.and_eq_true_iff.mp prefix₃).2
  have htime := (Bool.and_eq_true_iff.mp prefix₂).1
  have hqueries := (Bool.and_eq_true_iff.mp prefix₂).2
  exact ⟨GrowthExpr.isPolynomial_sound profile.time htime,
    GrowthExpr.isPolynomial_sound profile.oracleQueries hqueries,
    GrowthExpr.isPolynomial_sound profile.distributionSamples hsamples,
    GrowthExpr.isPolynomial_sound profile.randomBits hrandom,
    GrowthExpr.isPolynomial_sound profile.communication hcommunication,
    GrowthExpr.isPolynomial_sound profile.auxiliarySpace hspace⟩

end ResourceProfile

/-- A finite algorithm-shape language used by the executable analyzer. -/
inductive AlgorithmShape where
  | primitive (resources : ResourceProfile)
  | sequential (first second : AlgorithmShape)
  | conditional (ifTrue ifFalse : AlgorithmShape)
  | repeat (iterations : GrowthExpr) (body : AlgorithmShape)
  | unknown
  deriving Repr, DecidableEq

namespace AlgorithmShape

/-- Compute a symbolic worst-case resource profile from program structure. -/
def analyze : AlgorithmShape → ResourceProfile
  | .primitive resources => resources
  | .sequential first second =>
      ResourceProfile.sequential first.analyze second.analyze
  | .conditional ifTrue ifFalse =>
      ResourceProfile.conditional ifTrue.analyze ifFalse.analyze
  | .repeat iterations body => ResourceProfile.iterate iterations body.analyze
  | .unknown =>
      { time := .unknown
        oracleQueries := .unknown
        distributionSamples := .unknown
        randomBits := .unknown
        communication := .unknown
        auxiliarySpace := .unknown }

/-- Executable yes/no check for polynomial running time. -/
def decidePolynomialTime (shape : AlgorithmShape) : Bool :=
  shape.analyze.time.isPolynomial

/-- Executable yes/no check for polynomial use of every tracked resource. -/
def decideAllPolynomialResources (shape : AlgorithmShape) : Bool :=
  shape.analyze.allPolynomial

/-- The running-time answer produced by the analyzer is semantically sound. -/
theorem decidePolynomialTime_sound (shape : AlgorithmShape)
    (accepted : shape.decidePolynomialTime = true) :
    IsPolyBound id shape.analyze.time.eval :=
  GrowthExpr.isPolynomial_sound shape.analyze.time accepted

end AlgorithmShape

/-! ## Intrinsically analyzed computations -/

/-- A computation whose symbolic shape is linked to its operation counter by
construction.  Complex algorithms should be assembled with the combinators in
this namespace.  Only leaf primitives require a local cost proof. -/
structure AnalyzedComputation
    {Input : Type u} (sizeOf : Input → ℕ) (Output : Input → Type v) where
  run : (input : Input) → Cost (Output input)
  shape : AlgorithmShape
  time_le : ∀ input,
    (run input).ops ≤ shape.analyze.time.eval (sizeOf input)

namespace AnalyzedComputation

/-- The mathematical function computed by an analyzed computation. -/
def function
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (program : AnalyzedComputation sizeOf Output) :
    (input : Input) → Output input :=
  fun input => (program.run input).value

/-- Turn an intrinsically analyzed computation into the ordinary costed
implementation interface. -/
def implementation
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (program : AnalyzedComputation sizeOf Output) :
    CostedImplementation program.function where
  run := program.run
  correct := fun _ => rfl

/-- Reading the already supplied input requires no algorithmic work. -/
def input {Input : Type u} (sizeOf : Input → ℕ) :
    AnalyzedComputation sizeOf (fun _ => Input) where
  run := fun input => Cost.pure input
  shape := .primitive ResourceProfile.zero
  time_le := by
    intro input
    change 0 ≤ 0
    exact le_rfl

/-- Return one already available constant without charging an operation. -/
def constant {Input : Type u} (sizeOf : Input → ℕ) {Value : Type v}
    (value : Value) : AnalyzedComputation sizeOf (fun _ => Value) where
  run := fun _ => Cost.pure value
  shape := .primitive ResourceProfile.zero
  time_le := by
    intro input
    change 0 ≤ 0
    exact le_rfl

/-- Universal audited escape hatch.  Any dependent costed function can be a
leaf, but its author must prove the advertised symbolic upper bound.  This is
where a library primitive, solver, or foreign routine receives its explicit
cost contract. -/
def primitive
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (run : (input : Input) → Cost (Output input)) (bound : GrowthExpr)
    (time_le : ∀ input, (run input).ops ≤ bound.eval (sizeOf input)) :
    AnalyzedComputation sizeOf Output where
  run := run
  shape := .primitive (ResourceProfile.timeOnly bound)
  time_le := by
    simpa [AlgorithmShape.analyze, ResourceProfile.timeOnly,
      ResourceProfile.zero] using time_le

/-- Apply one genuine unit-cost unary RAM primitive to a computed value. -/
def mapUnit
    {Input : Type u} {sizeOf : Input → ℕ}
    {Value : Input → Type v} {Result : Input → Type w}
    (program : AnalyzedComputation sizeOf Value)
    (operation : (input : Input) → Value input → Result input) :
    AnalyzedComputation sizeOf Result where
  run := fun input => Cost.liftUnary (operation input) (program.run input)
  shape := .sequential program.shape
    (.primitive ResourceProfile.localOperation)
  time_le := by
    intro input
    calc
      (Cost.liftUnary (operation input) (program.run input)).ops
          = (program.run input).ops + 1 := rfl
      _ ≤ program.shape.analyze.time.eval (sizeOf input) + 1 :=
        Nat.add_le_add_right (program.time_le input) 1
      _ = _ := by
        simp [AlgorithmShape.analyze, ResourceProfile.sequential,
          ResourceProfile.localOperation, ResourceProfile.timeOnly,
          ResourceProfile.zero, GrowthExpr.eval]

/-- General dependent sequencing.  The continuation has one shape and bound
uniform over every possible intermediate value. -/
def bind
    {Input : Type u} {sizeOf : Input → ℕ}
    {Intermediate : Input → Type v} {Output : Input → Type w}
    (first : AnalyzedComputation sizeOf Intermediate)
    (continuation : (input : Input) → Intermediate input → Cost (Output input))
    (continuationShape : AlgorithmShape)
    (continuation_le : ∀ input intermediate,
      (continuation input intermediate).ops ≤
        continuationShape.analyze.time.eval (sizeOf input)) :
    AnalyzedComputation sizeOf Output where
  run := fun input => Cost.bind (first.run input) (continuation input)
  shape := .sequential first.shape continuationShape
  time_le := by
    intro input
    rw [Cost.ops_bind]
    calc
      (first.run input).ops +
          (continuation input (first.run input).value).ops
        ≤ first.shape.analyze.time.eval (sizeOf input) +
            continuationShape.analyze.time.eval (sizeOf input) :=
          Nat.add_le_add (first.time_le input)
            (continuation_le input (first.run input).value)
      _ = _ := by
        simp [AlgorithmShape.analyze, ResourceProfile.sequential,
          GrowthExpr.eval]

/-- Sequence two computations on the same input, discarding the first value. -/
def andThen
    {Input : Type u} {sizeOf : Input → ℕ}
    {First : Input → Type v} {Second : Input → Type w}
    (first : AnalyzedComputation sizeOf First)
    (second : AnalyzedComputation sizeOf Second) :
    AnalyzedComputation sizeOf Second :=
  bind first (fun input _ => second.run input) second.shape
    (fun input _ => second.time_le input)

/-- Worst-case conditional execution.  The condition and only the selected
branch are run; the symbolic bound takes the maximum of both branches. -/
def branch
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (condition : AnalyzedComputation sizeOf (fun _ => Bool))
    (ifTrue ifFalse : AnalyzedComputation sizeOf Output) :
    AnalyzedComputation sizeOf Output where
  run := fun input => Cost.branch (condition.run input)
    (fun _ => ifTrue.run input) (fun _ => ifFalse.run input)
  shape := .sequential condition.shape
    (.conditional ifTrue.shape ifFalse.shape)
  time_le := by
    intro input
    have hcondition := condition.time_le input
    have htrue := ifTrue.time_le input
    have hfalse := ifFalse.time_le input
    unfold Cost.branch
    dsimp only
    split
    · calc
        (condition.run input).ops + (ifTrue.run input).ops + 1
            ≤ condition.shape.analyze.time.eval (sizeOf input) +
                ifTrue.shape.analyze.time.eval (sizeOf input) + 1 := by
              omega
        _ ≤ condition.shape.analyze.time.eval (sizeOf input) +
              (1 + max
                (ifTrue.shape.analyze.time.eval (sizeOf input))
                (ifFalse.shape.analyze.time.eval (sizeOf input))) := by omega
        _ = _ := by
          simp [AlgorithmShape.analyze, ResourceProfile.sequential,
            ResourceProfile.conditional, GrowthExpr.eval]
    · calc
        (condition.run input).ops + (ifFalse.run input).ops + 1
            ≤ condition.shape.analyze.time.eval (sizeOf input) +
                ifFalse.shape.analyze.time.eval (sizeOf input) + 1 := by
              omega
        _ ≤ condition.shape.analyze.time.eval (sizeOf input) +
              (1 + max
                (ifTrue.shape.analyze.time.eval (sizeOf input))
                (ifFalse.shape.analyze.time.eval (sizeOf input))) := by omega
        _ = _ := by
          simp [AlgorithmShape.analyze, ResourceProfile.sequential,
            ResourceProfile.conditional, GrowthExpr.eval]

/-- Intrinsically analyzed counted iteration with input-dependent state. -/
def iterate
    {Input : Type u} {sizeOf : Input → ℕ} {State : Input → Type v}
    (initial : AnalyzedComputation sizeOf State)
    (iterations : Input → ℕ) (iterationBound : GrowthExpr)
    (iterations_le : ∀ input,
      iterations input ≤ iterationBound.eval (sizeOf input))
    (step : (input : Input) → State input → Cost (State input))
    (stepShape : AlgorithmShape)
    (step_le : ∀ input state,
      (step input state).ops ≤ stepShape.analyze.time.eval (sizeOf input)) :
    AnalyzedComputation sizeOf State where
  run := fun input =>
    Cost.bind (initial.run input) fun state =>
      Cost.iterate (iterations input) (step input) state
  shape := .sequential initial.shape (.repeat iterationBound stepShape)
  time_le := by
    intro input
    rw [Cost.ops_bind]
    have loopBound := Cost.ops_iterate_le (iterations input)
      (stepShape.analyze.time.eval (sizeOf input)) (step input)
      (initial.run input).value (step_le input)
    calc
      (initial.run input).ops +
          (Cost.iterate (iterations input) (step input)
            (initial.run input).value).ops
        ≤ initial.shape.analyze.time.eval (sizeOf input) +
            iterations input *
              (stepShape.analyze.time.eval (sizeOf input) + 1) :=
          Nat.add_le_add (initial.time_le input) loopBound
      _ ≤ initial.shape.analyze.time.eval (sizeOf input) +
            iterationBound.eval (sizeOf input) *
              (stepShape.analyze.time.eval (sizeOf input) + 1) := by
          gcongr
          exact iterations_le input
      _ = _ := by
        simp [AlgorithmShape.analyze, ResourceProfile.sequential,
          ResourceProfile.iterate, GrowthExpr.eval]

/-- Intrinsically analyzed stateful fold over an input-dependent list. -/
def foldlList
    {Input : Type u} {sizeOf : Input → ℕ} {Item : Type v}
    {State : Input → Type w}
    (items : Input → List Item)
    (lengthBound : GrowthExpr)
    (length_le : ∀ input,
      (items input).length ≤ lengthBound.eval (sizeOf input))
    (initial : AnalyzedComputation sizeOf State)
    (step : (input : Input) → State input → Item → Cost (State input))
    (stepShape : AlgorithmShape)
    (step_le : ∀ input state item,
      (step input state item).ops ≤
        stepShape.analyze.time.eval (sizeOf input)) :
    AnalyzedComputation sizeOf State where
  run := fun input => Cost.bind (initial.run input) fun state =>
    Cost.foldlList (step input) (items input) state
  shape := .sequential initial.shape (.repeat lengthBound stepShape)
  time_le := by
    intro input
    rw [Cost.ops_bind]
    have foldBound := Cost.ops_foldlList_le (step input) (items input)
      (initial.run input).value
      (stepShape.analyze.time.eval (sizeOf input)) (step_le input)
    calc
      (initial.run input).ops +
          (Cost.foldlList (step input) (items input)
            (initial.run input).value).ops
        ≤ initial.shape.analyze.time.eval (sizeOf input) +
            (items input).length *
              (stepShape.analyze.time.eval (sizeOf input) + 1) :=
          Nat.add_le_add (initial.time_le input) foldBound
      _ ≤ initial.shape.analyze.time.eval (sizeOf input) +
            lengthBound.eval (sizeOf input) *
              (stepShape.analyze.time.eval (sizeOf input) + 1) := by
          gcongr
          exact length_le input
      _ = _ := by
        simp [AlgorithmShape.analyze, ResourceProfile.sequential,
          ResourceProfile.iterate, GrowthExpr.eval]

/-- Intrinsically analyzed total while loop.  Fuel is both the termination
certificate and the maximum iteration count. -/
def whileFuel
    {Input : Type u} {sizeOf : Input → ℕ} {State : Input → Type v}
    (initial : AnalyzedComputation sizeOf State)
    (fuel : Input → ℕ) (fuelBound : GrowthExpr)
    (fuel_le : ∀ input, fuel input ≤ fuelBound.eval (sizeOf input))
    (condition : (input : Input) → State input → Cost Bool)
    (conditionShape : AlgorithmShape)
    (condition_le : ∀ input state,
      (condition input state).ops ≤
        conditionShape.analyze.time.eval (sizeOf input))
    (body : (input : Input) → State input → Cost (State input))
    (bodyShape : AlgorithmShape)
    (body_le : ∀ input state,
      (body input state).ops ≤ bodyShape.analyze.time.eval (sizeOf input)) :
    AnalyzedComputation sizeOf (fun input => Cost.WhileResult (State input)) where
  run := fun input => Cost.bind (initial.run input) fun state =>
    Cost.whileFuel (fuel input) (condition input) (body input) state
  shape := .sequential initial.shape
    (.repeat fuelBound (.sequential conditionShape bodyShape))
  time_le := by
    intro input
    rw [Cost.ops_bind]
    have loopBound := Cost.ops_whileFuel_le (fuel input)
      (conditionShape.analyze.time.eval (sizeOf input))
      (bodyShape.analyze.time.eval (sizeOf input))
      (condition input) (body input) (initial.run input).value
      (condition_le input) (body_le input)
    calc
      (initial.run input).ops +
          (Cost.whileFuel (fuel input) (condition input) (body input)
            (initial.run input).value).ops
        ≤ initial.shape.analyze.time.eval (sizeOf input) +
            fuel input *
              (conditionShape.analyze.time.eval (sizeOf input) +
                bodyShape.analyze.time.eval (sizeOf input) + 1) :=
          Nat.add_le_add (initial.time_le input) loopBound
      _ ≤ initial.shape.analyze.time.eval (sizeOf input) +
            fuelBound.eval (sizeOf input) *
              (conditionShape.analyze.time.eval (sizeOf input) +
                bodyShape.analyze.time.eval (sizeOf input) + 1) := by
          gcongr
          exact fuel_le input
      _ = _ := by
        simp [AlgorithmShape.analyze, ResourceProfile.sequential,
          ResourceProfile.iterate, GrowthExpr.eval]

/-- Execute the Boolean polynomial-time checker for an intrinsically analyzed
computation. -/
def decidePolynomialTime
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (program : AnalyzedComputation sizeOf Output) : Bool :=
  program.shape.decidePolynomialTime

/-- A computed `true` result certifies the ordinary semantic implementation
without any additional global cost proof. -/
theorem decidePolynomialTime_sound
    {Input : Type u} {sizeOf : Input → ℕ} {Output : Input → Type v}
    (program : AnalyzedComputation sizeOf Output)
    (accepted : program.decidePolynomialTime = true) :
    program.implementation.IsPolynomial sizeOf := by
  apply IsPolyBound.of_le
    (GrowthExpr.lift_to_size
      (AlgorithmShape.decidePolynomialTime_sound program.shape accepted))
  exact program.time_le

end AnalyzedComputation

/-! ## Linking the executable answer to an actual implementation -/

/-- A costed implementation linked to a finite static resource description.

The `time_le` field prevents dishonest annotations: it must prove that the
symbolic shape bounds the actual instrumented operation counter on every
input. -/
structure StaticallyAnalyzedImplementation
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input} where
  implementation : CostedImplementation function
  sizeOf : Input → ℕ
  shape : AlgorithmShape
  time_le : ∀ input,
    (implementation.run input).ops ≤ shape.analyze.time.eval (sizeOf input)

namespace StaticallyAnalyzedImplementation

/-- Execute the polynomial-time decision procedure for a linked program. -/
def decidePolynomialTime
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (program : StaticallyAnalyzedImplementation (function := function)) : Bool :=
  program.shape.decidePolynomialTime

/-- A `true` result from the executable analyzer certifies the existing
semantic `CostedImplementation.IsPolynomial` predicate. -/
theorem decidePolynomialTime_sound
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (program : StaticallyAnalyzedImplementation (function := function))
    (accepted : program.decidePolynomialTime = true) :
    program.implementation.IsPolynomial program.sizeOf := by
  apply IsPolyBound.of_le
    (GrowthExpr.lift_to_size
      (AlgorithmShape.decidePolynomialTime_sound program.shape accepted))
  exact program.time_le

end StaticallyAnalyzedImplementation

/-! ## Fully profiled implementations -/

/-- Polynomial bounds for every resource counter of a concrete profiled run. -/
structure PolynomialResourceBounds
    {Input : Type u} {Output : Input → Type v}
    (sizeOf : Input → ℕ) (run : (input : Input) → ProfiledCost (Output input)) : Prop where
  time : IsPolyBound sizeOf (fun input => ProfiledCost.steps (run input))
  oracleQueries :
    IsPolyBound sizeOf (fun input => ProfiledCost.oracleQueries (run input))
  distributionSamples :
    IsPolyBound sizeOf (fun input => ProfiledCost.distributionSamples (run input))
  randomBits :
    IsPolyBound sizeOf (fun input => ProfiledCost.randomBits (run input))
  communication :
    IsPolyBound sizeOf (fun input => ProfiledCost.communicationUnits (run input))
  auxiliarySpace :
    IsPolyBound sizeOf (fun input => ProfiledCost.peakCells (run input))

/-- A fully profiled computation linked componentwise to one analyzed shape. -/
structure StaticallyAnalyzedProfiledImplementation
    {Input : Type u} {Output : Input → Type v}
    (function : (input : Input) → Output input) where
  run : (input : Input) → ProfiledCost (Output input)
  correct : ∀ input, (run input).ret = function input
  sizeOf : Input → ℕ
  shape : AlgorithmShape
  time_le : ∀ input,
    ProfiledCost.steps (run input) ≤ shape.analyze.time.eval (sizeOf input)
  queries_le : ∀ input,
    ProfiledCost.oracleQueries (run input) ≤
      shape.analyze.oracleQueries.eval (sizeOf input)
  samples_le : ∀ input,
    ProfiledCost.distributionSamples (run input) ≤
      shape.analyze.distributionSamples.eval (sizeOf input)
  randomBits_le : ∀ input,
    ProfiledCost.randomBits (run input) ≤
      shape.analyze.randomBits.eval (sizeOf input)
  communication_le : ∀ input,
    ProfiledCost.communicationUnits (run input) ≤
      shape.analyze.communication.eval (sizeOf input)
  space_le : ∀ input,
    ProfiledCost.peakCells (run input) ≤
      shape.analyze.auxiliarySpace.eval (sizeOf input)

namespace StaticallyAnalyzedProfiledImplementation

/-- Execute the all-resource polynomial decision procedure. -/
def decideAllPolynomialResources
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (program : StaticallyAnalyzedProfiledImplementation function) : Bool :=
  program.shape.decideAllPolynomialResources

/-- A `true` all-resource answer certifies all counters of the same concrete
profiled execution. -/
theorem decideAllPolynomialResources_sound
    {Input : Type u} {Output : Input → Type v}
    {function : (input : Input) → Output input}
    (program : StaticallyAnalyzedProfiledImplementation function)
    (accepted : program.decideAllPolynomialResources = true) :
    PolynomialResourceBounds program.sizeOf program.run := by
  have bounds := ResourceProfile.allPolynomial_sound program.shape.analyze accepted
  rcases bounds with ⟨htime, hqueries, hsamples, hrandom,
    hcommunication, hspace⟩
  constructor
  · exact IsPolyBound.of_le (GrowthExpr.lift_to_size htime) program.time_le
  · exact IsPolyBound.of_le (GrowthExpr.lift_to_size hqueries) program.queries_le
  · exact IsPolyBound.of_le (GrowthExpr.lift_to_size hsamples) program.samples_le
  · exact IsPolyBound.of_le (GrowthExpr.lift_to_size hrandom) program.randomBits_le
  · exact IsPolyBound.of_le
      (GrowthExpr.lift_to_size hcommunication) program.communication_le
  · exact IsPolyBound.of_le (GrowthExpr.lift_to_size hspace) program.space_le

end StaticallyAnalyzedProfiledImplementation

end EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity
