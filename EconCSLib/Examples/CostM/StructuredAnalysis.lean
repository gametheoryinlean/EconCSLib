/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.SourceCost

/-!
# Regression examples for structured cost extraction

These examples test that the executable program syntax, rather than a
separately maintained complexity tree, generates the cost expression.
They cover nested counted loops, a fuelled while loop, branching, an explicit
degree report, a semantic polynomial-time theorem, and rejection of an
exponential loop bound.
-/

namespace EconCSLib.Examples.CostM.StructuredAnalysis

open EconCSLib.OpenProblem.UnitCostRAM
open EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity

/-! ## Reading ordinary Lean definitions -/

/-- An uninstrumented ordinary Lean function. -/
def ordinaryStraightLine (n : ℕ) : ℕ :=
  (n + 1) * 2

/-- Exact real arithmetic uses the same audited unit-cost real-RAM rule. -/
def ordinaryRealStraightLine (x : ℝ) : ℝ :=
  (x + 1) * 2

/-- Branches are read using condition cost plus the maximum branch cost. -/
def ordinaryBranch (n : ℕ) : ℕ :=
  if n < 10 then n + 1 else n * 2

/-- Structural recursion over a natural is recognized as at most one visit
per constructor in the aggregate input representation. -/
def ordinaryCountdown : ℕ → ℕ
  | 0 => 0
  | n + 1 => ordinaryCountdown n

/-- A standard library traversal with a statically known callback. -/
def ordinaryListMap (values : List ℕ) : List ℕ :=
  values.map fun value => value + 1

/-- A quadratic library routine with a statically known scalar comparator. -/
def ordinaryInsertionSort (values : List ℕ) : List ℕ :=
  values.insertionSort (· ≤ ·)

/-- A callback supplied at runtime cannot be assigned an arbitrary unit cost;
the reader must request a uniform callback contract. -/
def ordinaryUnknownCallback (callback : ℕ → ℕ)
    (values : List ℕ) : List ℕ :=
  values.map callback

/-- A transparent definition from an imported module is followed even when no
special library contract is registered for it. -/
def ordinaryFactorial (n : ℕ) : ℕ :=
  n.factorial

/-- An overloaded operator on an arbitrary user type is not confused with a
one-word scalar instruction. -/
structure LargeValue where
  entries : List ℕ

instance : HAdd LargeValue LargeValue LargeValue where
  hAdd left right := ⟨left.entries ++ right.entries⟩

def ordinaryNonScalarAdd (left right : LargeValue) : LargeValue :=
  left + right

/-- Even on `Nat`, a locally replaced overloaded operation is not silently
identified with the audited standard RAM primitive. -/
def ordinaryCustomScalarAdd (left right : ℕ) : ℕ :=
  letI : HAdd ℕ ℕ ℕ := ⟨Nat.add⟩
  left + right

/-- A model-specific external primitive can be admitted without changing the
reader. Its use remains visible under `assumed source contracts`. -/
opaque modeledExternalSolver (input : ℕ) : ℕ := input

source_cost_contract modeledExternalSolver := polynomial 3

def ordinaryModeledExternal (input : ℕ) : ℕ :=
  modeledExternalSolver input

/-- Direct `for` notation over a standard finite list. -/
def ordinaryForList (values : List ℕ) : ℕ := Id.run do
  let mut total := 0
  for value in values do
    total := total + value
  return total

/-- Nested direct `for` loops generate a quadratic worst-case expression. -/
def ordinaryNestedFor (rows : List (List ℕ)) : ℕ := Id.run do
  let mut total := 0
  for row in rows do
    for value in row do
      total := total + value
  return total

/-- Standard bounded range notation is another audited finite `ForIn`
instance. -/
def ordinaryForRange (bound : ℕ) : ℕ := Id.run do
  let mut total := 0
  for index in [0:bound] do
    total := total + index
  return total

/-- Direct iteration over an array uses the audited standard Array instance. -/
def ordinaryForArray (values : Array ℕ) : ℕ := Id.run do
  let mut total := 0
  for value in values do
    total := total + value
  return total

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- A pure while loop whose maximum number of iterations is explicit. -/
def ordinaryFuelledWhile (fuel state : ℕ) : ℕ :=
  whileFuel fuel (fun value => 0 < value) (fun value => value - 1) state

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- Explicit finite loops can be nested without leaving ordinary Lean. -/
def ordinaryNestedFuel (fuel state : ℕ) : ℕ :=
  repeatFuel fuel
    (fun _ current =>
      whileFuel fuel (fun value => 0 < value)
        (fun value => value - 1) current)
    state

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- The source reader composes an explicit arithmetic bound: this routine
performs at most `n²` iterations. -/
def ordinaryQuadraticFuel (n : ℕ) : ℕ :=
  repeatFuel (n * n) (fun _ total => total + 1) 0

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- A finite loop need not be polynomial. Its explicit fuel is `2^n`, so the
source checker must reject a polynomial-time classification. -/
def ordinaryExponentialFuel (n : ℕ) : ℕ :=
  repeatFuel (2 ^ n) (fun _ total => total + 1) 0

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- A local name must not hide a super-polynomial fuel expression. -/
def ordinaryLetExponentialFuel (n : ℕ) : ℕ :=
  let fuel := 2 ^ n
  repeatFuel fuel (fun _ total => total + 1) 0

def squareBound (n : ℕ) : ℕ := n * n

def exponentialBound (n : ℕ) : ℕ := 2 ^ n

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- Bound inference follows transparent source helpers. -/
def ordinaryHelperQuadraticFuel (n : ℕ) : ℕ :=
  repeatFuel (squareBound n) (fun _ total => total + 1) 0

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- A helper declaration must not hide an exponential loop bound. -/
def ordinaryHelperExponentialFuel (n : ℕ) : ℕ :=
  repeatFuel (exponentialBound n) (fun _ total => total + 1) 0

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- Indexed finite folds expose both their exact bound and their loop index. -/
def ordinaryFoldFin (n : ℕ) : ℕ :=
  foldFin n (fun total index => total + index.val) 0

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- Finite prefix search is linear in its explicit bound. -/
def ordinaryFindFirst (n : ℕ) : Option ℕ :=
  findFirst n (fun index => index == n - 1)

open EconCSLib.OpenProblem.UnitCostRAM.FiniteControl in
/-- Decidable propositions erase their type-level `Eq`/`Decidable` plumbing. -/
def ordinaryFindFirstPropositional (n : ℕ) : Option ℕ :=
  findFirst n (fun index => decide (index = n - 1))

/-- The same negative test through ordinary range-based `for` syntax. -/
def ordinaryExponentialRange (n : ℕ) : ℕ := Id.run do
  let mut total := 0
  for _ in [0:2 ^ n] do
    total := total + 1
  return total

/-- An exponential argument remains visible after expansion into a
structurally recursive helper. -/
def ordinaryExponentialCountdown (n : ℕ) : ℕ :=
  ordinaryCountdown (2 ^ n)

/-- Materializing and traversing all sublists is correctly recognized as
exponential even though the outer control flow is an ordinary finite loop. -/
def ordinaryForSublists (values : List ℕ) : ℕ := Id.run do
  let mut total := 0
  for subset in values.sublists do
    total := total + subset.length
  return total

/-- A cartesian product has a polynomial (quadratic) aggregate-size bound. -/
def ordinaryForProduct (left right : List ℕ) : ℕ := Id.run do
  let mut total := 0
  for pair in left.product right do
    total := total + pair.1 + pair.2
  return total

/-- Calling a function stored in runtime data cannot be bounded by inspecting
the projection alone. -/
structure RuntimeOperation where
  run : ℕ → ℕ

def ordinaryRuntimeOperation (operation : RuntimeOperation) (input : ℕ) : ℕ :=
  operation.run input


#source_cost ordinaryStraightLine
#source_cost ordinaryRealStraightLine
#source_cost ordinaryBranch
#source_cost ordinaryCountdown
#source_cost ordinaryListMap
#source_cost ordinaryInsertionSort
#source_cost ordinaryUnknownCallback
#source_cost ordinaryFactorial
#source_cost ordinaryNonScalarAdd
#source_cost ordinaryCustomScalarAdd
#source_cost ordinaryModeledExternal
#source_cost ordinaryForList
#source_cost ordinaryNestedFor
#source_cost ordinaryForRange
#source_cost ordinaryForArray
#source_cost ordinaryFuelledWhile
#source_cost ordinaryNestedFuel
#source_cost ordinaryQuadraticFuel
#source_cost ordinaryExponentialFuel
#source_cost ordinaryLetExponentialFuel
#source_cost ordinaryHelperQuadraticFuel
#source_cost ordinaryHelperExponentialFuel
#source_cost ordinaryFoldFin
#source_cost ordinaryFindFirst
#source_cost ordinaryFindFirstPropositional
#source_cost ordinaryExponentialRange
#source_cost ordinaryExponentialCountdown
#source_cost ordinaryForSublists
#source_cost ordinaryForProduct
#source_cost ordinaryRuntimeOperation

#guard_source_cost ordinaryQuadraticFuel := polynomial
#guard_source_cost ordinaryRealStraightLine := polynomial
#guard_source_cost ordinaryExponentialFuel := nonpolynomial_bound
#guard_source_cost ordinaryLetExponentialFuel := nonpolynomial_bound
#guard_source_cost ordinaryHelperQuadraticFuel := polynomial
#guard_source_cost ordinaryHelperExponentialFuel := nonpolynomial_bound
#guard_source_cost ordinaryFoldFin := polynomial
#guard_source_cost ordinaryFindFirst := polynomial
#guard_source_cost ordinaryFindFirstPropositional := polynomial
#guard_source_cost ordinaryExponentialRange := nonpolynomial_bound
#guard_source_cost ordinaryExponentialCountdown := nonpolynomial_bound
#guard_source_cost ordinaryForSublists := nonpolynomial_bound
#guard_source_cost ordinaryForProduct := polynomial
#guard_source_cost ordinaryRuntimeOperation := unresolved
#guard_source_cost ordinaryCustomScalarAdd := unresolved

/-! ## Exact typed primitive-path extraction -/

/-- A tiny typed instruction language.  `scan` abstracts an operation whose
cost is linear in the aggregate input size; the other instructions cost one. -/
inductive CounterInstruction : Type → Type where
  | scan (value : ℕ) : CounterInstruction ℕ
  | isEven (value : ℕ) : CounterInstruction Bool
  | double (value : ℕ) : CounterInstruction ℕ

def counterModel : PrimitiveModel CounterInstruction where
  execute
    | .scan value => value
    | .isEven value => decide (Even value)
    | .double value => 2 * value
  cost
    | .scan _ => .inputSize
    | .isEven _ | .double _ => .constant 1

/-- The continuation branches on the actual result of a typed primitive.
PrimitiveProgram.costExpression follows precisely the executed branch. -/
def primitiveBranchProgram (seed : ℕ) :
    PrimitiveProgram CounterInstruction ℕ :=
  .invokeBind (.scan seed) fun scanned =>
    .invokeBind (.isEven scanned) fun even =>
      if even then .invoke (.double scanned) else .pure scanned

#eval (primitiveBranchProgram 4).report counterModel
#eval (primitiveBranchProgram 4).run counterModel 10

example : (primitiveBranchProgram 4).polynomialDegree? counterModel = some 1 := by
  native_decide

example : ((primitiveBranchProgram 4).run counterModel 10).ops = 12 := by
  native_decide

example : ((primitiveBranchProgram 3).run counterModel 10).ops = 11 := by
  native_decide

theorem primitiveBranchProgram_degree_bound :
    ∃ coefficient : ℕ, ∀ inputSize,
      ((primitiveBranchProgram 4).run counterModel inputSize).ops ≤
        coefficient * (inputSize + 1) ^ 1 :=
  (primitiveBranchProgram 4).polynomialDegree?_run_sound counterModel
    (by native_decide)

/-! ## Uniform worst-case structured extraction -/

abbrev CounterState (_input : ℕ) := ℕ
abbrev CounterOutput (_input : ℕ) := ℕ

/-- The exact primitive program can be used as one body inside uniform
structured control flow.  This path performs one linear scan and one
constant-time operation, hence the generated uniform bound n+1. -/
def typedPrimitiveBody : StructuredProgram id CounterState :=
  StructuredProgram.ofPrimitiveProgram counterModel
    (fun _ _ =>
      .invokeBind (.scan 4) fun scanned => .invoke (.double scanned))
    (.add .inputSize (.constant 1)) (by
      intro input state
      simp only [PrimitiveProgram.invoke,
        PrimitiveProgram.costExpression, counterModel, GrowthExpr.eval]
      rfl)

example : typedPrimitiveBody.polynomialDegree? = some 1 := by
  native_decide

/-- One unit-cost increment. -/
def increment : StructuredProgram id CounterState :=
  .operation fun _ state => state + 1

/-- The source program itself contains two loops of length n. -/
def quadraticBody : StructuredProgram id CounterState :=
  .repeat id .inputSize (fun _ => le_rfl) <|
    .repeat id .inputSize (fun _ => le_rfl) increment

/-- Initialize to zero, execute n² increments, and return the counter. -/
def quadraticAlgorithm :
    StructuredAlgorithm id CounterState CounterOutput where
  initial _ := Cost.pure 0
  initialBound := .constant 0
  initial_le := by
    intro input
    change 0 ≤ 0
    exact le_rfl
  body := quadraticBody
  finish := fun _ state => state

#eval quadraticAlgorithm.report
#eval quadraticAlgorithm.function 5

example : quadraticAlgorithm.report.polynomial = true := by
  native_decide

example : quadraticAlgorithm.polynomialDegree? = some 2 := by
  native_decide

example : quadraticAlgorithm.function 5 = 25 := by
  native_decide

theorem quadraticAlgorithm_isPolynomial :
    quadraticAlgorithm.implementation.IsPolynomial id :=
  quadraticAlgorithm.decidePolynomialTime_sound (by native_decide)

theorem quadraticAlgorithm_degree_bound :
    ∃ coefficient : ℕ, ∀ input,
      (quadraticAlgorithm.run input).ops ≤
        coefficient * (input + 1) ^ 2 :=
  quadraticAlgorithm.polynomialDegree?_run_sound (by native_decide)

/-- Countdown uses a total while loop with input-size fuel. -/
def countdownBody : StructuredProgram id CounterState :=
  .whileFuel id .inputSize (fun _ => le_rfl)
    (fun _ state => state != 0)
    (.operation fun _ state => state - 1)

/-- After countdown, branch once and increment on either branch.  Both branch
alternatives are read by the worst-case analyzer. -/
def countdownAndBranchBody : StructuredProgram id CounterState :=
  .sequential countdownBody <|
    .branch (fun _ state => decide (Even state))
      increment increment

def countdownAlgorithm :
    StructuredAlgorithm id CounterState CounterOutput where
  initial input := Cost.pure input
  initialBound := .constant 0
  initial_le := by
    intro input
    change 0 ≤ 0
    exact le_rfl
  body := countdownAndBranchBody
  finish := fun _ state => state

#eval countdownAlgorithm.report

example : countdownAlgorithm.polynomialDegree? = some 1 := by
  native_decide

example : countdownAlgorithm.function 7 = 1 := by
  native_decide

/-- A syntactically explicit exponential loop is rejected.  False means not
certified; only true results are promoted to semantic theorems. -/
def exponentialProgram : StructuredProgram id CounterState :=
  .repeat (fun n => 2 ^ n) .exponential (fun _ => le_rfl) increment

#eval exponentialProgram.report

example : exponentialProgram.decidePolynomialTime = false := by
  native_decide

example : exponentialProgram.polynomialDegree? = none := by
  native_decide

end EconCSLib.Examples.CostM.StructuredAnalysis
