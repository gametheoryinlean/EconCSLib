/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.AlgorithmCost
import EconCSLib.OpenProblem.Util.FiniteControl
import Lean

/-!
# Conservative source reader for ordinary Lean definitions

`AlgorithmCost` gives a kernel-checked cost semantics for algorithms written
in its typed primitive and structured languages.  This module adds a front end
for already existing ordinary Lean `def`s.  It reads the declaration value
stored in `Environment`, traverses `Lean.Expr`, follows transparent helper
definitions in the same namespace, and extracts a symbolic source-level cost.

The reader is total as a diagnostic: every declaration produces a report.
It is deliberately partial as a certifier.  Recursion without a size decrease
certificate, higher-order calls whose body is not statically known, opaque or
foreign declarations, and unsupported recursors contribute `GrowthExpr.unknown`
and a precise issue.  Such a report cannot be promoted to the semantic
polynomial-time theorems.  This prevents source inspection from silently
assigning a false cost to arbitrary Lean code.

The model is source-level unit-cost RAM, not Lean backend instruction count:

* permitted scalar arithmetic/comparison and random access cost one;
* constructing a fixed-arity value and reading a projection cost one;
* evaluating a condition and dispatching a branch cost one;
* only the selected branch is charged, using a symbolic maximum statically;
* explicit call arguments are evaluated before a call;
* type, implicit, and instance arguments are erased from the runtime cost;
* transparent helpers in the analyzed declaration's namespace are unfolded;
* every unresolved operation becomes `unknown`, never zero.

The symbolic variable `n` is a dominating aggregate problem-size parameter.
A runtime natural or runtime container has size at most `n`; an explicitly
constructed bound is analyzed compositionally.  Thus a loop bounded by
`m * m` contributes `n²`, while one bounded by `2 ^ m` is visibly rejected by
the polynomial checker.  Connecting this source convention to a concrete
`sizeOf : Input → ℕ` remains an explicit semantic proof obligation.  A
different encoding (for example bit complexity of unbounded integers)
requires a different cost contract; this module never silently conflates
those models.

Use `#source_cost declarationName` to inspect an ordinary Lean definition.
-/

namespace EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity.SourceReader

open Lean Elab Command

/-! ## Reports available to ordinary Lean code -/

/-- Counts of source constructs observed while reading a declaration. -/
structure SourceStats where
  expressionNodes : ℕ := 0
  applications : ℕ := 0
  lambdas : ℕ := 0
  lets : ℕ := 0
  branches : ℕ := 0
  primitiveCalls : ℕ := 0
  constructorCalls : ℕ := 0
  projectionCalls : ℕ := 0
  expandedDefinitions : ℕ := 0
  structuralRecursors : ℕ := 0
  boundedLoops : ℕ := 0
  monadicBinds : ℕ := 0
  unresolvedCalls : ℕ := 0
  deriving Repr, Inhabited, DecidableEq

namespace SourceStats

def add (left right : SourceStats) : SourceStats where
  expressionNodes := left.expressionNodes + right.expressionNodes
  applications := left.applications + right.applications
  lambdas := left.lambdas + right.lambdas
  lets := left.lets + right.lets
  branches := left.branches + right.branches
  primitiveCalls := left.primitiveCalls + right.primitiveCalls
  constructorCalls := left.constructorCalls + right.constructorCalls
  projectionCalls := left.projectionCalls + right.projectionCalls
  expandedDefinitions :=
    left.expandedDefinitions + right.expandedDefinitions
  structuralRecursors := left.structuralRecursors + right.structuralRecursors
  boundedLoops := left.boundedLoops + right.boundedLoops
  monadicBinds := left.monadicBinds + right.monadicBinds
  unresolvedCalls := left.unresolvedCalls + right.unresolvedCalls

def oneNode : SourceStats := { expressionNodes := 1 }

end SourceStats

/-- One place where source inspection needs a semantic cost contract or a
termination/size argument before it can certify a bound. -/
structure SourceIssue where
  declaration : Name
  kind : String
  detail : String
  deriving Repr, Inhabited, DecidableEq

/-- Internal and user-visible result of reading a source expression. -/
structure SourceAnalysis where
  cost : GrowthExpr
  stats : SourceStats
  issues : Array SourceIssue := #[]
  expanded : Array Name := #[]
  primitives : Array Name := #[]
  assumedContracts : Array Name := #[]
  deriving Repr

namespace SourceAnalysis

def zero : SourceAnalysis where
  cost := .constant 0
  stats := {}

def sequential (left right : SourceAnalysis) : SourceAnalysis where
  cost := .add left.cost right.cost
  stats := left.stats.add right.stats
  issues := left.issues ++ right.issues
  expanded := left.expanded ++ right.expanded
  primitives := left.primitives ++ right.primitives
  assumedContracts := left.assumedContracts ++ right.assumedContracts

def maximum (left right : SourceAnalysis) : SourceAnalysis where
  cost := .maximum left.cost right.cost
  stats := left.stats.add right.stats
  issues := left.issues ++ right.issues
  expanded := left.expanded ++ right.expanded
  primitives := left.primitives ++ right.primitives
  assumedContracts := left.assumedContracts ++ right.assumedContracts

def charge (amount : GrowthExpr) (analysis : SourceAnalysis) : SourceAnalysis :=
  { analysis with cost := .add analysis.cost amount }

def withNode (analysis : SourceAnalysis) : SourceAnalysis :=
  { analysis with stats := analysis.stats.add SourceStats.oneNode }

def unresolved (declaration : Name) (kind detail : String) : SourceAnalysis where
  cost := .unknown
  stats := { expressionNodes := 1, unresolvedCalls := 1 }
  issues := #[{ declaration, kind, detail }]

/-- Record a failed certification obligation without charging a second
`unknown` term.  This is useful when the extracted resource expression is
already `unknown` for exactly the reported reason. -/
def auditIssue (declaration : Name) (kind detail : String) : SourceAnalysis where
  cost := .constant 0
  stats := { unresolvedCalls := 1 }
  issues := #[{ declaration, kind, detail }]

def certified (analysis : SourceAnalysis) : Bool :=
  analysis.issues.isEmpty && analysis.cost.isPolynomial

end SourceAnalysis

/-- Final report for one environment declaration. -/
structure SourceReport where
  declaration : Name
  bodyAvailable : Bool
  analysis : SourceAnalysis
  certifiedPolynomial : Bool
  degreeUpperBound : Option ℕ
  deriving Repr

/-! ## Source-level cost model -/

/-- Names treated as one source-level unit-cost scalar/RAM operation.  This is
intentionally explicit and narrow.  A generic library routine is never
classified as constant time merely because its name resembles an operation. -/
private def primitiveNameStrings : Array String := #[
  "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
  "Nat.succ", "Nat.pred", "Nat.beq", "Nat.decLt", "Nat.decLe",
  "Int.add", "Int.sub", "Int.mul", "Int.ediv", "Int.emod",
  "Int.neg", "Int.beq", "Int.decLt", "Int.decLe",
  "Float.add", "Float.sub", "Float.mul", "Float.div",
  "Float.beq", "Float.decLt", "Float.decLe",
  "Array.get", "Array.get!", "Array.set", "Array.set!",
  "Array.swap", "Array.size", "Array.isEmpty",
  "Prod.fst", "Prod.snd"
]

private def zeroCostNameStrings : Array String := #[
  "id", "Id.run", "Eq.refl", "OfNat.ofNat"
]

private def isPrimitiveName (name : Name) : Bool :=
  primitiveNameStrings.contains name.toString

private def isZeroCostName (name : Name) : Bool :=
  zeroCostNameStrings.contains name.toString

/-- Generic notation such as `+` elaborates through a type class.  It is a
one-word primitive only when all of its data types are scalar types admitted
by this RAM model.  This check prevents a user-defined `HAdd` on a large data
structure from being mislabeled constant-time. -/
private def overloadedPrimitiveTypeArity? (name : Name) : Option ℕ :=
  match name.toString with
  | "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv" => some 3
  | "Neg.neg" | "LT.lt" | "LE.le" | "BEq.beq" => some 1
  | _ => none

private def isScalarType : Expr → Bool
  | .mdata _ body => isScalarType body
  | .const name _ =>
      #["Nat", "Int", "Float", "Real", "Rat", "Bool", "UInt8",
        "UInt16", "UInt32", "UInt64", "USize"].contains name.toString
  | _ => false

private def isNaturalType : Expr → Bool
  | .mdata _ body => isNaturalType body
  | .const name _ => name.toString == "Nat"
  | _ => false

private def hasHomogeneousNaturalTypes (arguments : Array Expr) : Bool :=
  3 ≤ arguments.size &&
    isNaturalType arguments[0]! && isNaturalType arguments[1]! &&
    isNaturalType arguments[2]!

private partial def expressionHasRuntimeVariable : Expr → Bool
  | .fvar _ | .bvar _ | .mvar _ => true
  | .app function argument =>
      expressionHasRuntimeVariable function ||
        expressionHasRuntimeVariable argument
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionHasRuntimeVariable type || expressionHasRuntimeVariable body
  | .letE _ type value body _ =>
      expressionHasRuntimeVariable type ||
        expressionHasRuntimeVariable value ||
        expressionHasRuntimeVariable body
  | .mdata _ body | .proj _ _ body => expressionHasRuntimeVariable body
  | _ => false

private partial def expressionContainsConstFragment
    (expression : Expr) (fragments : Array String) : Bool :=
  match expression with
  | .const name _ =>
      fragments.any fun fragment => name.toString.contains fragment
  | .app function argument =>
      expressionContainsConstFragment function fragments ||
        expressionContainsConstFragment argument fragments
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionContainsConstFragment type fragments ||
        expressionContainsConstFragment body fragments
  | .letE _ type value body _ =>
      expressionContainsConstFragment type fragments ||
        expressionContainsConstFragment value fragments ||
        expressionContainsConstFragment body fragments
  | .mdata _ body | .proj _ _ body =>
      expressionContainsConstFragment body fragments
  | _ => false

private def standardScalarInstanceFragments (name : Name) : Array String :=
  match name.toString with
  | "HAdd.hAdd" => #["instAdd"]
  | "HSub.hSub" => #["instSub"]
  | "HMul.hMul" => #["instMul"]
  | "HDiv.hDiv" => #["instDiv"]
  | "Neg.neg" => #["instNeg"]
  | "LT.lt" => #["instLT"]
  | "LE.le" => #["instLE"]
  | "BEq.beq" => #["instDecidableEq", "instBEqNat", "instBEqInt",
      "instBEqFloat", "instBEqBool", "instBEqUInt", "instBEqUSize"]
  | _ => #[]

private def hasAuditedScalarInstance (name : Name) (arity : ℕ)
    (arguments : Array Expr) : Bool :=
  match arguments[arity]? with
  | some instanceExpression =>
      !expressionHasRuntimeVariable instanceExpression &&
        expressionContainsConstFragment instanceExpression
          (standardScalarInstanceFragments name)
  | none => false

private def isApprovedOverloadedPrimitive
    (name : Name) (arguments : Array Expr) : Bool :=
  match overloadedPrimitiveTypeArity? name with
  | none => false
  | some arity =>
      arity ≤ arguments.size &&
        (arguments.extract 0 arity).all isScalarType &&
        hasAuditedScalarInstance name arity arguments

private def expressionHeadName? (expression : Expr) : Option Name :=
  match expression.getAppFn with
  | .const name _ => some name
  | _ => none

private partial def expressionContainsConstWithPrefix
    (expression : Expr) (prefixes : Array String) : Bool :=
  match expression with
  | .const name _ =>
      prefixes.any fun prefixText => name.toString.startsWith prefixText
  | .app function argument =>
      expressionContainsConstWithPrefix function prefixes ||
        expressionContainsConstWithPrefix argument prefixes
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionContainsConstWithPrefix type prefixes ||
        expressionContainsConstWithPrefix body prefixes
  | .letE _ type value body _ =>
      expressionContainsConstWithPrefix type prefixes ||
        expressionContainsConstWithPrefix value prefixes ||
        expressionContainsConstWithPrefix body prefixes
  | .mdata _ body | .proj _ _ body =>
      expressionContainsConstWithPrefix body prefixes
  | _ => false

private def isIdentityMonad (expression : Expr) : Bool :=
  (expressionHeadName? expression).any fun name => name.toString == "Id"

private def isApprovedFiniteCollectionType (expression : Expr) : Bool :=
  (expressionHeadName? expression).any fun name =>
    #["List", "Array", "Vector", "Std.Range", "Std.Legacy.Range", "Range", "ByteArray",
      "FloatArray", "Subarray", "Finset"].contains name.toString

private def hasApprovedFiniteForInstance (arguments : Array Expr) : Bool :=
  arguments.any fun argument =>
    expressionContainsConstWithPrefix argument #[
      "List.instForIn", "Array.instForIn", "Vector.instForIn",
      "Std.Range.instForIn", "Std.Legacy.Range.instForIn", "Range.instForIn", "ByteArray.instForIn",
      "FloatArray.instForIn", "Subarray.instForIn", "Finset.instForIn"]

private def isForInName (name : Name) : Bool :=
  name.toString == "ForIn.forIn" || name.toString == "ForIn'.forIn'"

private def isMonadicBindName (name : Name) : Bool :=
  name.toString == "Bind.bind"

private def isMonadicPureName (name : Name) : Bool :=
  name.toString == "Pure.pure"

private def isConditionalName (name : Name) : Bool :=
  name == ``ite || name == ``dite || name.toString == "Bool.cond"

private def isCourseOfValuesRecursorName (name : Name) : Bool :=
  #["Nat.brecOn", "List.brecOn"].contains name.toString

/-- Audited source-level cost rules for common total library combinators.
Callback positions refer to the array of explicit arguments. -/
private inductive LibraryCostRule where
  | fixed (operations : ℕ)
  | logarithmic
  | linear
  | nLogN
  | polynomial (degree : ℕ)
  | exponentialOutput
  | factorialOutput
  | linearWithCallbacks (callbackIndices : Array ℕ)
  | nLogNWithCallbacks (callbackIndices : Array ℕ)
  | polynomialWithCallbacks (degree : ℕ) (callbackIndices : Array ℕ)
  deriving Repr, Inhabited

private def LibraryCostRule.containsIteration : LibraryCostRule → Bool
  | .fixed _ => false
  | _ => true

/-- Where an audited library routine obtains the number of iterations. -/
private inductive BoundLocator where
  | aggregateInput
  | naturalArgument (index : ℕ)
  | collectionArgument (index : ℕ)

private def argumentFromEnd? (arguments : Array Expr)
    (offset : ℕ) : Option Expr :=
  if offset < arguments.size then
    some arguments[arguments.size - 1 - offset]!
  else none

mutual
/-- Conservative symbolic magnitude for a natural-valued source expression.
This is used for loop bounds, not for the operation cost of evaluating the
expression itself. -/
private partial def inferNaturalGrowth : Expr → GrowthExpr
  | .mdata _ body => inferNaturalGrowth body
  | .lit (.natVal value) => .constant value
  | .bvar _ | .fvar _ => .inputSize
  | expression@(.app ..) =>
      let function := expression.getAppFn
      let arguments := expression.getAppArgs
      match function with
      | .const name _ =>
          let text := name.toString
          if text == "Nat.add" ||
              (text == "HAdd.hAdd" && hasHomogeneousNaturalTypes arguments) then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some left, some right =>
                .add (inferNaturalGrowth left) (inferNaturalGrowth right)
            | _, _ => .unknown
          else if text == "Nat.mul" ||
              (text == "HMul.hMul" && hasHomogeneousNaturalTypes arguments) then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some left, some right =>
                .mul (inferNaturalGrowth left) (inferNaturalGrowth right)
            | _, _ => .unknown
          else if #["Nat.sub", "Nat.div", "Nat.mod"].contains text ||
              (#["HSub.hSub", "HDiv.hDiv"].contains text &&
                hasHomogeneousNaturalTypes arguments) then
            match argumentFromEnd? arguments 1 with
            | some left => inferNaturalGrowth left
            | none => .unknown
          else if #["Nat.max", "Max.max", "max"].contains text then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some left, some right =>
                .maximum (inferNaturalGrowth left) (inferNaturalGrowth right)
            | _, _ => .unknown
          else if text == "Nat.succ" then
            match argumentFromEnd? arguments 0 with
            | some value => .add (inferNaturalGrowth value) (.constant 1)
            | none => .unknown
          else if text == "OfNat.ofNat" && 1 ≤ arguments.size &&
              isNaturalType arguments[0]! then
            -- Numerals elaborate through `OfNat`; the natural literal is the
            -- penultimate raw argument, immediately before its instance.
            match argumentFromEnd? arguments 1 with
            | some literal => inferNaturalGrowth literal
            | none => .unknown
          else if text == "Nat.pow" ||
              (text == "HPow.hPow" && hasHomogeneousNaturalTypes arguments) then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some base, some exponent =>
                let baseGrowth := inferNaturalGrowth base
                match inferNaturalGrowth exponent with
                | .constant fixed => .pow baseGrowth fixed
                | exponentGrowth =>
                    match baseGrowth with
                    | .constant 0 => .constant 0
                    | .constant 1 => .constant 1
                    | .constant 2 =>
                        if exponentGrowth == .inputSize then .exponential
                        else .unknown
                    | _ =>
                        -- Variable-base exponentiation can exceed 2^n.
                        if exponentGrowth == .constant 0 then .constant 1
                        else .unknown
            | _, _ => .unknown
          else if text == "Nat.factorial" then .factorial
          else if #["List.length", "Array.size", "Finset.card"].contains text then
            match argumentFromEnd? arguments 0 with
            | some collection => inferCollectionGrowth collection
            | none => .unknown
          else .unknown
      | _ => .unknown
  | _ => .unknown

/-- Conservative cardinality for finite containers that occur as loop
sources.  Runtime input containers contribute `n`; explicitly constructed
containers inherit the growth of their construction bound. -/
private partial def inferCollectionGrowth : Expr → GrowthExpr
  | .mdata _ body => inferCollectionGrowth body
  | .bvar _ | .fvar _ => .inputSize
  | expression@(.app ..) =>
      let function := expression.getAppFn
      let arguments := expression.getAppArgs
      match function with
      | .const name _ =>
          let text := name.toString
          if text == "List.nil" then .constant 0
          else if text == "List.cons" then
            match argumentFromEnd? arguments 0 with
            | some tail => .add (.constant 1) (inferCollectionGrowth tail)
            | none => .unknown
          else if text == "List.append" then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some left, some right =>
                .add (inferCollectionGrowth left) (inferCollectionGrowth right)
            | _, _ => .unknown
          else if #["List.zip", "List.zipWith", "List.product",
              "Finset.product"].contains text then
            match argumentFromEnd? arguments 1, argumentFromEnd? arguments 0 with
            | some left, some right =>
                if #["List.product", "Finset.product"].contains text then
                  .mul (inferCollectionGrowth left) (inferCollectionGrowth right)
                else
                  .add (inferCollectionGrowth left) (inferCollectionGrowth right)
            | _, _ => .unknown
          else if #["List.range", "Array.range", "Finset.range"].contains text then
            match argumentFromEnd? arguments 0 with
            | some bound => inferNaturalGrowth bound
            | none => .unknown
          else if #["List.replicate", "Array.replicate"].contains text then
            match argumentFromEnd? arguments 1 with
            | some count => inferNaturalGrowth count
            | none => .unknown
          else if #["List.map", "List.filter", "List.filterMap",
              "List.reverse", "List.take", "List.drop",
              "List.toArray", "Array.toList",
              "Array.map", "Array.filter", "Array.filterMap",
              "Finset.filter", "Finset.image", "Finset.map"].contains text then
            match argumentFromEnd? arguments 0 with
            | some source => inferCollectionGrowth source
            | none => .unknown
          else if #["List.sublists", "Finset.powerset"].contains text then
            match argumentFromEnd? arguments 0 with
            | some source =>
                match inferCollectionGrowth source with
                | .constant count => .constant (2 ^ count)
                | .inputSize => .exponential
                | _ => .unknown
            | none => .unknown
          else if text == "List.permutations" then
            match argumentFromEnd? arguments 0 with
            | some source =>
                match inferCollectionGrowth source with
                | .constant count => .constant count.factorial
                | .inputSize => .factorial
                | _ => .unknown
            | none => .unknown
          else if text == "Finset.univ" then .inputSize
          else if text == "Std.Legacy.Range.mk" then
            if let some stop := arguments[1]? then inferNaturalGrowth stop
            else .unknown
          else .unknown
      | _ => .unknown
  | _ => .unknown
end

private def libraryBoundLocator? (name : Name) : BoundLocator :=
  let text := name.toString
  if #["List.range", "Array.range", "Finset.range", "Nat.pow",
      "List.replicate", "Array.replicate",
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.repeatFuel",
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.whileFuel",
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.foldFin",
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.findFirst",
      "Fin.foldl", "Fin.foldlM"].contains text then
    if text == "Nat.pow" then .naturalArgument 1 else .naturalArgument 0
  else if #["List.length", "List.reverse", "List.append", "List.get?",
      "Array.toList", "Finset.card", "Finset.toList", "Finset.attach",
      "List.mergeSort", "Array.qsort", "List.sublists",
      "Finset.powerset", "List.permutations"].contains text then
    .collectionArgument 0
  else if #["List.take", "List.drop", "List.map", "List.filter",
      "List.filterMap", "List.any", "List.all", "List.find?",
      "List.mapM", "List.filterM", "List.filterMapM", "List.anyM",
      "List.allM", "List.findM?", "List.insertionSort"].contains text then
    .collectionArgument 1
  else if #["List.foldl", "List.foldr", "List.foldlM", "List.foldrM",
      "Array.foldl", "Array.foldr", "Array.foldlM", "Array.foldrM"].contains text then
    .collectionArgument 2
  else if #["Array.map", "Array.filter", "Array.filterMap", "Array.any",
      "Array.all", "Array.find?", "Array.mapM", "Array.filterM",
      "Array.filterMapM", "Array.anyM", "Array.allM",
      "Array.findM?"].contains text then
    .collectionArgument 1
  else if text == "Finset.fold" then .collectionArgument 3
  else .aggregateInput

/-- Scalar exponentiation with a natural exponent is implemented here as at
most one unit-cost multiplication per exponent unit.  This is a conservative
upper bound (exponentiation by squaring can be faster), and unlike arbitrary
`HPow` instances it has a uniform RAM interpretation. -/
private def isApprovedNaturalExponentPower (name : Name)
    (arguments : Array Expr) : Bool :=
  name.toString == "HPow.hPow" && 3 ≤ arguments.size &&
    isScalarType arguments[0]! && isNaturalType arguments[1]! &&
    isScalarType arguments[2]!

/-- Total materialization cost of all subsets, including their stored
elements.  Only the directly representable input-size and constant cases are
accepted; larger symbolic exponents remain unknown rather than understated. -/
private def powersetMaterializationCost : GrowthExpr → GrowthExpr
  | .constant count => .constant ((count + 1) * 2 ^ count)
  | .inputSize => .mul (.add .inputSize (.constant 1)) .exponential
  | _ => .unknown

/-- Total materialization cost of all permutations, including the elements
stored in each permutation. -/
private def permutationsMaterializationCost : GrowthExpr → GrowthExpr
  | .constant count => .constant ((count + 1) * count.factorial)
  | .inputSize => .mul (.add .inputSize (.constant 1)) .factorial
  | _ => .unknown

/-- A declaration-specific source cost assumption.  This is needed for an
opaque primitive, foreign routine, oracle, or solver whose Lean body cannot be
read.  Registering it changes only the diagnostic source model; a semantic
RAM theorem must still prove the corresponding local implementation bound. -/
private structure RegisteredSourceContract where
  declaration : Name
  rule : LibraryCostRule
  deriving Repr, Inhabited

private def addRegisteredSourceContract
    (state : NameMap LibraryCostRule)
    (entry : RegisteredSourceContract) : NameMap LibraryCostRule :=
  state.insert entry.declaration entry.rule

private initialize sourceContractExtension :
    SimplePersistentEnvExtension RegisteredSourceContract
      (NameMap LibraryCostRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addRegisteredSourceContract
    addImportedFn := fun entries =>
      mkStateFromImportedEntries addRegisteredSourceContract {} entries }

private def registeredSourceCostRule? (environment : Environment)
  (name : Name) : Option LibraryCostRule :=
  (sourceContractExtension.getState environment).find? name

private def libraryCostRule? (name : Name) : Option LibraryCostRule :=
  let text := name.toString
  if #[
      "List.length", "List.reverse", "List.append",
      "List.get?", "List.take", "List.drop",
      "List.zip", "List.zipWith", "List.flatten", "List.toArray",
      "List.range", "Array.toList", "Array.range",
      "Finset.card", "Finset.toList", "Finset.attach", "Finset.range"
    ].contains text then
    some .linear
  else if text == "Nat.gcd" then
    -- Euclid performs at most linearly many recursive reductions in the
    -- numeric input measure used by the unit-cost RAM source reader.  The
    -- sharper logarithmic estimate is unnecessary for polynomiality and
    -- would require a separate bit-length convention for natural words.
    some .linear
  else if #[
      "List.map", "List.filter", "List.filterMap", "List.foldl",
      "List.foldr", "List.any", "List.all", "List.find?",
      "List.mapM", "List.filterM", "List.filterMapM", "List.foldlM",
      "List.foldrM", "List.anyM", "List.allM", "List.findM?",
      "Array.map", "Array.filter", "Array.filterMap", "Array.foldl",
      "Array.foldr", "Array.any", "Array.all", "Array.find?",
      "Array.mapM", "Array.filterM", "Array.filterMapM", "Array.foldlM",
      "Array.foldrM", "Array.anyM", "Array.allM", "Array.findM?"
    ].contains text then
    some (.linearWithCallbacks #[0])
  else if text == "Finset.fold" then
    -- Both the binary operation and the element map run once per element.
    some (.linearWithCallbacks #[0, 2])
  else if #["Fin.foldl", "Fin.foldlM"].contains text then
    some (.linearWithCallbacks #[1])
  else if text ==
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.repeatFuel" then
    some (.linearWithCallbacks #[1])
  else if text ==
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.whileFuel" then
    some (.linearWithCallbacks #[1, 2])
  else if text ==
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.foldFin" then
    some (.linearWithCallbacks #[1])
  else if text ==
      "EconCSLib.OpenProblem.UnitCostRAM.FiniteControl.findFirst" then
    some (.linearWithCallbacks #[1])
  else if text == "List.mergeSort" then
    some (.nLogNWithCallbacks #[1])
  else if text == "Array.qsort" then
    -- Lean's in-place quicksort can be quadratic in the worst case.
    some (.polynomialWithCallbacks 2 #[1])
  else if text == "List.insertionSort" then
    some (.polynomialWithCallbacks 2 #[0])
  else if #["List.product", "Finset.product"].contains text then
    some (.polynomial 2)
  else if #["List.flatMap", "List.bind", "Array.flatMap"].contains text then
    some (.polynomialWithCallbacks 2 #[0])
  else if #["List.sublists", "Finset.powerset"].contains text then
    some .exponentialOutput
  else if text == "List.permutations" then
    some .factorialOutput
  else if #["Nat.pow", "List.replicate", "Array.replicate"].contains text then
    some .linear
  else none

/-- Retain only explicit arguments by following the declaration's telescope.
Implicit type parameters and instance dictionaries are erased by this source
cost model. -/
private def explicitArguments (type : Expr) (arguments : Array Expr) : Array Expr :=
  let rec visit (type : Expr) (index : ℕ) (result : Array Expr) : Array Expr :=
    if h : index < arguments.size then
      match type with
      | .forallE _ _ body binderInfo =>
          let result :=
            if binderInfo.isExplicit then result.push arguments[index]
            else result
          visit body (index + 1) result
      | _ => result ++ arguments.extract index arguments.size
    else result
  visit type 0 #[]

/-- Retain type-class arguments. Most are erased from the RAM model, but a
`Decidable` argument to `ite` is executable code that computes the branch. -/
private def instanceArguments (type : Expr)
    (arguments : Array Expr) : Array Expr :=
  let rec visit (type : Expr) (index : ℕ) (result : Array Expr) : Array Expr :=
    if h : index < arguments.size then
      match type with
      | .forallE _ _ body binderInfo =>
          let result :=
            if binderInfo.isInstImplicit then result.push arguments[index]
            else result
          visit body (index + 1) result
      | _ => result
    else result
  visit type 0 #[]

mutual
/-- Extend direct bound recognition through local helper definitions.  This
does not charge helper execution (the ordinary expression reader does that
separately); it only recovers the magnitude of a value subsequently used as
a loop bound. -/
private partial def inferNaturalGrowthM (expression : Expr)
    (visiting : NameSet := {}) (fuel : ℕ := 32) : MetaM GrowthExpr := do
  let direct := inferNaturalGrowth expression
  if direct != .unknown then return direct
  if fuel == 0 then return .unknown
  match expression with
  | .mdata _ body => inferNaturalGrowthM body visiting (fuel - 1)
  | .letE _ _ value body _ =>
      inferNaturalGrowthM (body.instantiate1 value) visiting (fuel - 1)
  | expression@(.app ..) =>
      let arguments := expression.getAppArgs
      match expression.getAppFn with
      | .const name _ =>
          if visiting.contains name then return .unknown
          let info ← getConstInfo name
          if isConditionalName name then
            let explicit := explicitArguments info.type arguments
            if explicit.size < 3 then return .unknown
            let left ← inferNaturalGrowthM explicit[explicit.size - 2]!
              visiting (fuel - 1)
            let right ← inferNaturalGrowthM explicit[explicit.size - 1]!
              visiting (fuel - 1)
            return .maximum left right
          match info with
          | .defnInfo definition =>
              inferNaturalGrowthM (definition.value.beta arguments)
                (visiting.insert name) (fuel - 1)
          | .opaqueInfo opaqueValue =>
              inferNaturalGrowthM (opaqueValue.value.beta arguments)
                (visiting.insert name) (fuel - 1)
          | _ => return .unknown
      | _ => return .unknown
  | _ => return .unknown

/-- Helper-expanding counterpart for finite collection cardinalities. -/
private partial def inferCollectionGrowthM (expression : Expr)
    (visiting : NameSet := {}) (fuel : ℕ := 32) : MetaM GrowthExpr := do
  let direct := inferCollectionGrowth expression
  if direct != .unknown then return direct
  if fuel == 0 then return .unknown
  match expression with
  | .mdata _ body => inferCollectionGrowthM body visiting (fuel - 1)
  | .letE _ _ value body _ =>
      inferCollectionGrowthM (body.instantiate1 value) visiting (fuel - 1)
  | expression@(.app ..) =>
      let arguments := expression.getAppArgs
      match expression.getAppFn with
      | .const name _ =>
          if visiting.contains name then return .unknown
          let info ← getConstInfo name
          if isConditionalName name then
            let explicit := explicitArguments info.type arguments
            if explicit.size < 3 then return .unknown
            let left ← inferCollectionGrowthM explicit[explicit.size - 2]!
              visiting (fuel - 1)
            let right ← inferCollectionGrowthM explicit[explicit.size - 1]!
              visiting (fuel - 1)
            return .maximum left right
          match info with
          | .defnInfo definition =>
              inferCollectionGrowthM (definition.value.beta arguments)
                (visiting.insert name) (fuel - 1)
          | .opaqueInfo opaqueValue =>
              inferCollectionGrowthM (opaqueValue.value.beta arguments)
                (visiting.insert name) (fuel - 1)
          | _ => return .unknown
      | _ => return .unknown
  | _ => return .unknown
end

private structure ReaderContext where
  root : Name
  scopePrefix : Name
  visiting : NameSet := {}
  depth : ℕ := 0
  maxDepth : ℕ := 64

private def ReaderContext.descend (context : ReaderContext)
    (name : Name) : ReaderContext :=
  { context with
    visiting := context.visiting.insert name
    depth := context.depth + 1 }

private def combineSequential (parts : Array SourceAnalysis) : SourceAnalysis :=
  parts.foldl SourceAnalysis.sequential SourceAnalysis.zero

private def combineMaximum (parts : Array SourceAnalysis) : SourceAnalysis :=
  if let some first := parts[0]? then
    parts.extract 1 parts.size |>.foldl SourceAnalysis.maximum first
  else SourceAnalysis.zero

/-- Try the two standard size notions used by structural recursion. Runtime
variables denote an aggregate input of size `n`; explicit naturals and
explicitly constructed standard containers retain their sharper bound. -/
private def inferStructuralMajorGrowth (major : Expr) : MetaM GrowthExpr := do
  let natural ← inferNaturalGrowthM major
  if natural != .unknown then pure natural
  else inferCollectionGrowthM major

/-! The mutually recursive reader lives in MetaM because it queries
declaration types and values from the current environment. -/

mutual
private partial def analyzeExpr (context : ReaderContext)
    (expression : Expr) : MetaM SourceAnalysis := do
  if context.maxDepth ≤ context.depth then
    return SourceAnalysis.unresolved context.root "expansion-depth"
      s!"stopped after {context.maxDepth} transparent-definition expansions"
  match expression with
  | .bvar _ | .fvar _ | .sort _ | .const _ _ | .lit _ =>
      return SourceAnalysis.zero.withNode
  | .mvar _ =>
      return SourceAnalysis.unresolved context.root "metavariable"
        "the declaration body contains an unresolved metavariable"
  | .mdata _ body =>
      return (← analyzeExpr context body).withNode
  | .forallE .. =>
      -- Types and propositions are erased from executable source cost.
      return SourceAnalysis.zero.withNode
  | .lam _ _ body _ =>
      let result ← analyzeExpr context body
      return { result.withNode with
        stats := { result.withNode.stats with
          lambdas := result.stats.lambdas + 1 } }
  | .letE _ _ value body _ =>
      let valueAnalysis ← analyzeExpr context value
      -- Substitute the computed value into the body before inspecting loop
      -- bounds. Otherwise `let fuel := 2 ^ n; repeatFuel fuel ...` would hide
      -- an exponential bound behind an undifferentiated local variable.
      -- The value is also charged at its binding site; any syntactic
      -- duplication caused by substitution is conservative.
      let bodyAnalysis ← analyzeExpr context (body.instantiate1 value)
      let result := valueAnalysis.sequential bodyAnalysis |>.withNode
      return { result with
        stats := { result.stats with lets := result.stats.lets + 1 } }
  | .proj _ _ object =>
      let result := (← analyzeExpr context object).charge (.constant 1) |>.withNode
      return { result with
        stats := { result.stats with
          projectionCalls := result.stats.projectionCalls + 1 } }
  | expression@(.app ..) =>
      -- Applications whose result is itself a type or proposition are erased
      -- by execution. This prevents type constructors such as `Eq` and
      -- `Decidable` from being mistaken for runtime subroutines when they
      -- occur inside a concrete decision procedure.
      let expressionType ← Meta.whnf (← Meta.inferType expression)
      if Expr.isSort expressionType then
        return SourceAnalysis.zero.withNode
      expression.withApp fun function arguments => do
        match function with
        | .const name _ => analyzeConstantCall context name arguments
        | .lam .. =>
            let argumentAnalyses ← arguments.mapM (analyzeExpr context)
            let instantiated := function.beta arguments
            let bodyAnalysis ← analyzeExpr context instantiated
            let result := (combineSequential argumentAnalyses).sequential
              bodyAnalysis |>.withNode
            return { result with
              stats := { result.stats with
                applications := result.stats.applications + 1 } }
        | .fvar _ | .bvar _ =>
            let argumentAnalyses ← arguments.mapM (analyzeExpr context)
            let unresolved := SourceAnalysis.unresolved context.root
              "higher-order-call"
              "called function is a runtime variable; supply a uniform cost contract"
            return (combineSequential argumentAnalyses).sequential unresolved
        | _ =>
            let functionAnalysis ← analyzeExpr context function
            let argumentAnalyses ← arguments.mapM (analyzeExpr context)
            let unresolved := SourceAnalysis.unresolved context.root
              "unsupported-function-expression"
              "application head is neither a declaration nor a statically known lambda"
            return functionAnalysis.sequential
              (combineSequential argumentAnalyses) |>.sequential unresolved

private partial def analyzeConditional (context : ReaderContext)
    (name : Name) (arguments : Array Expr) : MetaM SourceAnalysis := do
  let info ← getConstInfo name
  let explicit := explicitArguments info.type arguments
  if explicit.size < 3 then
    return SourceAnalysis.unresolved name "malformed-conditional"
      s!"expected condition and two branches, found {explicit.size} explicit arguments"
  let condition := explicit[explicit.size - 3]!
  let ifTrue := explicit[explicit.size - 2]!
  let ifFalse := explicit[explicit.size - 1]!
  let conditionAnalysis ← analyzeExpr context condition
  let decisionAnalyses ←
    (instanceArguments info.type arguments).mapM (analyzeExpr context)
  let trueAnalysis ← analyzeExpr context ifTrue
  let falseAnalysis ← analyzeExpr context ifFalse
  let branches := trueAnalysis.maximum falseAnalysis
  let result := conditionAnalysis.sequential (combineSequential decisionAnalyses)
    |>.sequential branches |>.charge (.constant 1) |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      branches := result.stats.branches + 1 } }

private partial def analyzeCasesRecursor (context : ReaderContext)
    (name : Name) (recursor : RecursorVal)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  let majorIndex := recursor.getMajorIdx
  let firstMinor := recursor.getFirstMinorIdx
  if hMajor : majorIndex < arguments.size then
    let majorAnalysis ← analyzeExpr context arguments[majorIndex]
    let mut minors : Array SourceAnalysis := #[]
    for offset in [:recursor.numMinors] do
      let index := firstMinor + offset
      if h : index < arguments.size then
        minors := minors.push (← analyzeExpr context arguments[index])
    let result := majorAnalysis.sequential (combineMaximum minors)
      |>.charge (.constant 1) |>.withNode
    return { result with
      stats := { result.stats with
        applications := result.stats.applications + 1
        branches := result.stats.branches + 1 } }
  else
    return SourceAnalysis.unresolved name "malformed-cases-recursor"
      s!"major argument index {majorIndex} is outside {arguments.size} arguments"

/-- Some standard `casesOn` declarations are transparent wrappers rather than
kernel recursor constants.  Their explicit telescope is major value followed
by alternative handlers. -/
private partial def analyzeCasesWrapper (context : ReaderContext)
    (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  let explicit := explicitArguments info.type arguments
  if explicit.size < 2 then
    return SourceAnalysis.unresolved name "malformed-cases-wrapper"
      s!"expected a major value and alternatives, found {explicit.size} explicit arguments"
  let majorAnalysis ← analyzeExpr context explicit[0]!
  let mut alternatives : Array SourceAnalysis := #[]
  for index in [1:explicit.size] do
    alternatives := alternatives.push
      (← analyzeCallableBody context explicit[index]!)
  let result := majorAnalysis.sequential (combineMaximum alternatives)
    |>.charge (.constant 1) |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      branches := result.stats.branches + 1 } }

/-- Analyze the body value supplied to a recursor.  A bare helper declaration
must be expanded even though merely referring to an ordinary constant usually
costs nothing. -/
private partial def analyzeCallableBody (context : ReaderContext)
    (body : Expr) : MetaM SourceAnalysis := do
  match body with
  | .const name _ => analyzeConstantCall context name #[]
  | _ => analyzeExpr context body

/-- A structural recursor visits at most linearly many constructors in the
aggregate source input representation.  Minor premises are alternative
constructor handlers, so the per-visit cost is their maximum. -/
private partial def analyzeStructuralRecursor (context : ReaderContext)
    (name : Name) (recursor : RecursorVal)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  let majorIndex := recursor.getMajorIdx
  let firstMinor := recursor.getFirstMinorIdx
  if hMajor : majorIndex < arguments.size then
    let majorAnalysis ← analyzeExpr context arguments[majorIndex]
    let mut minors : Array SourceAnalysis := #[]
    for offset in [:recursor.numMinors] do
      let index := firstMinor + offset
      if h : index < arguments.size then
        minors := minors.push (← analyzeCallableBody context arguments[index])
    let perVisit := (combineMaximum minors).charge (.constant 1)
    let iterationBound ← inferStructuralMajorGrowth arguments[majorIndex]
    let boundAudit :=
      if iterationBound == .unknown then
        SourceAnalysis.auditIssue name "unknown-structural-bound"
          "could not derive a constructor-count bound for the structural-recursion major argument"
      else SourceAnalysis.zero
    let loop : SourceAnalysis :=
      { perVisit with cost := .mul iterationBound perVisit.cost }
    let result := majorAnalysis.sequential boundAudit |>.sequential loop |>.withNode
    return { result with
      stats := { result.stats with
        applications := result.stats.applications + 1
        structuralRecursors := result.stats.structuralRecursors + 1 } }
  else
    return SourceAnalysis.unresolved name "malformed-structural-recursor"
      s!"major argument index {majorIndex} is outside {arguments.size} arguments"

/-- Course-of-values helpers such as Nat.brecOn expose the major value and
one step function as their final explicit arguments. -/
private partial def analyzeCourseOfValuesRecursor
    (context : ReaderContext) (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  let explicit := explicitArguments info.type arguments
  if explicit.size < 2 then
    return SourceAnalysis.unresolved name "malformed-course-of-values-recursor"
      s!"expected a major value and step function, found {explicit.size} explicit arguments"
  let major := explicit[explicit.size - 2]!
  let step := explicit[explicit.size - 1]!
  let majorAnalysis ← analyzeExpr context major
  let stepAnalysis ← analyzeCallableBody context step
  let perVisit := stepAnalysis.charge (.constant 1)
  let iterationBound ← inferNaturalGrowthM major
  let boundAudit :=
    if iterationBound == .unknown then
      SourceAnalysis.auditIssue name "unknown-course-of-values-bound"
        "could not derive a natural upper bound for the course-of-values recursion"
    else SourceAnalysis.zero
  let loop : SourceAnalysis :=
    { perVisit with cost := .mul iterationBound perVisit.cost }
  let result := majorAnalysis.sequential boundAudit |>.sequential loop |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      structuralRecursors := result.stats.structuralRecursors + 1 } }

private partial def analyzeLibraryCall (context : ReaderContext)
    (name : Name) (info : ConstantInfo) (arguments : Array Expr)
    (rule : LibraryCostRule) (registered := false) : MetaM SourceAnalysis := do
  let explicit := explicitArguments info.type arguments
  let callbackIndices := match rule with
    | .linearWithCallbacks indices
    | .nLogNWithCallbacks indices
    | .polynomialWithCallbacks _ indices => indices
    | _ => #[]
  let mut argumentAnalyses : Array SourceAnalysis := #[]
  for index in [:explicit.size] do
    if callbackIndices.contains index then
      -- Creating/passing a closure does not execute its body.  The body is
      -- analyzed below at the number of calls promised by the contract.
      argumentAnalyses := argumentAnalyses.push .zero
    else
      argumentAnalyses := argumentAnalyses.push
        (← analyzeExpr context explicit[index]!)
  let argumentsResult := combineSequential argumentAnalyses
  let callbackCost (index : ℕ) : MetaM SourceAnalysis := do
    if h : index < explicit.size then
      match explicit[index] with
      | .fvar _ | .bvar _ =>
          pure <| SourceAnalysis.unresolved context.root "unknown-callback"
            "library callback is supplied at runtime; provide a uniform callback cost contract"
      | callback => analyzeCallableBody context callback
    else
      pure <| SourceAnalysis.unresolved name "malformed-library-contract"
        s!"callback index {index} is outside {explicit.size} explicit arguments"
  let callbackAuditAndCost (indices : Array ℕ) : MetaM (SourceAnalysis × GrowthExpr) := do
    let callbacks ← indices.mapM callbackCost
    let audit := combineSequential <|
      callbacks.map fun callback => { callback with cost := .constant 0 }
    let cost := callbacks.foldl
      (fun total callback => .add total callback.cost) (.constant 0)
    pure (audit, cost)
  let iterationBound ←
    if registered || !rule.containsIteration then pure .inputSize
    else
      match libraryBoundLocator? name with
      | .aggregateInput => pure .inputSize
      | .naturalArgument index =>
          if let some argument := explicit[index]? then
            inferNaturalGrowthM argument
          else pure .unknown
      | .collectionArgument index =>
          if let some argument := explicit[index]? then
            inferCollectionGrowthM argument
          else pure .unknown
  let boundAudit :=
    if rule.containsIteration && iterationBound == .unknown then
      SourceAnalysis.auditIssue name "unknown-iteration-bound"
        s!"could not derive a finite symbolic upper bound from the loop argument of {name}"
    else SourceAnalysis.zero
  let (callbackAudit, localCost) ← match rule with
    | .fixed operations => pure (.zero, .constant operations)
    | .logarithmic => pure (.zero, .logarithm 2 iterationBound)
    | .linear => pure (.zero, iterationBound)
    | .nLogN => pure (.zero,
        .mul iterationBound (.logarithm 2 iterationBound))
    | .polynomial degree => pure (.zero, .pow iterationBound degree)
    | .exponentialOutput =>
        pure (.zero, powersetMaterializationCost iterationBound)
    | .factorialOutput =>
        pure (.zero, permutationsMaterializationCost iterationBound)
    | .linearWithCallbacks indices =>
        let (audit, callbacks) ← callbackAuditAndCost indices
        pure (audit, .mul iterationBound (.add callbacks (.constant 1)))
    | .nLogNWithCallbacks indices =>
        let (audit, callbacks) ← callbackAuditAndCost indices
        pure (audit, .mul (.mul iterationBound (.logarithm 2 iterationBound))
          (.add callbacks (.constant 1)))
    | .polynomialWithCallbacks degree indices =>
        let (audit, callbacks) ← callbackAuditAndCost indices
        pure (audit, .mul (.pow iterationBound degree)
          (.add callbacks (.constant 1)))
  let result := argumentsResult.sequential callbackAudit |>.sequential boundAudit
    |>.charge localCost |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      primitiveCalls := result.stats.primitiveCalls + 1
      boundedLoops := result.stats.boundedLoops +
        (if rule.containsIteration then 1 else 0) }
    primitives := result.primitives.push name
    assumedContracts :=
      if registered then result.assumedContracts.push name
      else result.assumedContracts }

/-- Analyze the direct-style `Id` monad bind generated by ordinary `do`
notation.  Other monads may call their continuation zero, one, or many times,
so they require a separate contract. -/
private partial def analyzeIdentityBind (context : ReaderContext)
    (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  if arguments.isEmpty || !isIdentityMonad arguments[0]! then
    return SourceAnalysis.unresolved name "unsupported-monadic-bind"
      "only single-shot Id.bind is inferred automatically; this monad needs a bind cost contract"
  let explicit := explicitArguments info.type arguments
  if explicit.size != 2 then
    return SourceAnalysis.unresolved name "malformed-monadic-bind"
      s!"expected an action and continuation, found {explicit.size} explicit arguments"
  let action ← analyzeExpr context explicit[0]!
  let continuation ← match explicit[1]! with
    | .fvar _ | .bvar _ =>
        pure <| SourceAnalysis.unresolved context.root "unknown-bind-continuation"
          "bind continuation is supplied at runtime"
    | callback => analyzeCallableBody context callback
  let result := action.sequential continuation |>.charge (.constant 1) |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      monadicBinds := result.stats.monadicBinds + 1 } }

private partial def analyzeIdentityPure (context : ReaderContext)
    (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  if arguments.isEmpty || !isIdentityMonad arguments[0]! then
    return SourceAnalysis.unresolved name "unsupported-monadic-pure"
      "only Id.pure is inferred automatically; this monad needs a pure cost contract"
  let explicit := explicitArguments info.type arguments
  if explicit.size != 1 then
    return SourceAnalysis.unresolved name "malformed-monadic-pure"
      s!"expected one returned value, found {explicit.size} explicit arguments"
  let result := (← analyzeExpr context explicit[0]!).charge (.constant 1) |>.withNode
  return { result with
    stats := { result.stats with applications := result.stats.applications + 1 } }

/-- Analyze scalar `base ^ exponent` when the exponent is natural.  Its
runtime work is bounded by the exponent; the magnitude of the result is
handled separately when the expression is later used as a loop bound. -/
private partial def analyzeNaturalExponentPower (context : ReaderContext)
    (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  let explicit := explicitArguments info.type arguments
  if explicit.size != 2 then
    return SourceAnalysis.unresolved name "malformed-natural-power"
      s!"expected base and natural exponent, found {explicit.size} explicit arguments"
  let argumentAnalyses ← explicit.mapM (analyzeExpr context)
  let exponentCost ← inferNaturalGrowthM explicit[1]!
  let audit :=
    if exponentCost == .unknown then
      SourceAnalysis.auditIssue name "unknown-power-exponent"
        "could not derive a symbolic upper bound for the natural exponent"
    else SourceAnalysis.zero
  let result := (combineSequential argumentAnalyses).sequential audit
    |>.charge exponentCost |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      primitiveCalls := result.stats.primitiveCalls + 1
      boundedLoops := result.stats.boundedLoops + 1 }
    primitives := result.primitives.push name }

/-- Analyze ordinary `for x in xs` syntax when Lean selected a known finite
container instance and the surrounding monad is `Id`.  Early termination only
reduces the number of callback invocations; the worst-case count is inferred
from the actual collection expression. -/
private partial def analyzeFiniteForIn (context : ReaderContext)
    (name : Name) (info : ConstantInfo)
    (arguments : Array Expr) : MetaM SourceAnalysis := do
  if arguments.size < 2 || !isIdentityMonad arguments[0]! then
    return SourceAnalysis.unresolved name "unsupported-for-monad"
      "automatic for-loop analysis currently requires the single-shot Id monad"
  if !isApprovedFiniteCollectionType arguments[1]! ||
      !hasApprovedFiniteForInstance arguments then
    return SourceAnalysis.unresolved name "unverified-for-instance"
      "the ForIn instance is not one of the audited finite container traversals"
  let explicit := explicitArguments info.type arguments
  if explicit.size < 3 then
    return SourceAnalysis.unresolved name "malformed-for-loop"
      s!"expected collection, initial state, and body, found {explicit.size} explicit arguments"
  let collection := explicit[explicit.size - 3]!
  let initial := explicit[explicit.size - 2]!
  let callback := explicit[explicit.size - 1]!
  let collectionAnalysis ← analyzeExpr context collection
  let initialAnalysis ← analyzeExpr context initial
  let callbackAnalysis ← match callback with
    | .fvar _ | .bvar _ =>
        pure <| SourceAnalysis.unresolved context.root "unknown-for-body"
          "for-loop body is supplied at runtime; provide a uniform callback contract"
    | callback => analyzeCallableBody context callback
  let callbackAudit : SourceAnalysis := { callbackAnalysis with cost := .constant 0 }
  let iterationBound ← inferCollectionGrowthM collection
  let boundAudit :=
    if iterationBound == .unknown then
      SourceAnalysis.auditIssue name "unknown-for-bound"
        "could not derive a finite symbolic cardinality bound for the for-loop collection"
    else SourceAnalysis.zero
  let loop : SourceAnalysis := {
    cost := .mul iterationBound (.add callbackAnalysis.cost (.constant 1))
    stats := {} }
  let result := collectionAnalysis.sequential initialAnalysis
    |>.sequential callbackAudit |>.sequential boundAudit
    |>.sequential loop |>.withNode
  return { result with
    stats := { result.stats with
      applications := result.stats.applications + 1
      primitiveCalls := result.stats.primitiveCalls + 1
      boundedLoops := result.stats.boundedLoops + 1 }
    primitives := result.primitives.push name }

private partial def analyzeConstantCall (context : ReaderContext)
    (name : Name) (arguments : Array Expr) : MetaM SourceAnalysis := do
  if isConditionalName name then
    return ← analyzeConditional context name arguments
  let env ← getEnv
  let info ← getConstInfo name
  if isForInName name then
    return ← analyzeFiniteForIn context name info arguments
  if isMonadicBindName name then
    return ← analyzeIdentityBind context name info arguments
  if isMonadicPureName name then
    return ← analyzeIdentityPure context name info arguments
  if isApprovedNaturalExponentPower name arguments then
    return ← analyzeNaturalExponentPower context name info arguments
  if isCourseOfValuesRecursorName name then
    return ← analyzeCourseOfValuesRecursor context name info arguments
  if name.toString.endsWith ".casesOn" then
    match info with
    | .recInfo recursor =>
        return ← analyzeCasesRecursor context name recursor arguments
    | _ =>
        return ← analyzeCasesWrapper context name info arguments
  let explicit := explicitArguments info.type arguments
  let argumentAnalyses ← explicit.mapM (analyzeExpr context)
  let argumentsResult := combineSequential argumentAnalyses
  if let some rule := registeredSourceCostRule? env name then
    return ← analyzeLibraryCall context name info arguments rule true
  if let some rule := libraryCostRule? name then
    return ← analyzeLibraryCall context name info arguments rule false
  if isZeroCostName name then
    let result := argumentsResult.withNode
    return { result with
      stats := { result.stats with
        applications := result.stats.applications + 1 } }
  if isPrimitiveName name || isApprovedOverloadedPrimitive name arguments then
    let result := argumentsResult.charge (.constant 1) |>.withNode
    return { result with
      stats := { result.stats with
        applications := result.stats.applications + 1
        primitiveCalls := result.stats.primitiveCalls + 1 }
      primitives := result.primitives.push name }
  if (overloadedPrimitiveTypeArity? name).isSome then
    let issue := SourceAnalysis.unresolved name "unapproved-overloaded-operation"
      s!"{name} is not using an audited standard scalar instance; inspect the implementation or supply a local cost contract"
    return argumentsResult.sequential issue
  if let some projection := env.getProjectionFnInfo? name then
    let projectionArity := projection.numParams + 1
    if projectionArity < arguments.size then
      let issue := SourceAnalysis.unresolved name "function-valued-projection"
        s!"{name} projects a function and immediately calls it; its runtime implementation needs a cost contract"
      return argumentsResult.sequential issue
    else
      let result := argumentsResult.charge (.constant 1) |>.withNode
      return { result with
        stats := { result.stats with
          applications := result.stats.applications + 1
          projectionCalls := result.stats.projectionCalls + 1 } }
  match info with
  | .ctorInfo _ =>
      let result := argumentsResult.charge (.constant 1) |>.withNode
      return { result with
        stats := { result.stats with
          applications := result.stats.applications + 1
          constructorCalls := result.stats.constructorCalls + 1 } }
  | .recInfo recursor =>
      return ← analyzeStructuralRecursor context name recursor arguments
  | .defnInfo definition =>
      if context.visiting.contains name then
        let issue := SourceAnalysis.unresolved name "recursive-call"
          s!"recursive cycle reached while expanding {name}; provide a recurrence or fuel bound"
        return argumentsResult.sequential issue
      -- Beta-reducing the transparent helper connects higher-order branch
      -- parameters to the concrete lambdas supplied at this call site.  Call
      -- arguments were already charged above; syntactic duplication here is
      -- conservative and therefore remains a valid source upper bound.
      let instantiatedBody := definition.value.beta arguments
      let bodyAnalysis ← analyzeExpr (context.descend name) instantiatedBody
      let result := argumentsResult.sequential bodyAnalysis |>.withNode
      return { result with
        stats := { result.stats with
          applications := result.stats.applications + 1
          expandedDefinitions := result.stats.expandedDefinitions + 1 }
        expanded := result.expanded.push name }
  | .thmInfo _ =>
      -- Proof terms are erased. Explicit computational arguments, if any,
      -- have already been conservatively charged.
      return argumentsResult.withNode
  | .opaqueInfo opaqueValue =>
      if context.visiting.contains name then
        let issue := SourceAnalysis.unresolved name "recursive-opaque-call"
          s!"recursive cycle reached while reading the stored body of {name}"
        return argumentsResult.sequential issue
      -- Opaque declarations are not reducible by the kernel, but Lean stores
      -- their bodies and uses computational opaque values for code generation.
      -- The source reader may inspect that stored body; this does not unfold
      -- the declaration in any theorem.
      let instantiatedBody := opaqueValue.value.beta arguments
      let bodyAnalysis ← analyzeExpr (context.descend name) instantiatedBody
      let result := argumentsResult.sequential bodyAnalysis |>.withNode
      return { result with
        stats := { result.stats with
          applications := result.stats.applications + 1
          expandedDefinitions := result.stats.expandedDefinitions + 1 }
        expanded := result.expanded.push name }
  | .axiomInfo _ =>
      let issue := SourceAnalysis.unresolved name "axiom-or-extern"
        s!"{name} has no inspectable implementation and needs a cost contract"
      return argumentsResult.sequential issue
  | .inductInfo _ | .quotInfo _ =>
      let issue := SourceAnalysis.unresolved name "non-executable-declaration"
        s!"{name} is not an executable definition"
      return argumentsResult.sequential issue

end

/-! ## Public metaprogram and command -/

/-- Read an ordinary declaration from the current Lean environment. -/
meta def analyzeDeclaration (declaration : Name) : MetaM SourceReport := do
  let info ← getConstInfo declaration
  match info with
  | .thmInfo _ =>
      let analysis := SourceAnalysis.unresolved declaration "proof-declaration"
        "the declaration is a theorem; proof terms are erased and are not RAM algorithms"
      return {
        declaration
        bodyAvailable := false
        analysis
        certifiedPolynomial := false
        degreeUpperBound := none }
  | _ => match info.value? (allowOpaque := true) with
  | none =>
      let analysis := SourceAnalysis.unresolved declaration "body-unavailable"
        "the declaration is axiomatic, inductive, or otherwise has no executable stored value"
      return {
        declaration
        bodyAvailable := false
        analysis
        certifiedPolynomial := false
        degreeUpperBound := none }
  | some body =>
      let context : ReaderContext := {
        root := declaration
        scopePrefix := declaration.getPrefix
        visiting := ({} : NameSet) |>.insert declaration }
      let analysis ← analyzeExpr context body
      return {
        declaration
        bodyAvailable := true
        analysis
        certifiedPolynomial := analysis.certified
        degreeUpperBound := analysis.cost.polynomialDegree? }

private def formatIssues (issues : Array SourceIssue) : String :=
  if issues.isEmpty then "none"
  else
    let unique := issues.foldl (init := #[]) fun result issue =>
      if result.any fun previous =>
          previous.declaration == issue.declaration &&
            previous.kind == issue.kind && previous.detail == issue.detail then
        result
      else result.push issue
    let shown := unique.extract 0 (min 30 unique.size)
    let lines := shown.toList.map fun issue =>
      s!"- [{issue.kind}] {issue.declaration}: {issue.detail}"
    let suffix :=
      if shown.size < unique.size then
        [s!"- ... {unique.size - shown.size} additional distinct issues omitted"]
      else []
    String.intercalate "\n" (lines ++ suffix)

private def formatNames (names : Array Name) : String :=
  let unique := names.foldl (init := #[]) fun result name =>
    if result.contains name then result else result.push name
  let shown := unique.extract 0 (min 30 unique.size)
  let body := String.intercalate ", " <| shown.toList.map toString
  if shown.size < unique.size then
    s!"#[{body}, ... {unique.size - shown.size} more]"
  else s!"#[{body}]"

/-- Normalize administrative zeroes introduced by compositional traversal.
This is presentation-only; certification uses the original expression. -/
private def simplifyForDisplay : GrowthExpr → GrowthExpr
  | .add left right =>
      match simplifyForDisplay left, simplifyForDisplay right with
      | .constant 0, right => right
      | left, .constant 0 => left
      | .constant left, .constant right => .constant (left + right)
      | left, right => .add left right
  | .mul left right =>
      match simplifyForDisplay left, simplifyForDisplay right with
      | .constant 1, right => right
      | left, .constant 1 => left
      | .constant left, .constant right => .constant (left * right)
      | left, right => .mul left right
  | .pow base exponent =>
      let base := simplifyForDisplay base
      if exponent == 0 then .constant 1
      else if exponent == 1 then base
      else .pow base exponent
  | .maximum left right =>
      let left := simplifyForDisplay left
      let right := simplifyForDisplay right
      if left == right then left
      else match left, right with
        | .constant left, .constant right => .constant (max left right)
        | left, right => .maximum left right
  | .logarithm base argument => .logarithm base (simplifyForDisplay argument)
  | expression => expression

private def parseRegisteredRule (kind : String)
    (parameters : Array ℕ) : Except String LibraryCostRule :=
  let exactlyOne (constructor : ℕ → LibraryCostRule) :=
    if parameters.size == 1 then .ok (constructor parameters[0]!)
    else .error s!"{kind} requires exactly one natural parameter"
  match kind with
  | "fixed" => exactlyOne .fixed
  | "logarithmic" =>
      if parameters.isEmpty then .ok .logarithmic
      else .error "logarithmic takes no parameters"
  | "linear" =>
      if parameters.isEmpty then .ok .linear
      else .error "linear takes no parameters"
  | "nlogn" =>
      if parameters.isEmpty then .ok .nLogN
      else .error "nlogn takes no parameters"
  | "polynomial" => exactlyOne .polynomial
  | "linear_callbacks" =>
      if parameters.isEmpty then .error "linear_callbacks needs at least one callback index"
      else .ok (.linearWithCallbacks parameters)
  | "nlogn_callbacks" =>
      if parameters.isEmpty then .error "nlogn_callbacks needs at least one callback index"
      else .ok (.nLogNWithCallbacks parameters)
  | "polynomial_callbacks" =>
      if parameters.size < 2 then
        .error "polynomial_callbacks needs a degree followed by callback indices"
      else
        .ok (.polynomialWithCallbacks parameters[0]!
          (parameters.extract 1 parameters.size))
  | _ => .error s!"unknown source cost rule '{kind}'"

syntax (name := sourceCostContractCommand)
  "source_cost_contract " ident " := " ident num* : command

/-- Add an explicit source-model contract for an opaque/foreign declaration.
Examples: `source_cost_contract solver := polynomial 3` and
`source_cost_contract traverse := linear_callbacks 0`.

This is a visible modeling assumption, recorded in every report that uses it;
it is not a replacement for the proof-backed `external` interface in
`AlgorithmCost`. -/
elab_rules : command
  | `(source_cost_contract $target:ident := $kind:ident $parameters:num*) => do
      let declaration ← resolveGlobalConstNoOverload target
      let values := parameters.map (·.getNat)
      let rule ← match parseRegisteredRule kind.getId.toString values with
        | .ok rule => pure rule
        | .error message => throwErrorAt kind message
      modifyEnv fun environment =>
        sourceContractExtension.addEntry environment { declaration, rule }

syntax (name := sourceCostCommand) "#source_cost " ident : command

syntax (name := guardSourceCostCommand)
  "#guard_source_cost " ident " := " ident : command

/-- Regression assertion for the three semantically distinct outcomes of the
source reader:

* `polynomial`: a complete syntax-level polynomial certificate;
* `nonpolynomial_bound`: a complete extracted bound rejected by the
  polynomial-expression checker (not a lower-bound theorem); and
* `unresolved`: at least one source-cost obligation is missing.
-/
elab_rules : command
  | `(#guard_source_cost $identifier:ident := $expected:ident) => do
      let declaration ← resolveGlobalConstNoOverload identifier
      let report ← liftTermElabM <| analyzeDeclaration declaration
      let mode := expected.getId.toString
      let accepted := match mode with
        | "polynomial" => report.certifiedPolynomial
        | "nonpolynomial_bound" =>
            report.analysis.issues.isEmpty &&
              !report.analysis.cost.isPolynomial
        | "unresolved" => !report.analysis.issues.isEmpty
        | _ => false
      if !#["polynomial", "nonpolynomial_bound", "unresolved"].contains mode then
        throwErrorAt expected
          "expected polynomial, nonpolynomial_bound, or unresolved"
      if !accepted then
        throwErrorAt identifier
          s!"source-cost guard expected {mode}, but obtained cost {report.analysis.cost.render}, polynomial={report.certifiedPolynomial}, issues={report.analysis.issues.size}"

/-- Inspect any ordinary Lean declaration and print its conservative symbolic
source cost.  The command always reports unresolved constructs explicitly. -/
elab_rules : command
  | `(#source_cost%$token $identifier:ident) => do
      let declaration ← resolveGlobalConstNoOverload identifier
      let report ← liftTermElabM <| analyzeDeclaration declaration
      let status :=
        if report.certifiedPolynomial && report.analysis.assumedContracts.isEmpty then
          "CERTIFIED-SYNTAX-POLYNOMIAL"
        else if report.certifiedPolynomial then
          "CONDITIONAL-SYNTAX-POLYNOMIAL"
        else if report.analysis.issues.isEmpty then
          "EXTRACTED-BOUND-NOT-POLYNOMIAL"
        else "NEEDS-CONTRACTS-OR-BOUNDS"
      let displayedCost := simplifyForDisplay report.analysis.cost
      let displayedCostText :=
        if 2000 < report.analysis.stats.expressionNodes then
          s!"<omitted: expression extracted from {report.analysis.stats.expressionNodes} source nodes; inspect the report programmatically>"
        else displayedCost.render
      logInfoAt token m!"source-cost report for {declaration}
status: {status}
body available: {report.bodyAvailable}
cost expression: {displayedCostText}
degree upper bound: {repr report.degreeUpperBound}
statistics: {repr report.analysis.stats}
expanded definitions: {formatNames report.analysis.expanded}
primitive calls: {formatNames report.analysis.primitives}
assumed source contracts: {formatNames report.analysis.assumedContracts}
issues:
{formatIssues report.analysis.issues}"

end EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity.SourceReader
