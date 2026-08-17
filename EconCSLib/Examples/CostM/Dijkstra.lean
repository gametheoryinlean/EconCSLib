/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Complexity

/-!
# Polynomial cost certificate for dense Dijkstra

This file tests the open-problem complexity API on the standard dense-graph
implementation of Dijkstra's algorithm.  For `n` vertices, every outer
iteration scans all vertices once to select the closest unvisited vertex and
once to relax outgoing edges.  There are exactly `n` outer iterations.

The graph is accessed as an adjacency matrix `weight u v`; `none` means that
the directed edge is absent.  Natural weights make nonnegativity part of the
type.  Distances use `Option ℕ`, with `none` representing infinity.

The local accounting convention is deliberately explicit:

* selecting one candidate is bounded by 6 primitive operations;
* relaxing one candidate is bounded by 8 primitive operations;
* `Cost.foldlList` additionally charges one loop-control operation per item;
* marking a vertex and dispatching the selected/nonselected branch cost one
  operation each; and
* constructing the initial dense distance/visited arrays costs `n + 1`.

The final theorem does not manually choose a polynomial coefficient or
exponent.  It links the instrumented implementation to an `AlgorithmShape`,
runs the executable static analyzer (`#eval` returns `true`), and obtains the
semantic `IsPolynomial` theorem from analyzer soundness.  A second regression
shape with exponential growth returns `false`.  A separate graph-theory
development would be needed to prove the usual shortest-path correctness
theorem.
-/

namespace EconCSLib.Examples.CostM.Dijkstra

open EconCSLib.OpenProblem
open EconCSLib.OpenProblem.UnitCostRAM
open EconCSLib.OpenProblem.UnitCostRAM.StaticComplexity

/-- A finite directed graph with nonnegative natural edge weights and a
distinguished source. -/
structure Instance where
  vertexCount : ℕ
  source : Fin vertexCount
  weight : Fin vertexCount → Fin vertexCount → Option ℕ

abbrev Vertex (problem : Instance) := Fin problem.vertexCount
abbrev Distances (problem : Instance) := Vertex problem → Option ℕ

/-- Mutable mathematical state of the dense Dijkstra loop. -/
structure State (problem : Instance) where
  distance : Distances problem
  visited : Finset (Vertex problem)

/-- All vertices in their canonical finite order. -/
def vertices (problem : Instance) : List (Vertex problem) :=
  List.ofFn id

/-- Initial source distance zero; every other distance is infinity. -/
def initialState (problem : Instance) : State problem where
  distance vertex := if vertex = problem.source then some 0 else none
  visited := ∅

/-- Decide whether `candidate` should replace the current best unvisited
vertex. -/
def chooseCloser (problem : Instance) (state : State problem)
    (current : Option (Vertex problem)) (candidate : Vertex problem) :
    Option (Vertex problem) :=
  if candidate ∈ state.visited then current
  else
    match state.distance candidate, current with
    | none, _ => current
    | some _, none => some candidate
    | some candidateDistance, some best =>
        match state.distance best with
        | none => some candidate
        | some bestDistance =>
            if candidateDistance < bestDistance then some candidate else current

/-- One selection scan.  The bound 6 covers membership, distance reads,
case/comparison work, and replacement of the current candidate. -/
def selectClosestCost (problem : Instance) (state : State problem) :
    Cost (Option (Vertex problem)) :=
  Cost.foldlList
    (fun current candidate =>
      ⟨chooseCloser problem state current candidate, 6⟩)
    (vertices problem) none

/-- Relax one outgoing edge from `chosen`. -/
def relaxOne (problem : Instance) (chosen target : Vertex problem)
    (distance : Distances problem) : Distances problem :=
  match distance chosen, problem.weight chosen target with
  | some chosenDistance, some edgeWeight =>
      let proposed := chosenDistance + edgeWeight
      match distance target with
      | none => Function.update distance target (some proposed)
      | some oldDistance =>
          if proposed < oldDistance then
            Function.update distance target (some proposed)
          else distance
  | _, _ => distance

/-- One relaxation scan.  The bound 8 covers matrix/distance reads, case
dispatch, addition, comparison, and a possible array update. -/
def relaxAllCost (problem : Instance) (chosen : Vertex problem)
    (distance : Distances problem) : Cost (Distances problem) :=
  Cost.foldlList
    (fun current target => ⟨relaxOne problem chosen target current, 8⟩)
    (vertices problem) distance

/-- One complete outer iteration. -/
def iterationCost (problem : Instance) (state : State problem) :
    Cost (State problem) :=
  let selected := selectClosestCost problem state
  match selected.value with
  | none => ⟨state, selected.ops + 1⟩
  | some chosen =>
      let marked : State problem :=
        { state with visited := insert chosen state.visited }
      let relaxed := relaxAllCost problem chosen marked.distance
      ⟨{ marked with distance := relaxed.value },
        selected.ops + 1 + relaxed.ops + 1⟩

/-- Dense Dijkstra run with `n` outer iterations. -/
def dijkstraCost (problem : Instance) : Cost (Distances problem) :=
  let initial : Cost (State problem) :=
    ⟨initialState problem, problem.vertexCount + 1⟩
  let finished := Cost.iterate problem.vertexCount
    (iterationCost problem) initial.value
  ⟨finished.value.distance, initial.ops + finished.ops⟩

/-- Mathematical function computed by the instrumented implementation. -/
def dijkstra (problem : Instance) : Distances problem :=
  (dijkstraCost problem).value

def dijkstraImplementation :
    CostedImplementation dijkstra where
  run := dijkstraCost
  correct := fun _ => rfl

theorem vertices_length (problem : Instance) :
    (vertices problem).length = problem.vertexCount := by
  simp [vertices]

theorem selectClosestCost_ops_le (problem : Instance)
    (state : State problem) :
    (selectClosestCost problem state).ops ≤ 7 * problem.vertexCount := by
  have h := Cost.ops_foldlList_le
    (fun (current : Option (Vertex problem)) (candidate : Vertex problem) =>
      ⟨chooseCloser problem state current candidate, 6⟩)
    (vertices problem) none 6 (by
      intro current candidate
      change 6 ≤ 6
      exact le_rfl)
  rw [vertices_length] at h
  unfold selectClosestCost
  omega

theorem relaxAllCost_ops_le (problem : Instance)
    (chosen : Vertex problem) (distance : Distances problem) :
    (relaxAllCost problem chosen distance).ops ≤
      9 * problem.vertexCount := by
  have h := Cost.ops_foldlList_le
    (fun (current : Distances problem) (target : Vertex problem) =>
      ⟨relaxOne problem chosen target current, 8⟩)
    (vertices problem) distance 8 (by
      intro current target
      change 8 ≤ 8
      exact le_rfl)
  rw [vertices_length] at h
  unfold relaxAllCost
  omega

theorem iterationCost_ops_le (problem : Instance) (state : State problem) :
    (iterationCost problem state).ops ≤
      16 * problem.vertexCount + 2 := by
  have hselect := selectClosestCost_ops_le problem state
  unfold iterationCost
  dsimp only
  split
  · change (selectClosestCost problem state).cost + 1 ≤ _
    change (selectClosestCost problem state).cost ≤ _ at hselect
    omega
  · rename_i chosen hchosen
    have hrelax := relaxAllCost_ops_le problem chosen
      ({ state with visited := insert chosen state.visited }).distance
    change (selectClosestCost problem state).cost + 1 +
      (relaxAllCost problem chosen state.distance).cost + 1 ≤ _
    change (selectClosestCost problem state).cost ≤ _ at hselect
    change (relaxAllCost problem chosen state.distance).cost ≤ _ at hrelax
    omega

/-- Static shape of one selection scan.  The analyzer itself multiplies the
six primitive operations by `n` iterations and adds one loop-control operation
per iteration. -/
def selectClosestShape : AlgorithmShape :=
  .repeat .inputSize (.primitive (ResourceProfile.timeOnly (.constant 6)))

/-- Static shape of one relaxation scan. -/
def relaxAllShape : AlgorithmShape :=
  .repeat .inputSize (.primitive (ResourceProfile.timeOnly (.constant 8)))

/-- Static shape of one outer Dijkstra iteration. -/
def iterationShape : AlgorithmShape :=
  .sequential selectClosestShape
    (.sequential
      (.primitive (ResourceProfile.timeOnly (.constant 2)))
      relaxAllShape)

/-- Complete static shape: initialize `n` cells, then perform `n` outer
iterations. -/
def dijkstraShape : AlgorithmShape :=
  .sequential
    (.primitive
      (ResourceProfile.timeOnly (.add .inputSize (.constant 1))))
    (.repeat .inputSize iterationShape)

/-- Initialization as an intrinsically analyzed primitive. -/
def dijkstraInitialAnalysis :
    AnalyzedComputation (fun problem : Instance => problem.vertexCount)
      (fun problem => State problem) :=
  AnalyzedComputation.primitive
    (fun problem : Instance =>
      (⟨initialState problem, problem.vertexCount + 1⟩ : Cost (State problem)))
    (.add .inputSize (.constant 1)) (by
      intro problem
      exact le_rfl)

/-- The complete dependent-state loop assembled with the intrinsic EDSL.
Its global cost/shape inequality is generated by `AnalyzedComputation.iterate`.
-/
def dijkstraStateAnalysis :
    AnalyzedComputation (fun problem : Instance => problem.vertexCount)
      (fun problem => State problem) :=
  AnalyzedComputation.iterate dijkstraInitialAnalysis
    (fun problem => problem.vertexCount) .inputSize
    (fun _ => le_rfl) iterationCost iterationShape (by
      intro problem state
      have bound := iterationCost_ops_le problem state
      simp only [iterationShape, selectClosestShape, relaxAllShape,
        AlgorithmShape.analyze, ResourceProfile.sequential,
        ResourceProfile.iterate, ResourceProfile.timeOnly,
        ResourceProfile.zero, GrowthExpr.eval]
      omega)

/-- Project the final distances using one unit-cost field-access primitive. -/
def dijkstraIntrinsicAnalysis :
    AnalyzedComputation (fun problem : Instance => problem.vertexCount)
      (fun problem => Distances problem) :=
  AnalyzedComputation.mapUnit dijkstraStateAnalysis
    (fun _ state => state.distance)

example : dijkstraIntrinsicAnalysis.decidePolynomialTime = true := by
  native_decide

/-- No global polynomial inequality is supplied here: the theorem follows
from the EDSL construction and the executable Boolean result. -/
theorem dijkstraIntrinsicAnalysis_isPolynomial :
    dijkstraIntrinsicAnalysis.implementation.IsPolynomial
      (fun problem => problem.vertexCount) :=
  dijkstraIntrinsicAnalysis.decidePolynomialTime_sound (by native_decide)

/-- Link the executable Dijkstra cost counter to its finite static shape.
This local inequality checks the instrumentation; it does not choose a
polynomial coefficient or exponent. -/
def dijkstraStaticAnalysis :
    StaticallyAnalyzedImplementation (function := dijkstra) where
  implementation := dijkstraImplementation
  sizeOf := fun problem => problem.vertexCount
  shape := dijkstraShape
  time_le := by
    intro problem
    have hloop := Cost.ops_iterate_le problem.vertexCount
      (16 * problem.vertexCount + 2) (iterationCost problem)
      (initialState problem) (iterationCost_ops_le problem)
    change problem.vertexCount + 1 +
      (Cost.iterate problem.vertexCount (iterationCost problem)
        (initialState problem)).ops ≤ _
    calc
      problem.vertexCount + 1 +
          (Cost.iterate problem.vertexCount (iterationCost problem)
            (initialState problem)).ops
        ≤ problem.vertexCount + 1 +
            problem.vertexCount * (16 * problem.vertexCount + 2 + 1) :=
          Nat.add_le_add_left hloop _
      _ = _ := by
        simp only [dijkstraShape, iterationShape, selectClosestShape,
          relaxAllShape, AlgorithmShape.analyze, ResourceProfile.sequential,
          ResourceProfile.iterate, ResourceProfile.timeOnly,
          ResourceProfile.zero, GrowthExpr.eval]
        ring

-- The requested executable answer for dense Dijkstra is `true`.
#eval dijkstraStaticAnalysis.decidePolynomialTime

example : dijkstraStaticAnalysis.decidePolynomialTime = true := by
  native_decide

/-- Regression test showing that the checker also returns `false`, rather
than accepting every program description. -/
def exponentialShape : AlgorithmShape :=
  .primitive (ResourceProfile.timeOnly .exponential)

#eval exponentialShape.decidePolynomialTime

example : exponentialShape.decidePolynomialTime = false := by
  native_decide

/-- The semantic polynomial-time theorem is now obtained from the executable
`true` result and the generic analyzer soundness theorem. -/
theorem dijkstraImplementation_isPolynomial :
    dijkstraImplementation.IsPolynomial (fun problem => problem.vertexCount) :=
  dijkstraStaticAnalysis.decidePolynomialTime_sound (by native_decide)

/-! ## Cost expression derived by reading executable program syntax -/

/-- One outer iteration exposed as a locally audited primitive.  The enclosing
loop is no longer repeated manually in a separate AlgorithmShape: it is part
of the executable StructuredProgram below. -/
def dijkstraIterationProgram :
    StructuredProgram (fun problem : Instance => problem.vertexCount)
      (fun problem => State problem) :=
  .external iterationCost
    (.add (.mul (.constant 16) .inputSize) (.constant 2))
    iterationCost_ops_le

/-- Executable Dijkstra control flow.  The analyzer reads this repeat
constructor and derives the multiplication by the vertex count itself. -/
def dijkstraProgram :
    StructuredProgram (fun problem : Instance => problem.vertexCount)
      (fun problem => State problem) :=
  .repeat (fun problem => problem.vertexCount) .inputSize
    (fun _ => le_rfl) dijkstraIterationProgram

/-- Complete dense Dijkstra algorithm in the single-source structured syntax:
initialization, executable loop, and final distance projection. -/
def dijkstraStructuredAlgorithm :
    StructuredAlgorithm (fun problem : Instance => problem.vertexCount)
      (fun problem => State problem) (fun problem => Distances problem) where
  initial problem :=
    ⟨initialState problem, problem.vertexCount + 1⟩
  initialBound := .add .inputSize (.constant 1)
  initial_le := fun _ => le_rfl
  body := dijkstraProgram
  finish := fun _ state => state.distance

/-- The new structured interpreter computes the same mathematical function as
the hand-instrumented dense Dijkstra implementation. -/
example : dijkstraStructuredAlgorithm.function = dijkstra := by
  funext problem
  rfl

-- The analyzer extracts a quadratic upper bound from the executable syntax.
#eval dijkstraStructuredAlgorithm.timeExpression
#eval dijkstraStructuredAlgorithm.report
#eval dijkstraStructuredAlgorithm.polynomialDegree?
#eval dijkstraStructuredAlgorithm.decidePolynomialTime

example : dijkstraStructuredAlgorithm.polynomialDegree? = some 2 := by
  native_decide

example : dijkstraStructuredAlgorithm.decidePolynomialTime = true := by
  native_decide

/-- Polynomial time now follows from reading the structured algorithm.  No
global Dijkstra cost inequality and no separately maintained shape are used. -/
theorem dijkstraStructuredAlgorithm_isPolynomial :
    dijkstraStructuredAlgorithm.implementation.IsPolynomial
      (fun problem => problem.vertexCount) :=
  dijkstraStructuredAlgorithm.decidePolynomialTime_sound (by native_decide)

end EconCSLib.Examples.CostM.Dijkstra
