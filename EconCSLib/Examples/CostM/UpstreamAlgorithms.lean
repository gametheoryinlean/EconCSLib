/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.SourceCost
import Mathlib

/-!
# Regression tests on algorithms from upstream Lean repositories

The definitions below either call the public implementation directly or are
small namespace-isolated copies of examples from the cited Apache-2.0
upstream sources.  They test the source-cost reader against genuine Lean
control-flow patterns rather than against cost expressions written by hand.

Sources checked locally:

* `leanprover/lean4`, including `Init.Data.Nat.Gcd`, list sorting, array
  quicksort, and the official NFM tutorial examples;
* `leanprover/cslib`, whose verified merge-sort development uses the same
  split/merge recursion as Lean's public `List.mergeSort` interface.
-/

namespace EconCSLib.Examples.CostM.UpstreamAlgorithms

/-! ## Direct upstream library algorithms -/

/-- Euclid's algorithm from `leanprover/lean4/src/Init/Data/Nat/Gcd.lean`. -/
def euclideanGCD (input : ℕ × ℕ) : ℕ :=
  Nat.gcd input.1 input.2

/-- Stable merge sort.  CSLib additionally proves sortedness and permutation
correctness for its explicitly timed version. -/
def stableMergeSort (values : List ℕ) : List ℕ :=
  values.mergeSort (fun left right ↦ left ≤ right)

/-- Standard insertion sort on lists. -/
def insertionSort (values : List ℕ) : List ℕ :=
  values.insertionSort (fun left right ↦ left ≤ right)

/-- In-place-style array quicksort interface from Lean's core library. -/
def arrayQuickSort (values : Array ℕ) : Array ℕ :=
  values.qsort (fun left right ↦ left < right)

/-- Tail-recursive list reversal. -/
def reverseList (values : List ℕ) : List ℕ :=
  values.reverse

/-- Cartesian-product enumeration; polynomial in the aggregate input size. -/
def cartesianProduct (input : List ℕ × List ℕ) : List (ℕ × ℕ) :=
  input.1.product input.2

/-- Enumeration of every sublist; its output already has exponential size. -/
def enumerateSublists (values : List ℕ) : List (List ℕ) :=
  values.sublists

/-- Enumeration of every permutation; its output has factorial size. -/
def enumeratePermutations (values : List ℕ) : List (List ℕ) :=
  values.permutations

/-! ## Official Lean tutorial control flow -/

/-- Fibonacci copied from
`leanprover/lean4/doc/examples/NFM2022/nfm7.lean`.  Lean elaborates this
equational definition through `Nat.brecOn`: the table of smaller results is
built once, so its generated course-of-values implementation is linear in
the unit-cost model rather than the exponential call tree of a literal
unstored recursive implementation. -/
def naiveFibonacci : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => naiveFibonacci (n + 1) + naiveFibonacci n

/-- Array traversal from
`leanprover/lean4/doc/examples/NFM2022/nfm8.lean`. -/
def arraySum (values : Array Int) : Int := Id.run do
  let mut total := 0
  for value in values do
    total := total + value
  return total

/-! ## Executable value checks -/

example : euclideanGCD (48, 18) = 6 := by native_decide
example : stableMergeSort [3, 1, 4, 1, 2] = [1, 1, 2, 3, 4] := by native_decide
example : insertionSort [3, 1, 4, 1, 2] = [1, 1, 2, 3, 4] := by native_decide
example : arrayQuickSort #[3, 1, 4, 1, 2] = #[1, 1, 2, 3, 4] := by native_decide
example : reverseList [1, 2, 3] = [3, 2, 1] := by native_decide
example : (cartesianProduct ([1, 2], [3, 4, 5])).length = 6 := by native_decide
example : (enumerateSublists [1, 2, 3]).length = 8 := by native_decide
example : (enumeratePermutations [1, 2, 3]).length = 6 := by native_decide
example : naiveFibonacci 10 = 89 := by native_decide
example : arraySum #[1, 2, 3, 4] = 10 := by native_decide

/-! ## Source-cost reports

The guard assertions are added after inspecting these reports, so a false
expectation cannot be hidden by changing the checker just to make this file
compile.
-/

#source_cost euclideanGCD
#source_cost stableMergeSort
#source_cost insertionSort
#source_cost arrayQuickSort
#source_cost reverseList
#source_cost cartesianProduct
#source_cost enumerateSublists
#source_cost enumeratePermutations
#source_cost naiveFibonacci
#source_cost arraySum

#guard_source_cost euclideanGCD := polynomial
#guard_source_cost stableMergeSort := polynomial
#guard_source_cost insertionSort := polynomial
#guard_source_cost arrayQuickSort := polynomial
#guard_source_cost reverseList := polynomial
#guard_source_cost cartesianProduct := polynomial
#guard_source_cost enumerateSublists := nonpolynomial_bound
#guard_source_cost enumeratePermutations := nonpolynomial_bound
#guard_source_cost naiveFibonacci := polynomial
#guard_source_cost arraySum := polynomial

end EconCSLib.Examples.CostM.UpstreamAlgorithms
