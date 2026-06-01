/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Myerson
import EconCSLib.Foundation.Argmax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort

/-!
# EconCSLib.MechanismDesign.Auction.Knapsack

Knapsack auctions in the single-parameter setting.

This file specializes `Auction.SingleParameterMechanism` to a standard
knapsack-auction environment:

* each agent `i` reports a scalar value in `U`
* agent `i` has public weight `w i`
* the mechanism chooses an allocation vector `x : I → U`
* the total weighted allocation must respect the capacity bound `W`

## Structure hierarchy

```
MechanismWithTransfers I (fun _ => U) (I → U) U   -- scalar reports and allocations
  └─ SingleParameterMechanism I U                 -- single-parameter transfer layer
       └─ KnapsackAuction I U                       -- public weights + total capacity
            └─ welfareMaximizingMechanism hW      -- Myerson-payment implementation
```

## Main definitions

* `KnapsackAuction` — a single-parameter mechanism with public weights and a
  total capacity bound
* `RespectsCapacity`, `IsFeasible` — feasibility predicates for `U`-valued
  allocations
* `BinaryAllocation`, `binaryToAllocation`, `binaryLoad`,
  `binaryRespectsCapacity` — `0/1` allocation profiles and their induced load
* `feasibleBinaryAllocations`, `binarySocialWelfare` — the finite feasible
  allocation space and its welfare objective
* `welfareMaximizer`, `maximalSocialWelfare` — a chosen welfare-maximizing
  feasible binary allocation and its objective value
* `welfareMaximizingAllocationRule`, `welfareMaximizingPaymentRule`,
  `welfareMaximizingMechanism` — the induced single-parameter mechanism with
  Myerson payments
* `dpSolveList`, `dynamicProgrammingOptimalAllocation`,
  `dynamicProgrammingOptimalValue` — a dynamic-programming solver for the
  natural-number `0/1` knapsack specialization

## Main proofs

* existence of a welfare-maximizing feasible binary allocation
* monotonicity of the welfare-maximizing allocation rule
* DSIC of the welfare-maximizing mechanism via
  `SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone`
* correctness of the dynamic-programming solver in the natural-number setting:
  `dynamicProgrammingOptimalAllocation_feasible` proves the DP output
  satisfies the capacity constraint, and
  `dynamicProgrammingOptimalAllocation_optimal` proves it maximizes social
  welfare among all feasible binary allocations
-/

open scoped BigOperators

/-- A knapsack auction with public weights `w i` and total capacity `W`.

The underlying strategic object is a `SingleParameterMechanism I U`, where the
value type `U` is a linearly ordered field (`[Field U] [LinearOrder U]
[IsStrictOrderedRing U]`; e.g. `ℚ`, `ℝ`): each agent reports a single scalar
value in `U`, receives an allocation level `xᵢ ∈ U`, and makes a `U`-valued
payment. The pointwise allocation bounds are inherited from
`SingleParameterMechanism.IsAllocFeasible`; the knapsack constraint is recorded
separately below. -/
structure KnapsackAuction (I : Type*) (U : Type*)
    extends SingleParameterMechanism I U where
  /-- Public weight / size of agent `i` in the knapsack constraint. -/
  weight : I → U
  /-- Total knapsack capacity. -/
  totalCapacity : U

namespace KnapsackAuction

variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U]

/-- The allocation rule respects the knapsack capacity constraint. -/
def RespectsCapacity [Fintype I] (A : KnapsackAuction I U) : Prop :=
  ∀ b : I → U, (∑ i, A.weight i * A.allocationRule b i) ≤ A.totalCapacity

/-- Feasibility for a knapsack auction:

* each agent's allocation lies in `[0,1]`
* the weighted allocation satisfies the total capacity bound -/
def IsFeasible [Fintype I] (A : KnapsackAuction I U) : Prop :=
  A.IsAllocFeasible ∧ A.RespectsCapacity

/-- Agent `i`'s public weight. -/
abbrev size (A : KnapsackAuction I U) (i : I) : U :=
  A.weight i

/-- The total capacity bound. -/
abbrev capacity (A : KnapsackAuction I U) : U :=
  A.totalCapacity

/-- Every public weight is nonnegative. -/
def NonnegativeWeights (A : KnapsackAuction I U) : Prop :=
  ∀ i, 0 ≤ A.weight i

/-- Every public weight is strictly positive. -/
def PositiveWeights (A : KnapsackAuction I U) : Prop :=
  ∀ i, 0 < A.weight i

/-- The knapsack capacity is nonnegative. -/
def NonnegativeCapacity (A : KnapsackAuction I U) : Prop :=
  0 ≤ A.totalCapacity

end KnapsackAuction

namespace KnapsackAuction

section BinaryAllocations

variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U]
variable [Fintype I] [DecidableEq I]

/-- A discrete knapsack allocation profile: each agent is either selected or not. -/
abbrev BinaryAllocation (I : Type*) := I → Bool

/-- The `0/1` allocation vector associated with a binary allocation profile. -/
def binaryToAllocation (x : BinaryAllocation I) : I → U :=
  fun i => if x i then 1 else 0

/-- The weighted load induced by a binary allocation profile. -/
def binaryLoad (A : KnapsackAuction I U) (x : BinaryAllocation I) : U :=
  ∑ i, A.weight i * binaryToAllocation x i

/-- Capacity feasibility for a binary allocation profile. -/
def binaryRespectsCapacity (A : KnapsackAuction I U) (x : BinaryAllocation I) : Prop :=
  A.binaryLoad x ≤ A.totalCapacity

/-- The finite list of binary allocations satisfying the knapsack constraint. -/
noncomputable def feasibleBinaryAllocations (A : KnapsackAuction I U) : List (BinaryAllocation I) := by
  classical
  exact ((Finset.univ : Finset (BinaryAllocation I)).filter fun x => A.binaryRespectsCapacity x).toList

/-- Social welfare of a binary allocation profile at valuation profile `b`. -/
def binarySocialWelfare (b : I → U) (x : BinaryAllocation I) : U :=
  ∑ i, b i * binaryToAllocation x i

omit [DecidableEq I] in
lemma zeroBinaryRespectsCapacity (A : KnapsackAuction I U) (hW : 0 ≤ A.totalCapacity) :
    A.binaryRespectsCapacity (fun _ => false) := by
  simp [binaryRespectsCapacity, binaryLoad, binaryToAllocation, hW]

lemma feasibleBinaryAllocations_nonempty (A : KnapsackAuction I U) (hW : 0 ≤ A.totalCapacity) :
    A.feasibleBinaryAllocations ≠ [] := by
  classical
  intro hnil
  have hmem : (fun _ : I => false) ∈ A.feasibleBinaryAllocations := by
    unfold feasibleBinaryAllocations
    simp [zeroBinaryRespectsCapacity (A := A) hW]
  rw [hnil] at hmem
  simp at hmem

/-- A welfare-maximizing feasible binary allocation, chosen using `List.argMaxOn`
on the finite space of feasible `0/1` allocations. -/
lemma exists_welfareMaximizer
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) :
    ∃ x : BinaryAllocation I,
      x ∈ A.feasibleBinaryAllocations ∧
        ∀ y ∈ A.feasibleBinaryAllocations,
          binarySocialWelfare b y ≤ binarySocialWelfare b x := by
  classical
  let xs := A.feasibleBinaryAllocations
  have hxs : xs ≠ [] := A.feasibleBinaryAllocations_nonempty hW
  cases h : xs with
  | nil =>
      exact False.elim (hxs h)
  | cons head tail =>
      obtain ⟨x, hxmem, hxmax⟩ := List.exists_argMax_on (binarySocialWelfare b) head tail
      refine ⟨x, ?_, ?_⟩
      · simpa [xs, h] using hxmem
      · intro y hy
        exact hxmax y (by simpa [xs, h] using hy)

noncomputable def welfareMaximizer
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) : BinaryAllocation I := by
  exact Classical.choose (A.exists_welfareMaximizer b hW)

/-- The maximal social welfare over the feasible binary allocation space. -/
noncomputable def maximalSocialWelfare
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) : U :=
  binarySocialWelfare b (A.welfareMaximizer b hW)

lemma welfareMaximizer_mem_feasibleBinaryAllocations
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) :
    A.welfareMaximizer b hW ∈ A.feasibleBinaryAllocations := by
  exact (Classical.choose_spec (A.exists_welfareMaximizer b hW)).1

lemma welfareMaximizer_ge
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity)
    {x : BinaryAllocation I}
    (hx : x ∈ A.feasibleBinaryAllocations) :
    binarySocialWelfare b x ≤ binarySocialWelfare b (A.welfareMaximizer b hW) := by
  exact (Classical.choose_spec (A.exists_welfareMaximizer b hW)).2 x hx

lemma binarySocialWelfare_update
    (b : I → U) (i : I) (θ : U) (x : BinaryAllocation I) :
    binarySocialWelfare (Function.update b i θ) x =
      θ * binaryToAllocation x i +
        Finset.sum (Finset.univ.erase i) (fun j => b j * binaryToAllocation x j) := by
  have hsum :
      Finset.sum (Finset.univ.erase i) (fun j => Function.update b i θ j * binaryToAllocation x j) =
        Finset.sum (Finset.univ.erase i) (fun j => b j * binaryToAllocation x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      simpa using hj
    simp [Function.update, hji]
  cases hxi : x i with
  | false =>
      rw [binarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsum]
      simp [Function.update, binaryToAllocation, hxi]
  | true =>
      rw [binarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      rw [hsum]
      simp [Function.update, binaryToAllocation, hxi]

end BinaryAllocations

section WelfareMaximizingMechanism

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The welfare-maximizing allocation rule for the knapsack auction, obtained by
choosing a feasible binary allocation with maximal social welfare and then
viewing it as an `I → ℝ` allocation vector. -/
noncomputable def welfareMaximizingAllocationRule
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : (I → ℝ) → I → ℝ :=
  fun b => binaryToAllocation (A.welfareMaximizer b hW)

/-- The Myerson payment formula associated with the welfare-maximizing knapsack
allocation rule. -/
noncomputable def welfareMaximizingPaymentRule
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : (I → ℝ) → I → ℝ :=
  SingleParameterMechanism.myersonPayment (A.welfareMaximizingAllocationRule hW)

/-- The canonical welfare-maximizing single-parameter knapsack mechanism, with
payments given by the Myerson formula. -/
noncomputable def welfareMaximizingMechanism
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) : SingleParameterMechanism I ℝ where
  allocationRule := A.welfareMaximizingAllocationRule hW
  paymentRule := A.welfareMaximizingPaymentRule hW

lemma welfareMaximizingAllocationRule_isMonotone
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) :
    SingleParameterMechanism.IsMonotone
      ({ allocationRule := A.welfareMaximizingAllocationRule hW
         paymentRule := A.welfareMaximizingPaymentRule hW } :
        SingleParameterMechanism I ℝ) := by
  intro i θ θ' hθ b
  by_cases hEq : θ = θ'
  · simp [welfareMaximizingAllocationRule, hEq]
  · have hlt : θ < θ' := lt_of_le_of_ne hθ hEq
    let bLo := Function.update b i θ
    let bHi := Function.update b i θ'
    let xLo := A.welfareMaximizer bLo hW
    let xHi := A.welfareMaximizer bHi hW
    have hxLo_feas : xLo ∈ A.feasibleBinaryAllocations := by
      exact A.welfareMaximizer_mem_feasibleBinaryAllocations bLo hW
    have hxHi_feas : xHi ∈ A.feasibleBinaryAllocations := by
      exact A.welfareMaximizer_mem_feasibleBinaryAllocations bHi hW
    have hLo :
        binarySocialWelfare bLo xHi ≤ binarySocialWelfare bLo xLo := by
      exact A.welfareMaximizer_ge bLo hW hxHi_feas
    have hHi :
        binarySocialWelfare bHi xLo ≤ binarySocialWelfare bHi xHi := by
      exact A.welfareMaximizer_ge bHi hW hxLo_feas
    by_cases hxLo_i : xLo i <;> by_cases hxHi_i : xHi i
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · exfalso
      have hLo' : binarySocialWelfare bLo xHi - binarySocialWelfare bLo xLo ≤ 0 := by
        linarith
      have hHi' : 0 ≤ binarySocialWelfare bHi xHi - binarySocialWelfare bHi xLo := by
        linarith
      have hHi_eq :
          binarySocialWelfare bHi xHi = binarySocialWelfare bLo xHi := by
        rw [binarySocialWelfare_update (b := b) (i := i) (θ := θ') (x := xHi),
          binarySocialWelfare_update (b := b) (i := i) (θ := θ) (x := xHi)]
        simp [binaryToAllocation, hxHi_i]
      have hLo_eq :
          binarySocialWelfare bHi xLo = binarySocialWelfare bLo xLo + (θ' - θ) := by
        rw [binarySocialWelfare_update (b := b) (i := i) (θ := θ') (x := xLo),
          binarySocialWelfare_update (b := b) (i := i) (θ := θ) (x := xLo)]
        simp [binaryToAllocation, hxLo_i]
        ring
      have : 0 < θ' - θ := sub_pos.mpr hlt
      rw [hHi_eq, hLo_eq] at hHi'
      linarith
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]
    · simp [welfareMaximizingAllocationRule, bLo, bHi, xLo, xHi, binaryToAllocation,
        hxLo_i, hxHi_i]

theorem welfareMaximizingMechanism_isDSIC
    (A : KnapsackAuction I ℝ) (hW : 0 ≤ A.totalCapacity) :
    (A.welfareMaximizingMechanism hW).IsDSIC := by
  simpa [welfareMaximizingMechanism, welfareMaximizingPaymentRule,
    welfareMaximizingAllocationRule] using
    (SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone
      (x := A.welfareMaximizingAllocationRule hW)
      (A.welfareMaximizingAllocationRule_isMonotone hW))

end WelfareMaximizingMechanism

section FractionalGreedy

variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U]
variable [Fintype I] [DecidableEq I] [LinearOrder I]

/-- Fractional social welfare for a `U`-valued allocation vector. -/
def fractionalSocialWelfare (b : I → U) (x : I → U) : U :=
  ∑ i, b i * x i

/-- Feasibility of a fractional knapsack allocation:
pointwise fractions lie in `[0,1]` and the weighted load respects capacity. -/
def fractionalFeasible (A : KnapsackAuction I U) (x : I → U) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    (∑ i, A.weight i * x i) ≤ A.totalCapacity

/-- Value-to-weight ratio used by the fractional greedy rule. -/
noncomputable def ratio (A : KnapsackAuction I U) (b : I → U) (i : I) : U :=
  b i / A.weight i

/-- Sorting key for the fractional greedy rule:
higher ratio first, ties broken by the ambient linear order on `I`. -/
noncomputable def ratioTieKey (A : KnapsackAuction I U) (b : I → U) (i : I) : U × I :=
  (-A.ratio b i, i)

/-- Agents sorted by decreasing value-to-weight ratio, with lexicographic
tie-breaking via the ambient order on `I`. -/
noncomputable def sortedAgentsByRatio (A : KnapsackAuction I U) (b : I → U) : List I :=
  by
    classical
    exact ((Finset.univ : Finset I).toList).mergeSort
      (fun i j => decide (A.ratioTieKey b i ≤ A.ratioTieKey b j))

/-- Greedy fractional allocation along a fixed list order. If the next item does
not fully fit, the algorithm takes exactly the remaining fraction and halts. -/
noncomputable def fractionalGreedyList (A : KnapsackAuction I U) (b : I → U) :
    List I → U → I → U
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if _ : remaining ≤ 0 then
        fun _ => 0
      else if _ : A.weight i ≤ remaining then
        Function.update (fractionalGreedyList A b items (remaining - A.weight i)) i 1
      else
        fun j => if j = i then remaining / A.weight i else 0
termination_by items _ => items.length

/-- The greedy fractional knapsack allocation obtained by sorting agents by
value-to-weight ratio and then filling capacity in that order. -/
noncomputable def fractionalGreedyAllocation
    (A : KnapsackAuction I U) (b : I → U) : I → U :=
  A.fractionalGreedyList b (A.sortedAgentsByRatio b) A.totalCapacity

omit [LinearOrder I] in
lemma BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations
    (A : KnapsackAuction I U) {x : BinaryAllocation I}
    (hx : x ∈ A.feasibleBinaryAllocations) :
    A.binaryRespectsCapacity x := by
  classical
  unfold feasibleBinaryAllocations at hx
  simp at hx
  exact hx

omit [DecidableEq I] [LinearOrder I] in
lemma binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
    (A : KnapsackAuction I U) {x : BinaryAllocation I}
    (hx : A.binaryRespectsCapacity x) :
    A.fractionalFeasible (binaryToAllocation x) := by
  constructor
  · intro i
    by_cases hxi : x i <;> simp [binaryToAllocation, hxi]
  · simpa [binaryRespectsCapacity, binaryLoad, binaryToAllocation] using hx

/-- If the ratio-sorted greedy fractional allocation is optimal for the
fractional relaxation, then its welfare dominates the welfare of the optimal
`0/1` knapsack allocation. This is the standard relaxation comparison:
every feasible binary allocation is also a feasible fractional allocation. -/
theorem fractionalGreedyWelfare_ge_zeroOneWelfare_of_optimal
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity)
    (hgreedyOptimal :
      ∀ x : I → U, A.fractionalFeasible x →
        fractionalSocialWelfare b x ≤
          fractionalSocialWelfare b (A.fractionalGreedyAllocation b)) :
    A.maximalSocialWelfare b hW ≤
      fractionalSocialWelfare b (A.fractionalGreedyAllocation b) := by
  let xStar := A.welfareMaximizer b hW
  have hxStarFeas : A.fractionalFeasible (binaryToAllocation xStar) := by
    exact A.binaryToAllocation_fractionalFeasible_of_binaryRespectsCapacity
      (A.BinaryRespectsCapacity_of_mem_feasibleBinaryAllocations
        (A.welfareMaximizer_mem_feasibleBinaryAllocations b hW))
  calc
    A.maximalSocialWelfare b hW
        = fractionalSocialWelfare b (binaryToAllocation xStar) := by
          simp [maximalSocialWelfare, fractionalSocialWelfare, xStar, binarySocialWelfare]
    _ ≤ fractionalSocialWelfare b (A.fractionalGreedyAllocation b) := by
      exact hgreedyOptimal _ hxStarFeas

end FractionalGreedy

section DynamicProgramming

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Integer-valued welfare of a binary allocation profile. -/
def natBinarySocialWelfare (b : I → Nat) (x : BinaryAllocation I) : Nat :=
  ∑ i, if x i then b i else 0

/-- Integer-valued load of a binary allocation profile. -/
def natBinaryLoad (w : I → Nat) (x : BinaryAllocation I) : Nat :=
  ∑ i, if x i then w i else 0

/-- An allocation is supported on a list of agents if every selected agent
appears in that list. -/
def supportedOn (items : List I) (x : BinaryAllocation I) : Prop :=
  ∀ i, x i = true → i ∈ items

omit [Fintype I] [DecidableEq I] in
lemma eq_false_of_supportedOn_of_not_mem
    {items : List I} {x : BinaryAllocation I}
    (hsupp : supportedOn items x) {i : I} (hi : i ∉ items) :
    x i = false := by
  cases hxi : x i with
  | false => rfl
  | true => exact False.elim (hi (hsupp i hxi))

omit [Fintype I] [DecidableEq I] in
lemma supportedOn_nil_iff {x : BinaryAllocation I} :
    supportedOn ([] : List I) x ↔ x = fun _ => false := by
  constructor
  · intro hsupp
    funext i
    exact eq_false_of_supportedOn_of_not_mem hsupp (by simp)
  · intro hx i hi
    simp [hx] at hi

omit [Fintype I] [DecidableEq I] in
lemma supportedOn_tail_of_eq_false
    {i : I} {items : List I} {x : BinaryAllocation I}
    (hsupp : supportedOn (i :: items) x) (hxi : x i = false) :
    supportedOn items x := by
  intro j hj
  have hjmem : j ∈ i :: items := hsupp j hj
  rcases List.mem_cons.mp hjmem with rfl | hjtail
  · simp [hxi] at hj
  · exact hjtail

omit [Fintype I] in
lemma supportedOn_update_false
    {i : I} {items : List I} {x : BinaryAllocation I}
    (hsupp : supportedOn (i :: items) x) :
    supportedOn items (Function.update x i false) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    simp at hj
  · have hxj : x j = true := by simpa [Function.update, hji] using hj
    have hjmem : j ∈ i :: items := hsupp j hxj
    rcases List.mem_cons.mp hjmem with rfl | hjtail
    · exact False.elim (hji rfl)
    · exact hjtail

lemma natBinarySocialWelfare_eq_add_of_true
    (b : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = true) :
    natBinarySocialWelfare b x =
      b i + natBinarySocialWelfare b (Function.update x i false) := by
  have htail :
      natBinarySocialWelfare b (Function.update x i false) =
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then b j else 0) := by
    rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i false j = true then b j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if x j = true then b j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [Function.update] using hs
  rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [hxi]

lemma natBinaryLoad_eq_add_of_true
    (w : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = true) :
    natBinaryLoad w x =
      w i + natBinaryLoad w (Function.update x i false) := by
  have htail :
      natBinaryLoad w (Function.update x i false) =
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
    rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i false j = true then w j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [Function.update] using hs
  rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [hxi]

lemma natBinarySocialWelfare_update_true_of_false
    (b : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = false) :
    natBinarySocialWelfare b (Function.update x i true) =
      b i + natBinarySocialWelfare b x := by
  have htail :
      natBinarySocialWelfare b x =
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then b j else 0) := by
    rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then b j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then b j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [hxi] using hs
  rw [natBinarySocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [Function.update]

lemma natBinaryLoad_update_true_of_false
    (w : I → Nat) {x : BinaryAllocation I} {i : I}
    (hxi : x i = false) :
    natBinaryLoad w (Function.update x i true) =
      w i + natBinaryLoad w x := by
  have htail :
      natBinaryLoad w x =
        Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then w j else 0) := by
    rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hs :
        Finset.sum (Finset.univ.erase i) (fun j => if x j = true then w j else 0) =
          Finset.sum (Finset.univ.erase i) (fun j => if Function.update x i true j = true then w j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by simpa using hj
      simp [Function.update, hji]
    simpa [hxi] using hs
  rw [natBinaryLoad, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [htail]
  simp [Function.update]

/-- A computable dynamic-programming solver for finite `0/1` knapsack instances.

The solver processes the agents in the given list order and uses the standard
"skip or take" recursion on the remaining capacity. This is the algorithmic
counterpart to the abstract welfare-maximizer above, specialized to natural
weights, natural capacity, and natural reported values. -/
def dpSolveList (w b : I → Nat) : List I → Nat → BinaryAllocation I
  | [], _ => fun _ => false
  | i :: is, capacity =>
      if w i ≤ capacity then
        let skip := dpSolveList w b is capacity
        let takeTail := dpSolveList w b is (capacity - w i)
        let take := Function.update takeTail i true
        if natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip then
          take
        else
          skip
      else
        dpSolveList w b is capacity
termination_by items _ => items.length

lemma dpSolveList_supportedOn (w b : I → Nat) :
    ∀ items capacity, supportedOn items (dpSolveList w b items capacity) := by
  intro items
  induction items with
  | nil =>
      intro capacity i hi
      simp [dpSolveList] at hi
  | cons i items ih =>
      intro capacity
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w b items capacity
        let takeTail := dpSolveList w b items (capacity - w i)
        let take := Function.update takeTail i true
        by_cases hchoose : natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          intro j hj
          by_cases hji : j = i
          · subst hji
            simp
          · exact List.mem_cons.2 (.inr (ih (capacity - w i) j (by simpa [take, Function.update, hji] using hj)))
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          intro j hj
          exact List.mem_cons.2 (.inr (ih capacity j hj))
      · intro j hj
        have hj' : dpSolveList w b items capacity j = true := by
          simpa [dpSolveList, hwi] using hj
        exact List.mem_cons.2 (.inr ((ih capacity) j hj'))

lemma dpSolveList_feasible (w b : I → Nat) :
    ∀ items, items.Nodup → ∀ capacity,
      natBinaryLoad w (dpSolveList w b items capacity) ≤ capacity := by
  intro items hnodup
  induction hnodup with
  | nil =>
      intro capacity
      simp [dpSolveList, natBinaryLoad]
  | @cons i items hnotmem hnodup ih =>
      intro capacity
      have hi_not_mem : i ∉ items := by
        intro hi
        exact (hnotmem i hi) rfl
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w b items capacity
        let takeTail := dpSolveList w b items (capacity - w i)
        let take := Function.update takeTail i true
        have htail : natBinaryLoad w takeTail ≤ capacity - w i := ih (capacity - w i)
        have htakeTailFalse : takeTail i = false := by
          exact eq_false_of_supportedOn_of_not_mem
            (dpSolveList_supportedOn w b items (capacity - w i)) hi_not_mem
        by_cases hchoose : natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          rw [natBinaryLoad_update_true_of_false w htakeTailFalse]
          calc
            w i + natBinaryLoad w takeTail ≤ w i + (capacity - w i) := Nat.add_le_add_left htail _
            _ = capacity := Nat.add_sub_of_le hwi
        · simp [dpSolveList, hwi, skip, takeTail, take, hchoose]
          exact ih capacity
      · simpa [dpSolveList, hwi] using ih capacity

lemma dpSolveList_optimal (w b : I → Nat) :
    ∀ (items : List I), items.Nodup → ∀ capacity {x : BinaryAllocation I},
      supportedOn items x →
      natBinaryLoad w x ≤ capacity →
        natBinarySocialWelfare b x ≤ natBinarySocialWelfare b (dpSolveList w b items capacity) := by
  intro items hnodup
  induction hnodup with
  | nil =>
      intro capacity x hsupp hload
      rw [(supportedOn_nil_iff.mp hsupp)]
      simp [dpSolveList, natBinarySocialWelfare]
  | @cons i items hnotmem hnodup ih =>
      intro capacity x hsupp hload
      have hi_not_mem : i ∉ items := by
        intro hi
        exact (hnotmem i hi) rfl
      by_cases hwi : w i ≤ capacity
      · let skip := dpSolveList w b items capacity
        let takeTail := dpSolveList w b items (capacity - w i)
        let take := Function.update takeTail i true
        by_cases hxi : x i = true
        · have hsuppTail : supportedOn items (Function.update x i false) :=
            supportedOn_update_false hsupp
          have hloadTail : natBinaryLoad w (Function.update x i false) ≤ capacity - w i := by
            rw [natBinaryLoad_eq_add_of_true w hxi] at hload
            exact (Nat.le_sub_iff_add_le hwi).2 (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hload)
          have hoptTail :
              natBinarySocialWelfare b (Function.update x i false) ≤
                natBinarySocialWelfare b takeTail :=
            ih (capacity - w i) hsuppTail hloadTail
          have htakeTailFalse : takeTail i = false := by
            exact eq_false_of_supportedOn_of_not_mem
              (dpSolveList_supportedOn w b items (capacity - w i)) hi_not_mem
          have hx :
              natBinarySocialWelfare b x ≤ natBinarySocialWelfare b take := by
            rw [natBinarySocialWelfare_eq_add_of_true b hxi,
              natBinarySocialWelfare_update_true_of_false b htakeTailFalse]
            exact Nat.add_le_add_left hoptTail (b i)
          by_cases hchoose : natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip
          · simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hx
          · have htake_le_skip : natBinarySocialWelfare b take ≤ natBinarySocialWelfare b skip :=
              le_of_not_ge hchoose
            exact le_trans hx (by simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using htake_le_skip)
        · have hxiFalse : x i = false := by
            cases hxib : x i with
            | false => rfl
            | true => exact False.elim (hxi hxib)
          have hsuppSkip : supportedOn items x :=
            supportedOn_tail_of_eq_false hsupp hxiFalse
          have hskip :
              natBinarySocialWelfare b x ≤ natBinarySocialWelfare b skip :=
            ih capacity hsuppSkip hload
          by_cases hchoose : natBinarySocialWelfare b take ≥ natBinarySocialWelfare b skip
          · exact
              (by
                simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using
                  (le_trans hskip hchoose))
          · simpa [dpSolveList, hwi, skip, takeTail, take, hchoose] using hskip
      · have hxiFalse : x i = false := by
          by_cases hxi : x i = true
          · have hwi' : w i ≤ natBinaryLoad w x := by
              rw [natBinaryLoad_eq_add_of_true w hxi]
              exact Nat.le_add_right _ _
            exact False.elim (hwi (le_trans hwi' hload))
          · cases hxib : x i with
            | false => rfl
            | true => exact False.elim (hxi hxib)
        have hsuppTail : supportedOn items x := supportedOn_tail_of_eq_false hsupp hxiFalse
        simpa [dpSolveList, hwi] using ih capacity hsuppTail hload

/-- The computable knapsack allocation obtained by running the dynamic program on
the full finite agent list. -/
noncomputable def dynamicProgrammingOptimalAllocation
    (w b : I → Nat) (capacity : Nat) : BinaryAllocation I :=
  dpSolveList w b ((Finset.univ : Finset I).toList) capacity

/-- The social welfare achieved by the dynamic-programming allocation. -/
noncomputable def dynamicProgrammingOptimalValue
    (w b : I → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare b (dynamicProgrammingOptimalAllocation w b capacity)

/-- The dynamic-programming allocation always satisfies the knapsack capacity
constraint in the natural-number specialization. -/
theorem dynamicProgrammingOptimalAllocation_feasible
    (w b : I → Nat) (capacity : Nat) :
    natBinaryLoad w (dynamicProgrammingOptimalAllocation w b capacity) ≤ capacity := by
  classical
  exact
    (by
      simpa [dynamicProgrammingOptimalAllocation] using
        (dpSolveList_feasible (w := w) (b := b)
          ((Finset.univ : Finset I).toList)
          (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset I))))
          capacity))

/-- The dynamic-programming allocation maximizes integer social welfare among
all feasible binary allocations. -/
theorem dynamicProgrammingOptimalAllocation_optimal
    (w b : I → Nat) (capacity : Nat) {x : BinaryAllocation I}
    (hfeas : natBinaryLoad w x ≤ capacity) :
    natBinarySocialWelfare b x ≤
      natBinarySocialWelfare b (dynamicProgrammingOptimalAllocation w b capacity) := by
  classical
  exact
    (by
      simpa [dynamicProgrammingOptimalAllocation] using
        (dpSolveList_optimal (w := w) (b := b)
          ((Finset.univ : Finset I).toList)
          (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset I))))
          capacity
          (x := x)
          (by intro i hi; exact Finset.mem_toList.mpr (Finset.mem_univ i))
          hfeas))

end DynamicProgramming

section GreedyApproximation

variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I]

/-- The knapsack-auction data obtained from natural-number weights and capacity,
with dummy zero allocation/payment rules. This is only used to instantiate the
fractional greedy construction. -/
def natAuctionData (w : I → Nat) (capacity : Nat) : KnapsackAuction I ℝ where
  allocationRule := fun _ _ => 0
  paymentRule := fun _ _ => 0
  weight := fun i => (w i : ℝ)
  totalCapacity := capacity

/-- Natural-number bids viewed as real-valued bids. -/
def realBidOfNat (b : I → Nat) : I → ℝ :=
  fun i => (b i : ℝ)

/-- The integral greedy prefix algorithm: process items in a fixed order,
take each whole item if it fits, and halt when the first item fails to fit. -/
def integralGreedyList (w : I → Nat) : List I → Nat → BinaryAllocation I
  | [], _ => fun _ => false
  | i :: items, remaining =>
      if w i ≤ remaining then
        Function.update (integralGreedyList w items (remaining - w i)) i true
      else
        fun _ => false
termination_by items _ => items.length

/-- The ratio-sorted integral greedy allocation. -/
noncomputable def integralGreedyAllocation (w b : I → Nat) (capacity : Nat) : BinaryAllocation I :=
  integralGreedyList w ((natAuctionData w capacity).sortedAgentsByRatio (realBidOfNat b)) capacity

/-- Welfare of the ratio-sorted integral greedy allocation. -/
noncomputable def integralGreedyValue (w b : I → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare b (integralGreedyAllocation w b capacity)

/-- Highest single-item value. -/
noncomputable def highestBidValue (b : I → Nat) : Nat :=
  Finset.sup' Finset.univ Finset.univ_nonempty b

omit [DecidableEq I] [LinearOrder I] in
lemma le_highestBidValue (b : I → Nat) (i : I) :
    b i ≤ highestBidValue b := by
  classical
  exact Finset.le_sup' (s := Finset.univ) (f := b) (by simp)

omit [DecidableEq I] [LinearOrder I] [Nonempty I] in
lemma fractionalSocialWelfare_realBidOfNat_binaryToAllocation
    (b : I → Nat) (x : BinaryAllocation I) :
    fractionalSocialWelfare (realBidOfNat b) (binaryToAllocation x) =
      natBinarySocialWelfare b x := by
  simp [fractionalSocialWelfare, realBidOfNat, binaryToAllocation, natBinarySocialWelfare]

/-- Fractional greedy prefix algorithm on a natural-number remaining capacity:
take each whole item if it fits, and otherwise take exactly the remaining
fraction of the current item and halt. -/
noncomputable def natFractionalGreedyList (w : I → Nat) : List I → Nat → I → ℝ
  | [], _ => fun _ => 0
  | i :: items, remaining =>
      if _ : w i ≤ remaining then
        Function.update (natFractionalGreedyList w items (remaining - w i)) i 1
      else
        fun j => if j = i then (remaining : ℝ) / w i else 0
termination_by items _ => items.length

/-- The ratio-sorted fractional greedy allocation on natural-number data. -/
noncomputable def natFractionalGreedyAllocation (w b : I → Nat) (capacity : Nat) : I → ℝ :=
  natFractionalGreedyList w ((natAuctionData w capacity).sortedAgentsByRatio (realBidOfNat b)) capacity

/-- Welfare of the ratio-sorted fractional greedy allocation. -/
noncomputable def natFractionalGreedyValue (w b : I → Nat) (capacity : Nat) : ℝ :=
  fractionalSocialWelfare (realBidOfNat b) (natFractionalGreedyAllocation w b capacity)

/-- A real-valued allocation is supported on a list if every nonzero coordinate
appears in that list. -/
def fractionalSupportedOn (items : List I) (x : I → ℝ) : Prop :=
  ∀ i, x i ≠ 0 → i ∈ items

omit [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
lemma eq_zero_of_fractionalSupportedOn_of_not_mem
    {items : List I} {x : I → ℝ}
    (hsupp : fractionalSupportedOn items x) {i : I} (hi : i ∉ items) :
    x i = 0 := by
  by_contra hxi
  exact hi (hsupp i hxi)

omit [Fintype I] [LinearOrder I] [Nonempty I] in
lemma integralGreedyList_supportedOn (w : I → Nat) :
    ∀ items remaining, supportedOn items (integralGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [integralGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : integralGreedyList w items (remaining - w i) j = true := by
            simpa [integralGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · simp [integralGreedyList, hfit] at hj

omit [Fintype I] [LinearOrder I] [Nonempty I] in
lemma natFractionalGreedyList_supportedOn (w : I → Nat) :
    ∀ items remaining,
      fractionalSupportedOn items (natFractionalGreedyList w items remaining) := by
  intro items
  induction items with
  | nil =>
      intro remaining i hi
      simp [natFractionalGreedyList] at hi
  | cons i items ih =>
      intro remaining j hj
      by_cases hfit : w i ≤ remaining
      · by_cases hji : j = i
        · subst hji
          simp
        · have hjtail : natFractionalGreedyList w items (remaining - w i) j ≠ 0 := by
            simpa [natFractionalGreedyList, hfit, Function.update, hji] using hj
          exact List.mem_cons_of_mem _ (ih _ _ hjtail)
      · by_cases hji : j = i
        · subst hji
          simp
        · exfalso
          simp [natFractionalGreedyList, hfit, hji] at hj

omit [LinearOrder I] [Nonempty I] in
lemma fractionalSocialWelfare_update_one_of_zero
    (b : I → ℝ) {x : I → ℝ} {i : I}
    (hxi : x i = 0) :
    fractionalSocialWelfare b (Function.update x i 1) =
      b i + fractionalSocialWelfare b x := by
  rw [fractionalSocialWelfare, fractionalSocialWelfare,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hs :
      Finset.sum (Finset.univ.erase i) (fun j => b j * Function.update x i 1 j) =
        Finset.sum (Finset.univ.erase i) (fun j => b j * x j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [hs]
  simp [Function.update, hxi]

omit [LinearOrder I] [Nonempty I] in
lemma fractionalSocialWelfare_singleton
    (b : I → ℝ) (i : I) (α : ℝ) :
    fractionalSocialWelfare b (fun j => if j = i then α else 0) = b i * α := by
  rw [fractionalSocialWelfare, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hs :
      Finset.sum (Finset.univ.erase i) (fun j => b j * (if j = i then α else 0)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [hji]
  rw [hs]
  simp

omit [LinearOrder I] in
lemma natFractionalGreedyList_le_integralGreedyList_plus_highest
    (w b : I → Nat) (hwpos : ∀ i, 0 < w i) :
    ∀ {items : List I}, items.Nodup → ∀ remaining,
      fractionalSocialWelfare (realBidOfNat b) (natFractionalGreedyList w items remaining) ≤
        (natBinarySocialWelfare b (integralGreedyList w items remaining) : ℝ) +
          highestBidValue b := by
  intro items hitems
  induction items with
  | nil =>
      intro remaining
      have hnil :
          (0 : ℝ) ≤
            (natBinarySocialWelfare b (fun _ => false) : ℝ) + highestBidValue b := by
        positivity
      simpa [natFractionalGreedyList, integralGreedyList, fractionalSocialWelfare] using hnil
  | cons i items ih =>
      intro remaining
      have hnotin : i ∉ items := (List.nodup_cons.mp hitems).1
      have htailNodup : items.Nodup := (List.nodup_cons.mp hitems).2
      by_cases hfit : w i ≤ remaining
      · have hfracTail :=
          ih htailNodup (remaining - w i)
        have hfracZero : natFractionalGreedyList w items (remaining - w i) i = 0 := by
          exact eq_zero_of_fractionalSupportedOn_of_not_mem
            (natFractionalGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintFalse : integralGreedyList w items (remaining - w i) i = false := by
          exact eq_false_of_supportedOn_of_not_mem
            (integralGreedyList_supportedOn w items (remaining - w i)) hnotin
        have hintEq :
            (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) =
              (b i : ℝ) +
                natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) := by
          exact_mod_cast
            (show natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) =
                b i + natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) by
              simpa [integralGreedyList, hfit] using
                (natBinarySocialWelfare_update_true_of_false
                  (b := b) (x := integralGreedyList w items (remaining - w i)) (i := i) hintFalse))
        calc
          fractionalSocialWelfare (realBidOfNat b)
              (natFractionalGreedyList w (i :: items) remaining)
              = (b i : ℝ) +
                  fractionalSocialWelfare (realBidOfNat b)
                    (natFractionalGreedyList w items (remaining - w i)) := by
                  simp [natFractionalGreedyList, hfit]
                  simpa [realBidOfNat] using
                    (fractionalSocialWelfare_update_one_of_zero
                      (b := realBidOfNat b) (x := natFractionalGreedyList w items (remaining - w i))
                      (i := i) hfracZero)
          _ ≤ (b i : ℝ) +
                ((natBinarySocialWelfare b (integralGreedyList w items (remaining - w i)) : ℝ) +
                  highestBidValue b) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left hfracTail (b i : ℝ)
          _ = (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue b := by
                rw [hintEq]
                ring
      · have hwipos : 0 < w i := hwpos i
        have hrem_le : remaining ≤ w i := Nat.le_of_lt (lt_of_not_ge hfit)
        have hratio_le_one : (remaining : ℝ) / w i ≤ 1 := by
          exact (div_le_one (by exact_mod_cast hwipos)).2 (by exact_mod_cast hrem_le)
        calc
          fractionalSocialWelfare (realBidOfNat b)
              (natFractionalGreedyList w (i :: items) remaining)
              = (b i : ℝ) * ((remaining : ℝ) / w i) := by
                  simp [natFractionalGreedyList, hfit]
                  simp [fractionalSocialWelfare_singleton, realBidOfNat]
          _ ≤ b i := by
              have hmul :
                  (b i : ℝ) * ((remaining : ℝ) / w i) ≤ (b i : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left hratio_le_one (show 0 ≤ (b i : ℝ) by positivity)
              simpa using hmul
          _ ≤ highestBidValue b := by
              exact_mod_cast le_highestBidValue b i
          _ ≤ (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) +
                highestBidValue b := by
              have hnonneg :
                  (0 : ℝ) ≤
                    (natBinarySocialWelfare b (integralGreedyList w (i :: items) remaining) : ℝ) := by
                positivity
              exact le_add_of_nonneg_left hnonneg

lemma natFractionalGreedyValue_le_integralGreedyValue_plus_highest
    (w b : I → Nat) (capacity : Nat) (hwpos : ∀ i, 0 < w i) :
    natFractionalGreedyValue w b capacity ≤
      integralGreedyValue w b capacity + highestBidValue b := by
  classical
  have hnodup :
      ((natAuctionData w capacity).sortedAgentsByRatio (realBidOfNat b)).Nodup := by
    simpa [sortedAgentsByRatio] using
      ((List.nodup_mergeSort
          (l := (Finset.univ : Finset I).toList)
          (le := fun i j =>
            decide
              ((natAuctionData w capacity).ratioTieKey (realBidOfNat b) i ≤
                (natAuctionData w capacity).ratioTieKey (realBidOfNat b) j))).2
        (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset I)))))
  simpa [natFractionalGreedyValue, natFractionalGreedyAllocation,
    integralGreedyValue, integralGreedyAllocation] using
    (natFractionalGreedyList_le_integralGreedyList_plus_highest
      (w := w) (b := b) hwpos hnodup capacity)

omit [LinearOrder I] [Nonempty I] in
lemma dynamicProgrammingOptimalAllocation_fractionalFeasible
    (w b : I → Nat) (capacity : Nat) :
    (natAuctionData w capacity).fractionalFeasible
      (binaryToAllocation (dynamicProgrammingOptimalAllocation w b capacity)) := by
  constructor
  · intro i
    by_cases hxi : dynamicProgrammingOptimalAllocation w b capacity i <;> simp [binaryToAllocation, hxi]
  · have hfeas :=
      dynamicProgrammingOptimalAllocation_feasible (w := w) (b := b) (capacity := capacity)
    simpa [natAuctionData, natBinaryLoad, binaryToAllocation] using
      (show ((natBinaryLoad w (dynamicProgrammingOptimalAllocation w b capacity) : Nat) : ℝ) ≤ capacity by
        exact_mod_cast hfeas)

/-- The ratio-sorted integral greedy algorithm, compared with the highest
single-value item, achieves a `1/2`-approximation to the DP-optimal `0/1`
knapsack welfare, provided the fractional greedy allocation is optimal for the
fractional relaxation and every item fits individually in the knapsack. -/
theorem integralGreedy_halfApprox_dpOptimal
    (w b : I → Nat) (capacity : Nat)
    (hwpos : ∀ i, 0 < w i)
    (_hallfit : ∀ i, w i ≤ capacity)
    (hfracOptimal :
      ∀ x : I → ℝ, (natAuctionData w capacity).fractionalFeasible x →
        fractionalSocialWelfare (realBidOfNat b) x ≤
          natFractionalGreedyValue w b capacity) :
    ((dynamicProgrammingOptimalValue w b capacity : ℝ) / 2) ≤
      max (integralGreedyValue w b capacity) (highestBidValue b) := by
  have hdp_le_frac :
      (dynamicProgrammingOptimalValue w b capacity : ℝ) ≤
        natFractionalGreedyValue w b capacity := by
    calc
      (dynamicProgrammingOptimalValue w b capacity : ℝ)
          = fractionalSocialWelfare (realBidOfNat b)
              (binaryToAllocation (dynamicProgrammingOptimalAllocation w b capacity)) := by
                norm_num [dynamicProgrammingOptimalValue,
                  fractionalSocialWelfare_realBidOfNat_binaryToAllocation]
      _ ≤ natFractionalGreedyValue w b capacity := by
          exact hfracOptimal _
            (dynamicProgrammingOptimalAllocation_fractionalFeasible
              (w := w) (b := b) (capacity := capacity))
  have hfrac_le :
      natFractionalGreedyValue w b capacity ≤
        integralGreedyValue w b capacity + highestBidValue b :=
    natFractionalGreedyValue_le_integralGreedyValue_plus_highest
      (w := w) (b := b) (capacity := capacity) hwpos
  have hsum_le_twomax :
      ((integralGreedyValue w b capacity : Nat) : ℝ) + highestBidValue b ≤
        2 * max (integralGreedyValue w b capacity) (highestBidValue b) := by
    have h1 : ((integralGreedyValue w b capacity : Nat) : ℝ) ≤ max (integralGreedyValue w b capacity) (highestBidValue b) := by
      exact_mod_cast le_max_left _ _
    have h2 : (highestBidValue b : ℝ) ≤ max (integralGreedyValue w b capacity) (highestBidValue b) := by
      exact_mod_cast le_max_right _ _
    have h12 := add_le_add h1 h2
    simpa [two_mul] using h12
  have hdp_le_sum : (dynamicProgrammingOptimalValue w b capacity : ℝ) ≤
      integralGreedyValue w b capacity + highestBidValue b :=
    le_trans hdp_le_frac hfrac_le
  have hdp_le_twomax : (dynamicProgrammingOptimalValue w b capacity : ℝ) ≤
      2 * max (integralGreedyValue w b capacity) (highestBidValue b) :=
    le_trans hdp_le_sum hsum_le_twomax
  nlinarith

end GreedyApproximation

end KnapsackAuction
