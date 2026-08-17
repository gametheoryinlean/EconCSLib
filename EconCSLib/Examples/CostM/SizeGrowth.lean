/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.SizeGrowth

/-!
# Regression examples for polynomial size growth

These examples exercise the size-sensitive rules needed for sound
polynomial-time composition and for loops whose local cost depends on the
current state.  They are intentionally small: their purpose is to check the
generic infrastructure, not to introduce an additional algorithmic model.
-/

namespace EconCSLib.Examples.CostM.SizeGrowth

open EconCSLib.OpenProblem.UnitCostRAM

/-! ## Sequential composition -/

/-- A first stage whose result has linear representation size. -/
def produceList (input : ℕ) : List ℕ :=
  List.replicate input input

/-- An explicit implementation contract for the first stage. -/
def produceListImplementation : CostedImplementation produceList where
  run input := ⟨produceList input, input⟩
  correct _ := rfl

theorem produceList_time_isPolynomial :
    produceListImplementation.IsPolynomial id := by
  simpa [produceListImplementation] using
    (IsPolyBound.self (sizeOf := id))

/-- Exact output-size certificate for the intermediate list. -/
def produceListSizeCertificate :
    OutputSizeCertificate (fun (_ : ℕ) (values : List ℕ) ↦ values.length)
      produceList where
  bound input := input
  output_le input := by simp [produceList]

theorem produceList_outputSize_isPolynomial :
    produceListSizeCertificate.IsPolynomial id := by
  simpa [produceListSizeCertificate] using
    (IsPolyBound.self (sizeOf := id))

/-- A continuation whose cost is linear in the intermediate representation,
not merely in the original input size. -/
def inspectList (_input : ℕ) (values : List ℕ) : ℕ :=
  values.length

def inspectListCost (input : ℕ) (values : List ℕ) : Cost ℕ :=
  ⟨inspectList input values, values.length⟩

theorem inspectList_relativeCost :
    IsPolyBoundInInputAndValueSize id
      (fun (_ : ℕ) (values : List ℕ) ↦ values.length)
      (fun input values ↦ (inspectListCost input values).ops) := by
  refine ⟨1, 1, ?_⟩
  intro input values
  simp [inspectListCost]
  omega

/-- The size-aware composition theorem derives polynomial time for the two
stages together. -/
theorem inspectProducedList_isPolynomial :
    (produceListImplementation.thenCosted inspectList inspectListCost
      (by intros; rfl)).IsPolynomial id := by
  apply CostedImplementation.thenCosted_isPolynomial
  · exact produceList_time_isPolynomial
  · exact ⟨produceListSizeCertificate,
      produceList_outputSize_isPolynomial⟩
  · exact inspectList_relativeCost

/-! ## Reachable-state bounds for finite loops -/

/-- One state-growing step.  Its local cost is linear in the current state
size, so a global constant body-cost bound would lose useful information. -/
def growStep (_input : ℕ) (state : List ℕ) : Cost (List ℕ) :=
  ⟨0 :: state, state.length + 1⟩

theorem growStep_iterate_length (input stage : ℕ) (state : List ℕ) :
    (Cost.iterateState (growStep input) stage state).length =
      state.length + stage := by
  induction stage generalizing state with
  | zero => simp
  | succ stage ih =>
      rw [Cost.iterateState_succ, ih]
      simp [growStep]
      omega

/-- Only states reachable from the empty initial state are bounded. -/
def growStateCertificate :
    IterateStateSizeCertificate id
      (fun (_ : ℕ) (state : List ℕ) ↦ state.length)
      id growStep (fun _ ↦ []) where
  bound input := input
  bound_isPolynomial := IsPolyBound.self
  state_le input stage hstage := by
    rw [growStep_iterate_length]
    simpa using hstage

theorem growStep_relativeCost :
    IsPolyBoundInInputAndStateSize id
      (fun (_ : ℕ) (state : List ℕ) ↦ state.length)
      (fun input state ↦ (growStep input state).ops) := by
  refine ⟨1, 1, ?_⟩
  intro input state
  simp [growStep]

/-- The counted loop is automatically polynomial after substituting the
reachable-state size certificate into the local body-cost polynomial. -/
theorem growingCountedLoop_isPolynomial :
    IsPolyTime id fun input ↦
      Cost.iterate input (growStep input) [] := by
  apply isPolyTime_iterate_of_reachableStateSize
  · exact IsPolyBound.self
  · exact growStateCertificate
  · exact growStep_relativeCost

/-- A one-operation loop test used to exercise the fuelled-while rule. -/
def keepGrowing (input : ℕ) (state : List ℕ) : Cost Bool :=
  ⟨state.length < input, 1⟩

theorem keepGrowing_relativeCost :
    IsPolyBoundInInputAndStateSize id
      (fun (_ : ℕ) (state : List ℕ) ↦ state.length)
      (fun input state ↦ (keepGrowing input state).ops) := by
  refine ⟨1, 0, ?_⟩
  simp [keepGrowing]

/-- The analogous fuelled while loop also receives a checked polynomial-time
certificate. -/
theorem growingWhileLoop_isPolynomial :
    IsPolyTime id fun input ↦
      Cost.whileFuel input (keepGrowing input) (growStep input) [] := by
  apply isPolyTime_whileFuel_of_reachableStateSize
  · exact IsPolyBound.self
  · exact growStateCertificate
  · exact keepGrowing_relativeCost
  · exact growStep_relativeCost

end EconCSLib.Examples.CostM.SizeGrowth
