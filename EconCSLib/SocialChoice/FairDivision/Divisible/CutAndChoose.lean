/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.DubinsSpanier
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose

The **cut-and-choose** protocol for 2-agent divisible fair division.

## Protocol

1. The **cutter** (agent 0) cuts the cake at a position `t ∈ [0,1]`, producing two pieces:
   - Left piece:  `[0, t]`
   - Right piece: `(t, 1]`
2. The **chooser** (agent 1) picks whichever piece they value more (ties go to the left).
3. The cutter receives the remaining piece.

## Main definitions

* `cutAndChooseAlloc μ t` — allocation produced by the protocol at cut point `t ∈ [0,1]`
* `IsFairCutPoint μ t`   — the cut is "fair for the cutter": `μ 0 (Iic t) = μ 0 (Ioi t)`

## Main results

* `cutAndChooseAlloc_isAllocation` — the output is always a valid complete partition
* `chooser_isEnvyFree`                      — the chooser (agent 1) never envies the cutter,
  regardless of the cut point (they always receive their preferred half)
* `cutter_isEnvyFree_of_fair`               — the cutter (agent 0) does not envy the chooser
  at a fair cut (the two halves are equal for the cutter, so they are indifferent)
* `cutAndChoose_isEnvyFree`                 — both agents are EF at any fair cut point
* `fairCutPoint_exists`                     — for finite non-atomic `μ 0`, a fair cut always
  exists (via the shared unit-interval IVT lemma `DubinsSpanier.cut_exists`)
* `cutAndChoose_ef_exists`                  — EF allocation always exists for 2 agents
  (corollary: combine `fairCutPoint_exists` with `cutAndChoose_isEnvyFree`)

## Relationship to `ef_exists_two_agents`

`ef_exists_two_agents` in `EnvyFree.lean` proves EF existence directly as an existential.
This file adds structure: the protocol is an **explicit function** parametrized by the cut
point, and the two fairness guarantees (chooser and cutter) are proved separately. The key
separation is that `chooser_isEnvyFree` holds for *any* cut — the chooser's guarantee does
not depend on the cut being fair.

## References

* Steinhaus, "The Problem of Fair Division" (1948) — original fair division paper
* Robertson–Webb, *Cake-Cutting Algorithms* (1998), Ch. 1
* Nisan et al., *Algorithmic Game Theory*, Ch. 13
-/

open MeasureTheory Set
open scoped unitInterval

namespace SocialChoice
namespace FairDivision
namespace Divisible

/-! ### Protocol definition -/

/-- The cut-and-choose allocation at cut point `t ∈ [0,1]`.

    The chooser (agent 1) receives the half they value more:
    - If `μ 1 (Iic t) ≥ μ 1 (Ioi t)`, agent 1 takes `[0, t]`; agent 0 gets `(t, 1]`.
    - Otherwise, agent 1 takes `(t, 1]`; agent 0 gets `[0, t]`.

    The allocation is noncomputable because measures are noncomputable. -/
noncomputable def cutAndChooseAlloc (μ : Fin 2 → Measure I) (t : I) :
    Allocation (Fin 2) I :=
  fun i =>
    if μ 1 (Iic t) ≥ μ 1 (Ioi t) then
      -- chooser takes left, cutter takes right
      if i = 0 then Ioi t else Iic t
    else
      -- chooser takes right, cutter takes left
      if i = 0 then Iic t else Ioi t

/-- A cut point `t` is **fair** (for the cutter, agent 0) if agent 0's measure is split
    equally: `μ 0 [0, t] = μ 0 (t, 1]`.

    At a fair cut the cutter is indifferent between the two halves, so they cannot envy
    whichever piece the chooser selects. -/
def IsFairCutPoint (μ : Fin 2 → Measure I) (t : I) : Prop :=
  μ 0 (Iic t) = μ 0 (Ioi t)

/-! ### Simp lemmas for agent-specific pieces -/

/-- Cutter (agent 0) receives the right piece when the chooser prefers left, and the
    left piece otherwise. -/
@[simp]
lemma cutAndChooseAlloc_zero (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 0 = if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t := rfl

/-- Chooser (agent 1) receives the left piece if they prefer it, the right piece otherwise. -/
@[simp]
lemma cutAndChooseAlloc_one (μ : Fin 2 → Measure I) (t : I) :
    cutAndChooseAlloc μ t 1 = if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t := by
  simp [cutAndChooseAlloc]

/-! ### The output is always a valid partition -/

/-- For any cut point `t`, the cut-and-choose allocation is a complete measurable partition
    of `[0,1]` into two pieces. This holds regardless of whether the cut is fair. -/
theorem cutAndChooseAlloc_isAllocation (μ : Fin 2 → Measure I) (t : I) :
    IsAllocation (cutAndChooseAlloc μ t) := by
  have hmL  : MeasurableSet (Iic t : Set I)    := measurableSet_Iic
  have hmR  : MeasurableSet (Ioi t : Set I)    := measurableSet_Ioi
  have hdLR : Disjoint (Iic t : Set I) (Ioi t) := Iic_disjoint_Ioi le_rfl
  have hcov : (Iic t : Set I) ∪ Ioi t = univ   := Iic_union_Ioi
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · -- Each piece is measurable (either Iic t or Ioi t).
    -- `show` uses definitional equality to expose the underlying if-expression.
    fin_cases i
    · show MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs <;> assumption
    · show MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs <;> assumption
  · -- Distinct agents receive disjoint pieces
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
                    (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs with h
      · exact hdLR.symm
      · exact hdLR
    · show Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
                    (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs with h
      · exact hdLR
      · exact hdLR.symm
    · exact absurd rfl hij
  · -- The two pieces cover the entire cake
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x ∈ Iic t ∨ x ∈ Ioi t :=
      (mem_union x (Iic t) (Ioi t)).mp (hcov ▸ mem_univ x)
    by_cases h : μ 1 (Iic t) ≥ μ 1 (Ioi t)
    · -- cutter gets Ioi, chooser gets Iic
      rcases hx with hx | hx
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_pos h]; exact hx⟩
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_pos h]; exact hx⟩
    · -- cutter gets Iic, chooser gets Ioi
      rcases hx with hx | hx
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_neg h]; exact hx⟩
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_neg h]; exact hx⟩

/-! ### Chooser guarantee -/

/-- **The chooser (agent 1) never envies the cutter**, regardless of the cut point.

    Since agent 1 selects whichever piece they value more, their own piece is always
    at least as valuable as the cutter's piece. No fairness condition on the cut is needed.

    This is the key asymmetry of cut-and-choose: the chooser's guarantee is unconditional;
    only the cutter's guarantee depends on the cut being fair. -/
theorem chooser_isEnvyFree (μ : Fin 2 → Measure I) (t : I) :
    (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 0) ≤
    (MeasureValuation μ).val 1 (cutAndChooseAlloc μ t 1) := by
  -- Reduce to μ 1 (if ...) ≤ μ 1 (if ...) via definitional equality
  show μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t) ≤
       μ 1 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
  split_ifs with h
  · exact h
  · push_neg at h; exact le_of_lt h

/-! ### Cutter guarantee at fair cut -/

/-- **The cutter (agent 0) does not envy the chooser** at a fair cut.

    If the cut point `t` satisfies `IsFairCutPoint μ t`, then agent 0 values both halves
    equally. Regardless of which half the chooser takes, the cutter is indifferent. -/
theorem cutter_isEnvyFree_of_fair (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 1) ≤
    (MeasureValuation μ).val 0 (cutAndChooseAlloc μ t 0) := by
  show μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t) ≤
       μ 0 (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
  split_ifs with h
  · -- chooser gets Iic, cutter gets Ioi; need μ 0 (Iic t) ≤ μ 0 (Ioi t)
    exact le_of_eq hfair
  · -- chooser gets Ioi, cutter gets Iic; need μ 0 (Ioi t) ≤ μ 0 (Iic t)
    exact le_of_eq hfair.symm

/-! ### Combined EF -/

/-- **Both agents are envy-free** at any fair cut point.

    This combines `chooser_isEnvyFree` (unconditional) and `cutter_isEnvyFree_of_fair`
    (requires fair cut) to give the full `IsEnvyFree` predicate for both agents. -/
theorem cutAndChoose_isEnvyFree (μ : Fin 2 → Measure I) (t : I)
    (hfair : IsFairCutPoint μ t) :
    IsEnvyFree (MeasureValuation μ) (cutAndChooseAlloc μ t) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact le_refl _
  · exact cutter_isEnvyFree_of_fair μ t hfair
  · exact chooser_isEnvyFree μ t
  · exact le_refl _

/-! ### Fair cut existence -/

/-- **A fair cut always exists** for finite non-atomic `μ 0` on `[0,1]`.

    This is the `c = μ([0,1])/2` case of `DubinsSpanier.cut_exists`. -/
theorem fairCutPoint_exists
    (μ : Fin 2 → Measure I) [IsFiniteMeasure (μ 0)] [NoAtoms (μ 0)] :
    ∃ t : I, IsFairCutPoint μ t := by
  set M := (μ 0 univ).toReal with hM_def
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have h_half_nonneg : 0 ≤ M / 2 := by positivity
  rcases eq_or_lt_of_le hM_nonneg with hM0 | hM_pos
  · refine ⟨0, ?_⟩
    unfold IsFairCutPoint
    have hM_eq : M = 0 := hM0.symm
    have h_toReal_zero : (μ 0 Set.univ).toReal = 0 := by
      simpa [hM_def] using hM_eq
    have hμ_univ : μ 0 Set.univ = 0 := by
      have hfin : μ 0 Set.univ ≠ ⊤ := measure_ne_top _ _
      rcases (ENNReal.toReal_eq_zero_iff (μ 0 Set.univ)).mp h_toReal_zero with hzero | htop
      · exact hzero
      · exact (hfin htop).elim
    have h_left : μ 0 (Iic (0 : I)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc
        μ 0 (Iic (0 : I)) ≤ μ 0 Set.univ := measure_mono (Set.subset_univ _)
        _ = 0 := hμ_univ
    have h_right : μ 0 (Ioi (0 : I)) = 0 := by
      refine le_antisymm ?_ zero_le
      calc
        μ 0 (Ioi (0 : I)) ≤ μ 0 Set.univ := measure_mono (Set.subset_univ _)
        _ = 0 := hμ_univ
    rw [h_left, h_right]
  obtain ⟨tstar, htstar⟩ := cut_exists (μ 0) (M / 2) (half_pos hM_pos) (half_lt_self hM_pos)
  refine ⟨tstar, ?_⟩
  unfold IsFairCutPoint
  -- Additivity: μ 0 (Iic tstar) + μ 0 (Ioi tstar) = μ 0 univ
  have h_split : μ 0 (Iic tstar) + μ 0 (Ioi tstar) = μ 0 univ := by
    have := measure_union (Iic_disjoint_Ioi (le_refl tstar)) measurableSet_Ioi (μ := μ 0)
    rw [Iic_union_Ioi] at this; exact this.symm
  -- toReal of both halves equals M/2
  have h_Iic : (μ 0 (Iic tstar)).toReal = M / 2 := htstar
  have h_Ioi : (μ 0 (Ioi tstar)).toReal = M / 2 := by
    have h_add : (μ 0 (Iic tstar)).toReal + (μ 0 (Ioi tstar)).toReal = M := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h_split]
    linarith
  -- Equal finite toReal values imply equality as ENNReal
  apply le_antisymm
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (by linarith)
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (by linarith)

/-! ### EF existence corollary -/

/-- **EF allocations always exist** for 2 agents with non-atomic finite measures (via
    cut-and-choose).

    This recovers `ef_exists_two_agents` from `EnvyFree.lean` as a corollary:
    `fairCutPoint_exists` gives a cut point `tstar` where agent 0's measure is halved,
    and `cutAndChoose_isEnvyFree` gives EF at any fair cut. -/
theorem cutAndChoose_ef_exists
    (μ : Fin 2 → Measure I)
    [IsFiniteMeasure (μ 0)] [NoAtoms (μ 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A := by
  obtain ⟨t, ht⟩ := fairCutPoint_exists μ
  exact ⟨cutAndChooseAlloc μ t,
         cutAndChooseAlloc_isAllocation μ t,
         cutAndChoose_isEnvyFree μ t ht⟩

/-- Bundled-instance form of cut-and-choose envy-free existence. -/
theorem cutAndChoose_exists_envyFree_allocation
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NoAtoms (M.measure 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ M.IsEnvyFree A :=
  cutAndChoose_ef_exists M.measure

/-- Cut-and-choose as a rule on bundled two-agent measure instances. -/
noncomputable def cutAndChooseRule
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NoAtoms (M.measure 0)] :
    {A : Allocation (Fin 2) I // M.feasible A} :=
  let t := Classical.choose (fairCutPoint_exists M.measure)
  ⟨cutAndChooseAlloc M.measure t, cutAndChooseAlloc_isAllocation M.measure t⟩

/-- The bundled cut-and-choose rule is envy-free. -/
theorem cutAndChooseRule_isEnvyFree
    (M : MeasureInstance (Fin 2) I)
    [IsFiniteMeasure (M.measure 0)] [NoAtoms (M.measure 0)] :
    M.IsEnvyFree (cutAndChooseRule M).1 := by
  unfold cutAndChooseRule
  exact cutAndChoose_isEnvyFree M.measure
    (Classical.choose (fairCutPoint_exists M.measure))
    (Classical.choose_spec (fairCutPoint_exists M.measure))

end Divisible
end FairDivision
end SocialChoice
