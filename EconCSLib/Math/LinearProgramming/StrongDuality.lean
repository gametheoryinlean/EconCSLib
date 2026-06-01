/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.LinearAlgebra.Farkas

/-!
# EconCSLib.Math.LinearProgramming.StrongDuality

Formalises **LP strong duality** [MFoGT, Section 2.8, Exercise 9] over any
linearly ordered field.

For the standard-form LP pair

  Primal P:  min ⟨c, x⟩  subject to  A x ≥ b  and  x ≥ 0
  Dual   D:  max ⟨u, b⟩  subject to  uᵀA ≤ c  and  u ≥ 0

if the primal is feasible and bounded below by `d ∈ 𝕜`, there exists a
dual-feasible `u` with `⟨u, b⟩ ≥ d`. Combined with weak duality this yields
equal primal/dual optima.

## Proof strategy

Apply Farkas (#69) to the **augmented system** that merges `A x ≥ b` with
the non-negativity constraints `x ≥ 0`. The augmented row index is
`I ⊕ Fin n`: the original `I` rows are unchanged, and each `Fin n` row is
the unit row `x_{j'} ≥ 0`. The primal lower-bound hypothesis becomes a
Farkas primal bound on the augmented system, and the Farkas certificate
decomposes into `(u, v)` where `u : I → 𝕜` is the dual feasible point and
`v : Fin n → 𝕜` is the slack on the non-negativity constraints (with
`uᵀA + v = c`, hence `uᵀA ≤ c`).

## Blueprint

* `docs/knowledge/nodes/core/linear_programming.strong_duality.md`
-/

open Finset BigOperators EconCSLib.LinearAlgebra

set_option linter.unusedSectionVars false

namespace EconCSLib.LinearProgramming

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-! ### Standard-form primal / dual predicates -/

/-- Primal feasibility: `∃ x, A x ≥ b ∧ x ≥ 0`. -/
def PrimalFeasible (A : I → Fin n → 𝕜) (b : I → 𝕜) : Prop :=
  ∃ x : Fin n → 𝕜, (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j)

/-- Dual feasibility of `u`: `u ≥ 0 ∧ uᵀA ≤ c`. -/
def DualFeasible (A : I → Fin n → 𝕜) (c : Fin n → 𝕜) (u : I → 𝕜) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * A i j ≤ c j)

/-! ### Weak duality

For any primal-feasible `x` and dual-feasible `u`, `⟨c, x⟩ ≥ ⟨u, b⟩`. -/
theorem lp_weak_duality (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    {x : Fin n → 𝕜} (hxA : ∀ i, b i ≤ ∑ j, A i j * x j) (hxnn : ∀ j, 0 ≤ x j)
    {u : I → 𝕜} (hu_du : DualFeasible A c u) :
    ∑ i, u i * b i ≤ ∑ j, c j * x j := by
  obtain ⟨hu_nn, hu_le⟩ := hu_du
  -- ⟨u, b⟩ ≤ ⟨u, A x⟩ (componentwise from Ax ≥ b, weighted by u ≥ 0)
  --        = ⟨uᵀA, x⟩
  --        ≤ ⟨c, x⟩      (componentwise from uᵀA ≤ c, weighted by x ≥ 0)
  calc ∑ i, u i * b i
      ≤ ∑ i, u i * (∑ j, A i j * x j) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hxA i) (hu_nn i)
    _ = ∑ j, (∑ i, u i * A i j) * x j := by
        have h1 : (∑ i, u i * ∑ j, A i j * x j)
            = ∑ i, ∑ j, u i * (A i j * x j) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
        have h2 : (∑ i, ∑ j, u i * (A i j * x j))
            = ∑ j, ∑ i, u i * (A i j * x j) := Finset.sum_comm
        have h3 : (∑ j, ∑ i, u i * (A i j * x j))
            = ∑ j, (∑ i, u i * A i j) * x j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [h1, h2, h3]
    _ ≤ ∑ j, c j * x j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hu_le j) (hxnn j)

/-! ### Augmented system for strong duality

To reduce LP strong duality to Farkas, augment the primal `A x ≥ b` with
unit rows `x_{j'} ≥ 0`. The augmented row index is `I ⊕ Fin n`. -/

/-- Augmented row index for the LP-Farkas reduction. -/
abbrev DualAugRow (I : Type*) (n : ℕ) : Type _ := I ⊕ Fin n

/-- Augmented matrix combining `A` rows with `x ≥ 0` unit rows. -/
def dualAugA (A : I → Fin n → 𝕜) : DualAugRow I n → Fin n → 𝕜
  | Sum.inl i, j => A i j
  | Sum.inr j', j => if j = j' then 1 else 0

/-- Augmented RHS. -/
def dualAugB (b : I → 𝕜) : DualAugRow I n → 𝕜
  | Sum.inl i => b i
  | Sum.inr _ => 0

@[simp] theorem dualAugA_inl (A : I → Fin n → 𝕜) (i : I) (j : Fin n) :
    dualAugA A (Sum.inl i) j = A i j := rfl

@[simp] theorem dualAugA_inr (A : I → Fin n → 𝕜) (j' j : Fin n) :
    dualAugA A (Sum.inr j') j = if j = j' then 1 else 0 := rfl

@[simp] theorem dualAugB_inl (b : I → 𝕜) (i : I) :
    dualAugB b (Sum.inl i : DualAugRow I n) = b i := rfl

@[simp] theorem dualAugB_inr (b : I → 𝕜) (j' : Fin n) :
    dualAugB b (Sum.inr j' : DualAugRow I n) = 0 := rfl

/-- Augmented feasibility is the primal feasibility (with `x ≥ 0`). -/
theorem isFeasible_dualAug_iff (A : I → Fin n → 𝕜) (b : I → 𝕜) :
    IsFeasible (dualAugA A) (dualAugB b) ↔ PrimalFeasible A b := by
  unfold IsFeasible PrimalFeasible
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i
      have h := hx (Sum.inl i)
      simpa [rowEval] using h
    · intro j'
      have h := hx (Sum.inr j')
      -- h : 0 ≤ ∑ j, (if j = j' then 1 else 0) * x j = x j'
      simp only [rowEval, dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h
      exact h
  · rintro ⟨x, hxA, hxnn⟩
    refine ⟨x, ?_⟩
    intro idx
    rcases idx with i | j'
    · simp only [rowEval, dualAugB_inl, dualAugA_inl]
      exact hxA i
    · simp only [rowEval, dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq']
      exact hxnn j'

/-! ### Strong duality -/

/-- **LP Strong Duality** [MFoGT, Section 2.8, Exercise 9]: if the primal LP
`min ⟨c, x⟩ s.t. A x ≥ b, x ≥ 0` is feasible and bounded below by `d`, then
there exists a dual-feasible `u` with `⟨u, b⟩ ≥ d`. -/
theorem lp_strong_duality (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (d : 𝕜)
    (hP_feas : PrimalFeasible A b)
    (hP_bound : ∀ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) → (∀ j, 0 ≤ x j) → d ≤ ∑ j, c j * x j) :
    ∃ u : I → 𝕜, DualFeasible A c u ∧ d ≤ ∑ i, u i * b i := by
  -- Translate hypotheses to the augmented system.
  have hAug_feas : IsFeasible (dualAugA A) (dualAugB b) :=
    (isFeasible_dualAug_iff A b).mpr hP_feas
  have hAug_bound : ∀ x : Fin n → 𝕜,
      (∀ idx, dualAugB b idx ≤ ∑ j, dualAugA A idx j * x j) →
      d ≤ ∑ j, c j * x j := by
    intro x hx
    apply hP_bound x
    · intro i
      have h := hx (Sum.inl i)
      simpa using h
    · intro j'
      have h := hx (Sum.inr j')
      simp only [dualAugB_inr, dualAugA_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h
      exact h
  -- Apply Farkas to the augmented system.
  have hCert := (farkas_lemma (dualAugA A) (dualAugB b) c d hAug_feas).mp hAug_bound
  obtain ⟨u_aug, hu_nn, hu_col, hu_b⟩ := hCert
  -- Decompose u_aug into u (on I) and v (on Fin n).
  refine ⟨fun i => u_aug (Sum.inl i), ?_, ?_⟩
  · -- DualFeasible: u ≥ 0 and uᵀA ≤ c.
    refine ⟨fun i => hu_nn (Sum.inl i), ?_⟩
    intro j
    -- Use the column-j condition on the augmented system.
    have h := hu_col j
    -- h : (∑ row, u_aug row * dualAugA A row j) = c j
    rw [Fintype.sum_sum_type] at h
    -- h : (∑ i, u_aug (Sum.inl i) * dualAugA A (Sum.inl i) j) +
    --     (∑ j', u_aug (Sum.inr j') * dualAugA A (Sum.inr j') j) = c j
    simp only [dualAugA_inl, dualAugA_inr, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
               Fintype.sum_ite_eq, Fintype.sum_ite_eq'] at h
    -- h : (∑ i, u_aug (inl i) * A i j) + u_aug (Sum.inr j) = c j
    -- Goal: ∑ i, u_aug (Sum.inl i) * A i j ≤ c j
    have hv_nn : 0 ≤ u_aug (Sum.inr j) := hu_nn (Sum.inr j)
    linarith
  · -- ⟨u, b⟩ ≥ d
    have h : (∑ row, u_aug row * dualAugB b row) = ∑ i, u_aug (Sum.inl i) * b i := by
      rw [Fintype.sum_sum_type]
      simp only [dualAugB_inl, dualAugB_inr, mul_zero, Finset.sum_const_zero, add_zero]
    linarith [hu_b, h.symm ▸ hu_b]

end EconCSLib.LinearProgramming
