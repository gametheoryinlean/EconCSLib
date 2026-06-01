/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.LinearProgramming.StrongDuality

/-!
# EconCSLib.Math.LinearProgramming.StrongComplementarity

Formalises **LP strong complementary slackness** [MFoGT, Section 2.8,
Exercise 11] over any linearly ordered field.

For the standard-form primal/dual pair

  Primal P:  min ⟨c, x⟩  subject to  A x ≥ b  and  x ≥ 0
  Dual   D:  max ⟨u, b⟩  subject to  uᵀ A ≤ c  and  u ≥ 0

if both are feasible, then there exist optimal `x` and `u` such that

  (Ax − b)_i > 0  ⟺  u_i = 0,        for every row i,
  (c − uᵀA)_j > 0 ⟺  x_j = 0,        for every column j.

That is, for every complementary pair (primal slack on row i, dual
variable u_i; resp. dual slack on column j, primal variable x_j),
**exactly one** of the two is strictly positive in some optimal pair.

## Proof strategy

The hard direction (strong content) follows from LP strong duality
applied to a perturbed LP, then combined across all constraints by
convex aggregation.  The easy direction is **weak complementary
slackness**, which is a direct consequence of any optimal pair.

This file proves:

* `lp_weak_complementarity` — the easy direction (strict slack ⇒ zero
  variable), holds for every optimal primal-dual pair.
* `exists_lp_strong_complementarity` — the existence form of the
  full bidirectional strong complementarity.

## Blueprint

* `docs/knowledge/nodes/core/linear_programming.strong_complementarity.md`
-/

open Finset BigOperators EconCSLib.LinearAlgebra

set_option linter.unusedSectionVars false

namespace EconCSLib.LinearProgramming

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-! ### Weak complementary slackness

For any optimal primal-dual pair `(x, u)` with matching objective
values, the standard CS identities hold:

  (Ax − b)_i · u_i = 0   for every row i,
  (c − uᵀA)_j · x_j = 0   for every column j.

Equivalently: strict primal slack forces the corresponding dual
variable to vanish, and strict dual slack forces the corresponding
primal variable to vanish.
-/

/-- **Weak complementary slackness**, row form. -/
theorem lp_weak_complementarity_row
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    {x : Fin n → 𝕜} (hxA : ∀ i, b i ≤ ∑ j, A i j * x j) (hxnn : ∀ j, 0 ≤ x j)
    {u : I → 𝕜} (hu_du : DualFeasible A c u)
    (h_match : ∑ j, c j * x j = ∑ i, u i * b i) :
    ∀ i, (∑ j, A i j * x j - b i) * u i = 0 := by
  obtain ⟨hu_nn, hu_le⟩ := hu_du
  -- Sum identity: ∑ u_i * (A x - b)_i + ∑ x_j * (c - uᵀA)_j = ⟨c, x⟩ - ⟨u, b⟩ = 0.
  have hsum1 : (∑ i, u i * (∑ j, A i j * x j - b i))
             + (∑ j, x j * (c j - ∑ i, u i * A i j)) = 0 := by
    have h1 : (∑ i, u i * (∑ j, A i j * x j - b i))
            = (∑ i, ∑ j, u i * (A i j * x j)) - ∑ i, u i * b i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_sub, Finset.mul_sum]
    have h2 : (∑ j, x j * (c j - ∑ i, u i * A i j))
            = (∑ j, c j * x j) - (∑ j, x j * ∑ i, u i * A i j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_sub, mul_comm (x j) (c j)]
    have hcross : (∑ i, ∑ j, u i * (A i j * x j))
                = (∑ j, x j * ∑ i, u i * A i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [h1, h2, hcross]
    linarith [h_match]
  -- Each term in hsum1 is ≥ 0 (nonneg variable times nonneg slack), so each is 0.
  have hterm_row : ∀ i ∈ Finset.univ, 0 ≤ u i * (∑ j, A i j * x j - b i) := by
    intro i _
    exact mul_nonneg (hu_nn i) (by linarith [hxA i])
  have hterm_col : ∀ j ∈ Finset.univ, 0 ≤ x j * (c j - ∑ i, u i * A i j) := by
    intro j _
    exact mul_nonneg (hxnn j) (by linarith [hu_le j])
  have hsum_row_nn : 0 ≤ ∑ i, u i * (∑ j, A i j * x j - b i) :=
    Finset.sum_nonneg hterm_row
  have hsum_col_nn : 0 ≤ ∑ j, x j * (c j - ∑ i, u i * A i j) :=
    Finset.sum_nonneg hterm_col
  have hsum_row_zero : ∑ i, u i * (∑ j, A i j * x j - b i) = 0 := by linarith
  -- Each individual term is 0.
  intro i
  have hindiv : u i * (∑ j, A i j * x j - b i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_row).mp hsum_row_zero i (Finset.mem_univ i)
  rw [mul_comm] at hindiv
  exact hindiv

/-- **Weak complementary slackness**, column form. -/
theorem lp_weak_complementarity_col
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    {x : Fin n → 𝕜} (hxA : ∀ i, b i ≤ ∑ j, A i j * x j) (hxnn : ∀ j, 0 ≤ x j)
    {u : I → 𝕜} (hu_du : DualFeasible A c u)
    (h_match : ∑ j, c j * x j = ∑ i, u i * b i) :
    ∀ j, (c j - ∑ i, u i * A i j) * x j = 0 := by
  obtain ⟨hu_nn, hu_le⟩ := hu_du
  -- Sum identity: ∑ u_i * (A x - b)_i + ∑ x_j * (c - uᵀA)_j = ⟨c, x⟩ - ⟨u, b⟩ = 0.
  have hsum1 : (∑ i, u i * (∑ j, A i j * x j - b i))
             + (∑ j, x j * (c j - ∑ i, u i * A i j)) = 0 := by
    have h1 : (∑ i, u i * (∑ j, A i j * x j - b i))
            = (∑ i, ∑ j, u i * (A i j * x j)) - ∑ i, u i * b i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_sub, Finset.mul_sum]
    have h2 : (∑ j, x j * (c j - ∑ i, u i * A i j))
            = (∑ j, c j * x j) - (∑ j, x j * ∑ i, u i * A i j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_sub, mul_comm (x j) (c j)]
    have hcross : (∑ i, ∑ j, u i * (A i j * x j))
                = (∑ j, x j * ∑ i, u i * A i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [h1, h2, hcross]
    linarith [h_match]
  have hterm_row : ∀ i ∈ Finset.univ, 0 ≤ u i * (∑ j, A i j * x j - b i) := by
    intro i _
    exact mul_nonneg (hu_nn i) (by linarith [hxA i])
  have hterm_col : ∀ j ∈ Finset.univ, 0 ≤ x j * (c j - ∑ i, u i * A i j) := by
    intro j _
    exact mul_nonneg (hxnn j) (by linarith [hu_le j])
  have hsum_row_nn : 0 ≤ ∑ i, u i * (∑ j, A i j * x j - b i) :=
    Finset.sum_nonneg hterm_row
  have hsum_col_nn : 0 ≤ ∑ j, x j * (c j - ∑ i, u i * A i j) :=
    Finset.sum_nonneg hterm_col
  have hsum_col_zero : ∑ j, x j * (c j - ∑ i, u i * A i j) = 0 := by linarith
  intro j
  have hindiv : x j * (c j - ∑ i, u i * A i j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_col).mp hsum_col_zero j (Finset.mem_univ j)
  rw [mul_comm] at hindiv
  exact hindiv

/-! ### Optimality-augmented system

For the per-index strong-CS dichotomy we apply Farkas to the system
encoding "primal-optimal `x`": `A x ≥ b`, `x ≥ 0`, `⟨c, x⟩ ≤ v`. The
augmented row index is `(I ⊕ Fin n) ⊕ Unit`:

* `inl (inl i)` ↦ original row `A i x ≥ b i`,
* `inl (inr j')` ↦ unit row `x_{j'} ≥ 0`,
* `inr ()` ↦ optimality row `-⟨c, x⟩ ≥ -v` (i.e. `⟨c, x⟩ ≤ v`).
-/

/-- Optimality-augmented row index. -/
abbrev OptAugRow (I : Type*) (n : ℕ) : Type _ := (I ⊕ Fin n) ⊕ Unit

/-- Optimality-augmented matrix. -/
def optAugA (A : I → Fin n → 𝕜) (c : Fin n → 𝕜) : OptAugRow I n → Fin n → 𝕜
  | Sum.inl (Sum.inl i), j => A i j
  | Sum.inl (Sum.inr j'), j => if j = j' then 1 else 0
  | Sum.inr (), j => -c j

/-- Optimality-augmented RHS. -/
def optAugB (b : I → 𝕜) (v : 𝕜) : OptAugRow I n → 𝕜
  | Sum.inl (Sum.inl i) => b i
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr () => -v

@[simp] theorem optAugA_inl_inl (A : I → Fin n → 𝕜) (c : Fin n → 𝕜)
    (i : I) (j : Fin n) :
    optAugA A c (Sum.inl (Sum.inl i)) j = A i j := rfl

@[simp] theorem optAugA_inl_inr (A : I → Fin n → 𝕜) (c : Fin n → 𝕜)
    (j' j : Fin n) :
    optAugA A c (Sum.inl (Sum.inr j')) j = if j = j' then 1 else 0 := rfl

@[simp] theorem optAugA_inr (A : I → Fin n → 𝕜) (c : Fin n → 𝕜) (j : Fin n) :
    optAugA A c (Sum.inr ()) j = -c j := rfl

@[simp] theorem optAugB_inl_inl (b : I → 𝕜) (v : 𝕜) (i : I) :
    optAugB b v (Sum.inl (Sum.inl i) : OptAugRow I n) = b i := rfl

@[simp] theorem optAugB_inl_inr (b : I → 𝕜) (v : 𝕜) (j' : Fin n) :
    optAugB b v (Sum.inl (Sum.inr j') : OptAugRow I n) = 0 := rfl

@[simp] theorem optAugB_inr (b : I → 𝕜) (v : 𝕜) :
    optAugB b v (Sum.inr () : OptAugRow I n) = -v := rfl

/-- An `x` satisfies `optAugA · x ≥ optAugB` iff `x` is primal-feasible and
has objective at most `v`. -/
theorem optAug_feasible_iff (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜)
    (v : 𝕜) (x : Fin n → 𝕜) :
    (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) ↔
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j ≤ v) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have h1 := h (Sum.inl (Sum.inl i))
      simpa using h1
    · intro j'
      have h1 := h (Sum.inl (Sum.inr j'))
      simp only [optAugB_inl_inr, optAugA_inl_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq'] at h1
      exact h1
    · have h1 := h (Sum.inr ())
      simp only [optAugB_inr, optAugA_inr] at h1
      have : (∑ j, -c j * x j) = -(∑ j, c j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [this ▸ h1]
  · rintro ⟨hAx, hxnn, hcx⟩ idx
    rcases idx with ⟨i | j'⟩ | ⟨⟩
    · simpa using hAx i
    · simp only [optAugB_inl_inr, optAugA_inl_inr, ite_mul, one_mul, zero_mul,
                 Fintype.sum_ite_eq']
      exact hxnn j'
    · show optAugB b v (Sum.inr ()) ≤ ∑ j, optAugA A c (Sum.inr ()) j * x j
      simp only [optAugB_inr, optAugA_inr]
      have : (∑ j, -c j * x j) = -(∑ j, c j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [this]

/-! ### Per-row dichotomy

For each fixed row `i₀`, there exists an optimal primal-dual pair
`(x, u)` with the row complementarity sum `(Ax - b)_{i₀} + u_{i₀}`
strictly positive.

This is the key step that upgrades weak CS to strong CS at one specific
row. The proof is by classical case analysis:

* **Case A**: some primal-optimal `x` has `(Ax - b)_{i₀} > 0`. Pair
  with any dual-optimal `u`.
* **Case B**: every primal-optimal `x` has `(Ax - b)_{i₀} = 0`. Apply
  Farkas to the bound implication `(Ax - b)_{i₀} ≤ 0` on the augmented
  system; the certificate yields a dual-optimal `u` with `u_{i₀} > 0`.
-/

/-- **Per-row strict-CS witness**: for each row `i₀`, there exists an
optimal primal-dual pair with `(Ax - b)_{i₀} + u_{i₀} > 0`.

Hypotheses:
* `hx₀` — `x₀` is primal-feasible with `⟨c, x₀⟩ = v` (primal-optimal).
* `hu₀` — `u₀` is dual-feasible with `⟨u₀, b⟩ = v` (dual-optimal).

Both `x₀` and `u₀` exist by LP strong duality when both P and D are
feasible. -/
theorem exists_row_strict_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v)
    (i₀ : I) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      0 < (∑ j, A i₀ j * x j - b i₀) + u i₀ := by
  classical
  -- Classical case split.
  by_cases hCaseA : ∃ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j = v) ∧ (b i₀ < ∑ j, A i₀ j * x j)
  · -- Case A: primal-optimal x with strict row slack at i₀.
    obtain ⟨x, hxA, hxnn, hcx, hstrict⟩ := hCaseA
    refine ⟨x, u₀, hxA, hxnn, hu₀, hcx, hu₀_val, ?_⟩
    have hu₀nn : 0 ≤ u₀ i₀ := hu₀.1 i₀
    linarith
  · -- Case B: ∀ primal-optimal x, (Ax - b)_{i₀} ≤ 0 (forced = 0 by Ax ≥ b).
    -- We now construct a dual-optimal u with u_{i₀} > 0 via Farkas.
    push_neg at hCaseA
    -- hCaseA : ∀ x, (Ax ≥ b) → (x ≥ 0) → (⟨c,x⟩ = v) → (Ax)_{i₀} ≤ b_{i₀}
    -- Encode "primal-optimal" as "primal-feasible + ⟨c, x⟩ ≤ v"; combined
    -- with weak duality (⟨c, x⟩ ≥ v), this is "= v".
    have hCaseA' : ∀ x : Fin n → 𝕜,
        (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) →
          -b i₀ ≤ ∑ j, (-A i₀ j) * x j := by
      intro x hx
      obtain ⟨hxA, hxnn, hcx_le⟩ := (optAug_feasible_iff A b c v x).mp hx
      -- Weak duality forces ⟨c, x⟩ ≥ ⟨u₀, b⟩ = v.
      have hcx_ge : v ≤ ∑ j, c j * x j := by
        have hwd := lp_weak_duality A b c hxA hxnn hu₀
        linarith [hu₀_val]
      have hcx_eq : ∑ j, c j * x j = v := le_antisymm hcx_le hcx_ge
      have hAi₀ := hCaseA x hxA hxnn hcx_eq
      have hsum_neg : (∑ j, -A i₀ j * x j) = -(∑ j, A i₀ j * x j) := by
        simp [Finset.sum_neg_distrib, neg_mul]
      linarith [hsum_neg]
    -- Apply Farkas. First, feasibility of the augmented system:
    have hAug_feas : EconCSLib.LinearAlgebra.IsFeasible (optAugA A c) (optAugB b v) :=
      ⟨x₀, (optAug_feasible_iff A b c v x₀).mpr ⟨hx₀A, hx₀nn, hx₀_val.le⟩⟩
    -- Farkas yields the certificate.
    have hCert :=
      (EconCSLib.LinearAlgebra.farkas_lemma (optAugA A c) (optAugB b v)
        (fun j => -A i₀ j) (-b i₀) hAug_feas).mp hCaseA'
    obtain ⟨w, hw_nn, hw_col, hw_b⟩ := hCert
    -- Decompose w into (μ, ν, λ) over (I, Fin n, Unit).
    set μ : I → 𝕜 := fun i => w (Sum.inl (Sum.inl i)) with hμ_def
    set ν : Fin n → 𝕜 := fun j' => w (Sum.inl (Sum.inr j')) with hν_def
    set lam : 𝕜 := w (Sum.inr ()) with hlam_def
    have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hw_nn (Sum.inl (Sum.inl i))
    have hν_nn : ∀ j', 0 ≤ ν j' := fun j' => hw_nn (Sum.inl (Sum.inr j'))
    have hlam_nn : 0 ≤ lam := hw_nn (Sum.inr ())
    -- Helper: reduce the OptAugRow sum to its three components.
    have sum_split : ∀ (f : OptAugRow I n → 𝕜),
        (∑ idx, f idx) = (∑ i, f (Sum.inl (Sum.inl i)))
          + (∑ j', f (Sum.inl (Sum.inr j'))) + f (Sum.inr ()) := by
      intro f
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hunit : (∑ u : Unit, f (Sum.inr u)) = f (Sum.inr ()) := by
        rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
      rw [hunit]
    -- Translate the column condition into `(μ + e_{i₀})ᵀ A + ν - lam c = -A i₀`.
    have hcol : ∀ j, (∑ i, μ i * A i j) + ν j - lam * c j = -A i₀ j := by
      intro j
      have h := hw_col j
      rw [sum_split] at h
      simp only [optAugA_inl_inl, optAugA_inl_inr, optAugA_inr, mul_ite, mul_one,
                 mul_zero, Fintype.sum_ite_eq] at h
      linarith [h]
    -- Translate the RHS condition: ⟨μ, b⟩ - lam * v ≥ -b_{i₀}.
    have hb : (∑ i, μ i * b i) - lam * v ≥ -b i₀ := by
      have h := hw_b
      rw [sum_split] at h
      simp only [optAugB_inl_inl, optAugB_inl_inr, mul_zero, Finset.sum_const_zero,
                 optAugB_inr] at h
      linarith [h]
    -- Now case-split on lam.
    by_cases hlam_pos : 0 < lam
    · -- Sub-case B.1: lam > 0. Set u = (μ + e_{i₀}) / lam.
      refine ⟨x₀, fun i => (μ i + (if i = i₀ then 1 else 0)) / lam, hx₀A, hx₀nn, ?_, hx₀_val,
              ?_, ?_⟩
      · -- DualFeasible
        refine ⟨?_, ?_⟩
        · intro i
          have hsum_nn : 0 ≤ μ i + (if i = i₀ then 1 else 0) := by
            have : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by
              split_ifs <;> simp
            linarith [hμ_nn i]
          exact div_nonneg hsum_nn hlam_pos.le
        · intro j
          -- (∑ i, (μ_i + e_{i₀,i}) / lam * A i j) ≤ c j.
          have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) ≤ lam * c j := by
            -- From hcol: ∑ i μ_i A_ij + ν_j - lam c_j = -A_{i₀,j}
            -- Rearrange: ∑ i (μ_i + e_{i₀,i}) A_ij = lam c_j - ν_j ≤ lam c_j
            have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, μ i * A i j) + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
              simp [Fintype.sum_ite_eq]
            have hsplit2 : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, μ i * A i j) + A i₀ j := by rw [hsplit, hsel]
            have hreorg : (∑ i, μ i * A i j) + A i₀ j = lam * c j - ν j := by linarith [hcol j]
            rw [hsplit2, hreorg]
            linarith [hν_nn j]
          rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * A i j)
              = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [div_le_iff₀ hlam_pos]; linarith
      · -- ⟨u, b⟩ = v: equals from ≥ v (Farkas) and ≤ v (weak duality).
        have hub_ge_v : v ≤ ∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i := by
          -- (⟨μ, b⟩ + b_{i₀}) / lam ≥ v from hb (since ⟨μ, b⟩ - lam v ≥ -b_{i₀}).
          have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i) ≥ lam * v := by
            have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i)
                = (∑ i, μ i * b i) + (∑ i, (if i = i₀ then 1 else 0) * b i) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * b i) = b i₀ := by
              simp [Fintype.sum_ite_eq]
            rw [hsplit, hsel]; linarith [hb]
          rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i)
              = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * b i) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [le_div_iff₀ hlam_pos]; linarith
        have hub_le_v : (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * b i) ≤ v := by
          have hu'_du : DualFeasible A c (fun i => (μ i + (if i = i₀ then 1 else 0)) / lam) := by
            refine ⟨?_, ?_⟩
            · intro i
              have hsum_nn : 0 ≤ μ i + (if i = i₀ then 1 else 0) := by
                have : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by
                  split_ifs <;> simp
                linarith [hμ_nn i]
              exact div_nonneg hsum_nn hlam_pos.le
            · intro j
              have hkey : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) ≤ lam * c j := by
                have hsplit : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                    = (∑ i, μ i * A i j) + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl (fun i _ => ?_); ring
                have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
                  simp [Fintype.sum_ite_eq]
                have hsplit2 : (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j)
                    = (∑ i, μ i * A i j) + A i₀ j := by rw [hsplit, hsel]
                have hreorg : (∑ i, μ i * A i j) + A i₀ j = lam * c j - ν j := by linarith [hcol j]
                rw [hsplit2, hreorg]
                linarith [hν_nn j]
              rw [show (∑ i, (μ i + (if i = i₀ then 1 else 0)) / lam * A i j)
                  = (∑ i, (μ i + (if i = i₀ then 1 else 0)) * A i j) / lam from by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl (fun i _ => ?_); ring]
              rw [div_le_iff₀ hlam_pos]; linarith
          have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
          linarith [hx₀_val]
        linarith
      · -- (Ax₀ - b)_{i₀} + u_{i₀} > 0.
        show 0 < (∑ j, A i₀ j * x₀ j - b i₀) + (μ i₀ + (if i₀ = i₀ then 1 else 0)) / lam
        have hu_i₀_pos : 0 < (μ i₀ + (if i₀ = i₀ then 1 else 0)) / lam := by
          have : μ i₀ + (if i₀ = i₀ then (1 : 𝕜) else 0) ≥ 1 := by
            simp; linarith [hμ_nn i₀]
          exact div_pos (by linarith) hlam_pos
        have hAx_nn : 0 ≤ ∑ j, A i₀ j * x₀ j - b i₀ := by linarith [hx₀A i₀]
        linarith
    · -- Sub-case B.2: lam ≤ 0 (i.e., lam = 0 since lam ≥ 0).
      push_neg at hlam_pos
      have hlam_zero : lam = 0 := le_antisymm hlam_pos hlam_nn
      -- u' = u₀ + (μ + e_{i₀}).
      refine ⟨x₀, fun i => u₀ i + μ i + (if i = i₀ then 1 else 0), hx₀A, hx₀nn, ?_, hx₀_val,
              ?_, ?_⟩
      · -- DualFeasible
        refine ⟨?_, ?_⟩
        · intro i
          have h1 : 0 ≤ u₀ i := hu₀.1 i
          have h2 : 0 ≤ μ i := hμ_nn i
          have h3 : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by split_ifs <;> simp
          linarith
        · intro j
          -- ((u₀)ᵀA)_j + ((μ + e_{i₀})ᵀA)_j ≤ c_j + 0 = c_j (since lam = 0).
          have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
          have hcol_j := hcol j
          rw [hlam_zero] at hcol_j
          -- hcol_j : (∑ i, μ i * A i j) + ν j - 0 = -A i₀ j
          --        i.e., (∑ i, μ i * A i j) = -A i₀ j - ν j ≤ -A i₀ j
          have h_μA_le : (∑ i, μ i * A i j) + A i₀ j ≤ 0 := by linarith [hν_nn j]
          have hsplit : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * A i j)
              = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j)
                + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
            simp [Fintype.sum_ite_eq]
          rw [hsplit, hsel]
          linarith
      · -- ⟨u', b⟩ = v.
        have hub_split : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * b i)
            = (∑ i, u₀ i * b i) + (∑ i, μ i * b i)
              + (∑ i, (if i = i₀ then 1 else 0) * b i) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        have hsel : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * b i) = b i₀ := by
          simp [Fintype.sum_ite_eq]
        rw [hub_split, hsel]
        -- From hb with lam = 0: ⟨μ, b⟩ ≥ -b_{i₀}, i.e., ⟨μ, b⟩ + b_{i₀} ≥ 0.
        have hμb_ge : (∑ i, μ i * b i) + b i₀ ≥ 0 := by
          rw [hlam_zero] at hb; linarith
        -- Apply weak duality on the new u' to get ⟨u', b⟩ ≤ v.
        have hu'_du : DualFeasible A c (fun i => u₀ i + μ i + (if i = i₀ then 1 else 0)) := by
          refine ⟨?_, ?_⟩
          · intro i
            have h1 : 0 ≤ u₀ i := hu₀.1 i
            have h2 : 0 ≤ μ i := hμ_nn i
            have h3 : 0 ≤ (if i = i₀ then (1 : 𝕜) else 0) := by split_ifs <;> simp
            linarith
          · intro j
            have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
            have hcol_j := hcol j
            rw [hlam_zero] at hcol_j
            have h_μA_le : (∑ i, μ i * A i j) + A i₀ j ≤ 0 := by linarith [hν_nn j]
            have hsplit : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * A i j)
                = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j)
                  + (∑ i, (if i = i₀ then 1 else 0) * A i j) := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            have hsel2 : (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * A i j) = A i₀ j := by
              simp [Fintype.sum_ite_eq]
            rw [hsplit, hsel2]
            linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        -- hwd : ∑ i, u' i * b i ≤ ∑ j, c j * x₀ j = v
        have hwd' : (∑ i, (u₀ i + μ i + (if i = i₀ then 1 else 0)) * b i) ≤ v := by
          have := hwd
          rw [hx₀_val] at this; exact this
        rw [hub_split, hsel] at hwd'
        linarith [hu₀_val]
      · -- (Ax₀ - b)_{i₀} + u'_{i₀} > 0.
        have hu'_i₀ : (u₀ i₀ + μ i₀ + (if i₀ = i₀ then 1 else 0)) ≥ 1 := by
          have h1 : 0 ≤ u₀ i₀ := hu₀.1 i₀
          have h2 : 0 ≤ μ i₀ := hμ_nn i₀
          simp; linarith
        have hAx_nn : 0 ≤ ∑ j, A i₀ j * x₀ j - b i₀ := by linarith [hx₀A i₀]
        linarith

/-! ### Per-column dichotomy

For each fixed column `j₀`, there exists an optimal primal-dual pair
`(x, u)` with the column complementarity sum `x_{j₀} + (c - uᵀA)_{j₀}`
strictly positive.

We reuse the **primal** augmented system `optAugA`/`optAugB` (so the
variable type stays `Fin n` as required by `farkas_lemma`), with cost
vector `-e_{j₀}` on the primal-feasibility set:

* **Case A**: some primal-optimal `x` has `x_{j₀} > 0`. Pair with any
  dual-optimal `u`.
* **Case B**: every primal-optimal `x` has `x_{j₀} = 0`. Apply Farkas
  to the bound implication `-x_{j₀} ≥ 0` on the augmented system; the
  certificate yields a dual-optimal `u` with `(c - uᵀA)_{j₀} > 0`.
-/

/-- **Per-column strict-CS witness**: for each column `j₀`, there exists
an optimal primal-dual pair with `x_{j₀} + (c - uᵀA)_{j₀} > 0`. -/
theorem exists_col_strict_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v)
    (j₀ : Fin n) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      0 < x j₀ + (c j₀ - ∑ i, u i * A i j₀) := by
  classical
  by_cases hCaseA : ∃ x : Fin n → 𝕜,
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
        (∑ j, c j * x j = v) ∧ (0 < x j₀)
  · obtain ⟨x, hxA, hxnn, hcx, hstrict⟩ := hCaseA
    refine ⟨x, u₀, hxA, hxnn, hu₀, hcx, hu₀_val, ?_⟩
    have hu₀_slack : 0 ≤ c j₀ - ∑ i, u₀ i * A i j₀ := by linarith [hu₀.2 j₀]
    linarith
  · push_neg at hCaseA
    have hCaseA' : ∀ x : Fin n → 𝕜,
        (∀ idx, optAugB b v idx ≤ ∑ j, optAugA A c idx j * x j) →
          (0 : 𝕜) ≤ ∑ j, (if j = j₀ then (-1 : 𝕜) else 0) * x j := by
      intro x hx
      obtain ⟨hxA, hxnn, hcx_le⟩ := (optAug_feasible_iff A b c v x).mp hx
      have hcx_ge : v ≤ ∑ j, c j * x j := by
        have hwd := lp_weak_duality A b c hxA hxnn hu₀
        linarith [hu₀_val]
      have hcx_eq : ∑ j, c j * x j = v := le_antisymm hcx_le hcx_ge
      have hxj₀_le : x j₀ ≤ 0 := hCaseA x hxA hxnn hcx_eq
      have hsel : (∑ j, (if j = j₀ then (-1 : 𝕜) else 0) * x j) = -x j₀ := by
        simp [Fintype.sum_ite_eq, ite_mul, neg_mul, one_mul, zero_mul]
      linarith [hsel]
    have hAug_feas : EconCSLib.LinearAlgebra.IsFeasible (optAugA A c) (optAugB b v) :=
      ⟨x₀, (optAug_feasible_iff A b c v x₀).mpr ⟨hx₀A, hx₀nn, hx₀_val.le⟩⟩
    have hCert :=
      (EconCSLib.LinearAlgebra.farkas_lemma (optAugA A c) (optAugB b v)
        (fun j => if j = j₀ then (-1 : 𝕜) else 0) 0 hAug_feas).mp hCaseA'
    obtain ⟨w, hw_nn, hw_col, hw_b⟩ := hCert
    set μ : I → 𝕜 := fun i => w (Sum.inl (Sum.inl i)) with hμ_def
    set ν : Fin n → 𝕜 := fun j' => w (Sum.inl (Sum.inr j')) with hν_def
    set lam : 𝕜 := w (Sum.inr ()) with hlam_def
    have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hw_nn (Sum.inl (Sum.inl i))
    have hν_nn : ∀ j', 0 ≤ ν j' := fun j' => hw_nn (Sum.inl (Sum.inr j'))
    have hlam_nn : 0 ≤ lam := hw_nn (Sum.inr ())
    have sum_split : ∀ (f : OptAugRow I n → 𝕜),
        (∑ idx, f idx) = (∑ i, f (Sum.inl (Sum.inl i)))
          + (∑ j', f (Sum.inl (Sum.inr j'))) + f (Sum.inr ()) := by
      intro f
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have hunit : (∑ u : Unit, f (Sum.inr u)) = f (Sum.inr ()) := by
        rw [show (Finset.univ : Finset Unit) = {()} from rfl, Finset.sum_singleton]
      rw [hunit]
    have hcol : ∀ j, (∑ i, μ i * A i j) + ν j - lam * c j = (if j = j₀ then (-1 : 𝕜) else 0) := by
      intro j
      have h := hw_col j
      rw [sum_split] at h
      simp only [optAugA_inl_inl, optAugA_inl_inr, optAugA_inr, mul_ite, mul_one,
                 mul_zero, Fintype.sum_ite_eq] at h
      linarith [h]
    have hb : (∑ i, μ i * b i) - lam * v ≥ 0 := by
      have h := hw_b
      rw [sum_split] at h
      simp only [optAugB_inl_inl, optAugB_inl_inr, mul_zero, Finset.sum_const_zero,
                 optAugB_inr] at h
      linarith [h]
    by_cases hlam_pos : 0 < lam
    · -- Sub-case B.1: lam > 0. Set u = μ / lam.
      refine ⟨x₀, fun i => μ i / lam, hx₀A, hx₀nn, ?_, hx₀_val, ?_, ?_⟩
      · -- DualFeasible
        refine ⟨fun i => div_nonneg (hμ_nn i) hlam_pos.le, ?_⟩
        intro j
        have hkey : (∑ i, μ i * A i j) ≤ lam * c j := by
          have hcol_j := hcol j
          by_cases hjj : j = j₀
          · subst hjj
            simp at hcol_j
            linarith [hν_nn j]
          · simp [hjj] at hcol_j
            linarith [hν_nn j]
        rw [show (∑ i, μ i / lam * A i j) = (∑ i, μ i * A i j) / lam from by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring]
        rw [div_le_iff₀ hlam_pos]; linarith
      · -- ⟨u, b⟩ = v.
        have hub_ge_v : v ≤ ∑ i, μ i / lam * b i := by
          have hkey : (∑ i, μ i * b i) ≥ lam * v := by linarith
          rw [show (∑ i, μ i / lam * b i) = (∑ i, μ i * b i) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [le_div_iff₀ hlam_pos]; linarith
        have hu'_du : DualFeasible A c (fun i => μ i / lam) := by
          refine ⟨fun i => div_nonneg (hμ_nn i) hlam_pos.le, ?_⟩
          intro j
          have hkey : (∑ i, μ i * A i j) ≤ lam * c j := by
            have hcol_j := hcol j
            by_cases hjj : j = j₀
            · subst hjj
              simp at hcol_j
              linarith [hν_nn j]
            · simp [hjj] at hcol_j
              linarith [hν_nn j]
          rw [show (∑ i, μ i / lam * A i j) = (∑ i, μ i * A i j) / lam from by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring]
          rw [div_le_iff₀ hlam_pos]; linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        linarith [hx₀_val]
      · -- (c - u'ᵀA)_{j₀} > 0 + x₀_{j₀} ≥ 0.
        show 0 < x₀ j₀ + (c j₀ - ∑ i, μ i / lam * A i j₀)
        have hcol_j₀ : (∑ i, μ i * A i j₀) = lam * c j₀ - ν j₀ - 1 := by
          have h := hcol j₀
          simp at h
          linarith
        have hsum_div : (∑ i, μ i / lam * A i j₀) = (∑ i, μ i * A i j₀) / lam := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [hsum_div, hcol_j₀]
        have hx₀_j₀_nn : 0 ≤ x₀ j₀ := hx₀nn j₀
        have hν_nn_j₀ : 0 ≤ ν j₀ := hν_nn j₀
        have hslack_pos : 0 < c j₀ - (lam * c j₀ - ν j₀ - 1) / lam := by
          have heq : c j₀ - (lam * c j₀ - ν j₀ - 1) / lam = (ν j₀ + 1) / lam := by
            field_simp; ring
          rw [heq]
          exact div_pos (by linarith) hlam_pos
        linarith
    · -- Sub-case B.2: lam = 0.
      push_neg at hlam_pos
      have hlam_zero : lam = 0 := le_antisymm hlam_pos hlam_nn
      refine ⟨x₀, fun i => u₀ i + μ i, hx₀A, hx₀nn, ?_, hx₀_val, ?_, ?_⟩
      · -- DualFeasible
        refine ⟨fun i => by linarith [hu₀.1 i, hμ_nn i], ?_⟩
        intro j
        have hcol_j := hcol j
        rw [hlam_zero] at hcol_j
        have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
        by_cases hjj : j = j₀
        · rw [hjj] at hcol_j
          simp at hcol_j
          have hμA_neg : (∑ i, μ i * A i j₀) ≤ -1 := by linarith [hν_nn j₀]
          have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
              = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          rw [hjj, hsplit]; linarith [hu₀.2 j₀]
        · simp [hjj] at hcol_j
          have hμA_nn : (∑ i, μ i * A i j) ≤ 0 := by linarith [hν_nn j]
          have hsplit : (∑ i, (u₀ i + μ i) * A i j)
              = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_); ring
          rw [hsplit]; linarith
      · -- ⟨u', b⟩ = v.
        have hub_split : (∑ i, (u₀ i + μ i) * b i)
            = (∑ i, u₀ i * b i) + (∑ i, μ i * b i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        have hμb_nn : (∑ i, μ i * b i) ≥ 0 := by rw [hlam_zero] at hb; linarith
        have hu'_du : DualFeasible A c (fun i => u₀ i + μ i) := by
          refine ⟨fun i => by linarith [hu₀.1 i, hμ_nn i], ?_⟩
          intro j
          have hcol_j := hcol j
          rw [hlam_zero] at hcol_j
          have h_u₀A : (∑ i, u₀ i * A i j) ≤ c j := hu₀.2 j
          by_cases hjj : j = j₀
          · rw [hjj] at hcol_j
            simp at hcol_j
            have hμA_neg : (∑ i, μ i * A i j₀) ≤ -1 := by linarith [hν_nn j₀]
            have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
                = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            rw [hjj, hsplit]; linarith [hu₀.2 j₀]
          · simp [hjj] at hcol_j
            have hμA_nn : (∑ i, μ i * A i j) ≤ 0 := by linarith [hν_nn j]
            have hsplit : (∑ i, (u₀ i + μ i) * A i j)
                = (∑ i, u₀ i * A i j) + (∑ i, μ i * A i j) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
            rw [hsplit]; linarith
        have hwd := lp_weak_duality A b c hx₀A hx₀nn hu'_du
        rw [hub_split]
        linarith [hx₀_val, hu₀_val]
      · -- (c - u'ᵀA)_{j₀} > 0.
        show 0 < x₀ j₀ + (c j₀ - ∑ i, (u₀ i + μ i) * A i j₀)
        have hcol_j₀ : (∑ i, μ i * A i j₀) = -1 - ν j₀ := by
          have h := hcol j₀
          simp at h
          rw [hlam_zero] at h; linarith
        have hsplit : (∑ i, (u₀ i + μ i) * A i j₀)
            = (∑ i, u₀ i * A i j₀) + (∑ i, μ i * A i j₀) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
        rw [hsplit, hcol_j₀]
        have h_u₀A : (∑ i, u₀ i * A i j₀) ≤ c j₀ := hu₀.2 j₀
        have hx₀_j₀_nn : 0 ≤ x₀ j₀ := hx₀nn j₀
        have hν_nn_j₀ : 0 ≤ ν j₀ := hν_nn j₀
        linarith

/-! ### Strong complementarity: main theorem

Given an optimal primal-dual pair `(x₀, u₀)` with common value `v`, the
per-index dichotomies produce `Fintype.card I + n` witness pairs, one
strict at each row and each column. Convex combination (averaging)
preserves optimality and gives a single pair strict at every index.
-/

/-- **LP Strong Complementarity** [MFoGT, Section 2.8, Exercise 11]:
given an optimal primal-dual pair `(x₀, u₀)` with common value `v`,
there exists an optimal pair `(x*, u*)` such that for **every** row
`i ∈ I` and column `j ∈ Fin n`, the row complementarity sum
`(Ax* - b)_i + u*_i` and the column complementarity sum
`x*_j + (c - u*ᵀA)_j` are strictly positive. Combined with weak
complementary slackness, this is the strict biconditional form. -/
theorem exists_strong_complementary_pair
    (A : I → Fin n → 𝕜) (b : I → 𝕜) (c : Fin n → 𝕜) (v : 𝕜)
    (hN_pos : (0 : 𝕜) < ((Fintype.card I + n : ℕ) : 𝕜))
    {x₀ : Fin n → 𝕜}
    (hx₀A : ∀ i, b i ≤ ∑ j, A i j * x₀ j)
    (hx₀nn : ∀ j, 0 ≤ x₀ j) (hx₀_val : ∑ j, c j * x₀ j = v)
    {u₀ : I → 𝕜} (hu₀ : DualFeasible A c u₀) (hu₀_val : ∑ i, u₀ i * b i = v) :
    ∃ (x : Fin n → 𝕜) (u : I → 𝕜),
      (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j) ∧
      DualFeasible A c u ∧
      (∑ j, c j * x j = v) ∧ (∑ i, u i * b i = v) ∧
      (∀ i, 0 < (∑ j, A i j * x j - b i) + u i) ∧
      (∀ j, 0 < x j + (c j - ∑ i, u i * A i j)) := by
  classical
  -- Skolemise per-row and per-column witnesses.
  have row_wits : ∀ i₀ : I, _ := fun i₀ =>
    exists_row_strict_pair A b c v hx₀A hx₀nn hx₀_val hu₀ hu₀_val i₀
  have col_wits : ∀ j₀ : Fin n, _ := fun j₀ =>
    exists_col_strict_pair A b c v hx₀A hx₀nn hx₀_val hu₀ hu₀_val j₀
  choose xR uR hxR_A hxR_nn huR_du hxR_cx huR_ub hR_strict using row_wits
  choose xC uC hxC_A hxC_nn huC_du hxC_cx huC_ub hC_strict using col_wits
  -- Cast N to 𝕜.
  set N : 𝕜 := ((Fintype.card I + n : ℕ) : 𝕜) with hN_def
  have hN_ne : N ≠ 0 := hN_pos.ne'
  -- Average x and u over all witnesses.
  set x_avg : Fin n → 𝕜 :=
    fun j => ((∑ i, xR i j) + (∑ j', xC j' j)) / N with hx_avg_def
  set u_avg : I → 𝕜 :=
    fun i => ((∑ i', uR i' i) + (∑ j, uC j i)) / N with hu_avg_def
  -- Cardinality identity.
  have hN_card : (Fintype.card I : 𝕜) + (n : 𝕜) = N := by
    rw [hN_def]; push_cast; ring
  -- Key linearity identities for Ax_avg, c·x_avg, u_avgᵀA, u_avg·b.
  have hAx_avg : ∀ i, (∑ j, A i j * x_avg j)
      = ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)) / N := by
    intro i
    simp only [hx_avg_def, mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ j, A i j * ((∑ i', xR i' j) + (∑ j', xC j' j)))
        = (∑ j, ∑ i', A i j * xR i' j) + (∑ j, ∑ j', A i j * xC j' j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun j j' => A i j * xC j' j)]
  have hcx_avg : (∑ j, c j * x_avg j)
      = ((∑ i', ∑ j, c j * xR i' j) + (∑ j', ∑ j, c j * xC j' j)) / N := by
    simp only [hx_avg_def, mul_div_assoc']
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ j, c j * ((∑ i', xR i' j) + (∑ j', xC j' j)))
        = (∑ j, ∑ i', c j * xR i' j) + (∑ j, ∑ j', c j * xC j' j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun j j' => c j * xC j' j)]
  have huA_avg : ∀ j, (∑ i, u_avg i * A i j)
      = ((∑ i', ∑ i, uR i' i * A i j) + (∑ j', ∑ i, uC j' i * A i j)) / N := by
    intro j
    simp only [hu_avg_def, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ i, ((∑ i', uR i' i) + (∑ j', uC j' i)) * A i j)
        = (∑ i, ∑ i', uR i' i * A i j) + (∑ i, ∑ j', uC j' i * A i j) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun i j' => uC j' i * A i j)]
  have hub_avg : (∑ i, u_avg i * b i)
      = ((∑ i', ∑ i, uR i' i * b i) + (∑ j', ∑ i, uC j' i * b i)) / N := by
    simp only [hu_avg_def, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    rw [show (∑ i, ((∑ i', uR i' i) + (∑ j', uC j' i)) * b i)
        = (∑ i, ∑ i', uR i' i * b i) + (∑ i, ∑ j', uC j' i * b i) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]]
    rw [Finset.sum_comm, @Finset.sum_comm _ _ _ _ Finset.univ Finset.univ
          (fun i j' => uC j' i * b i)]
  refine ⟨x_avg, u_avg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) (Ax_avg)_i ≥ b_i.
  · intro i
    rw [hAx_avg i, le_div_iff₀ hN_pos]
    -- N * b_i ≤ ∑_k (Ax_k)_i.
    rw [← hN_card]
    have hR : ∀ i', (∑ j, A i j * xR i' j) ≥ b i := fun i' => hxR_A i' i
    have hC : ∀ j', (∑ j, A i j * xC j' j) ≥ b i := fun j' => hxC_A j' i
    have hRs : (∑ i', ∑ j, A i j * xR i' j) ≥ Fintype.card I * b i := by
      calc (∑ i', ∑ j, A i j * xR i' j) ≥ ∑ _i' : I, b i :=
             Finset.sum_le_sum (fun i' _ => hR i')
        _ = Fintype.card I * b i := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hCs : (∑ j', ∑ j, A i j * xC j' j) ≥ n * b i := by
      calc (∑ j', ∑ j, A i j * xC j' j) ≥ ∑ _j' : Fin n, b i :=
             Finset.sum_le_sum (fun j' _ => hC j')
        _ = n * b i := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  -- (2) x_avg ≥ 0.
  · intro j
    rw [hx_avg_def]
    apply div_nonneg _ hN_pos.le
    have hRs : 0 ≤ ∑ i, xR i j := Finset.sum_nonneg (fun i _ => hxR_nn i j)
    have hCs : 0 ≤ ∑ j', xC j' j := Finset.sum_nonneg (fun j' _ => hxC_nn j' j)
    linarith
  -- (3) DualFeasible u_avg.
  · refine ⟨?_, ?_⟩
    · intro i
      rw [hu_avg_def]
      apply div_nonneg _ hN_pos.le
      have hRs : 0 ≤ ∑ i', uR i' i := Finset.sum_nonneg (fun i' _ => (huR_du i').1 i)
      have hCs : 0 ≤ ∑ j', uC j' i := Finset.sum_nonneg (fun j' _ => (huC_du j').1 i)
      linarith
    · intro j
      rw [huA_avg j, div_le_iff₀ hN_pos]
      rw [← hN_card]
      have hR : ∀ i', (∑ i, uR i' i * A i j) ≤ c j := fun i' => (huR_du i').2 j
      have hC : ∀ j', (∑ i, uC j' i * A i j) ≤ c j := fun j' => (huC_du j').2 j
      have hRs : (∑ i', ∑ i, uR i' i * A i j) ≤ Fintype.card I * c j := by
        calc (∑ i', ∑ i, uR i' i * A i j) ≤ ∑ _i' : I, c j :=
               Finset.sum_le_sum (fun i' _ => hR i')
          _ = Fintype.card I * c j := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hCs : (∑ j', ∑ i, uC j' i * A i j) ≤ n * c j := by
        calc (∑ j', ∑ i, uC j' i * A i j) ≤ ∑ _j' : Fin n, c j :=
               Finset.sum_le_sum (fun j' _ => hC j')
          _ = n * c j := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith
  -- (4) ⟨c, x_avg⟩ = v.
  · rw [hcx_avg]
    have hR : ∀ i', (∑ j, c j * xR i' j) = v := fun i' => hxR_cx i'
    have hC : ∀ j', (∑ j, c j * xC j' j) = v := fun j' => hxC_cx j'
    rw [show (∑ i', ∑ j, c j * xR i' j) = Fintype.card I * v from by
      have h1 : (∑ i', ∑ j, c j * xR i' j) = ∑ _i' : I, v :=
        Finset.sum_congr rfl (fun i' _ => hR i')
      rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [show (∑ j', ∑ j, c j * xC j' j) = n * v from by
      have h1 : (∑ j', ∑ j, c j * xC j' j) = ∑ _j' : Fin n, v :=
        Finset.sum_congr rfl (fun j' _ => hC j')
      rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [show ((Fintype.card I : 𝕜) * v + n * v) = N * v from by
      rw [← hN_card]; ring]
    field_simp
  -- (5) ⟨u_avg, b⟩ = v.
  · rw [hub_avg]
    have hR : ∀ i', (∑ i, uR i' i * b i) = v := fun i' => huR_ub i'
    have hC : ∀ j', (∑ i, uC j' i * b i) = v := fun j' => huC_ub j'
    rw [show (∑ i', ∑ i, uR i' i * b i) = Fintype.card I * v from by
      have h1 : (∑ i', ∑ i, uR i' i * b i) = ∑ _i' : I, v :=
        Finset.sum_congr rfl (fun i' _ => hR i')
      rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [show (∑ j', ∑ i, uC j' i * b i) = n * v from by
      have h1 : (∑ j', ∑ i, uC j' i * b i) = ∑ _j' : Fin n, v :=
        Finset.sum_congr rfl (fun j' _ => hC j')
      rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [show ((Fintype.card I : 𝕜) * v + n * v) = N * v from by
      rw [← hN_card]; ring]
    field_simp
  -- (6) ∀ i, (Ax_avg - b)_i + u_avg_i > 0.
  · intro i
    have hAx := hAx_avg i
    have hu : u_avg i = ((∑ i', uR i' i) + (∑ j', uC j' i)) / N := hu_avg_def ▸ rfl
    rw [hAx, hu]
    rw [show ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)) / N - b i
        + ((∑ i', uR i' i) + (∑ j', uC j' i)) / N
      = ((∑ i', ∑ j, A i j * xR i' j) + (∑ j', ∑ j, A i j * xC j' j)
         + ((∑ i', uR i' i) + (∑ j', uC j' i)) - N * b i) / N from by
      field_simp; ring]
    apply div_pos _ hN_pos
    rw [show N * b i = (Fintype.card I : 𝕜) * b i + (n : 𝕜) * b i from by
      rw [← hN_card]; ring]
    have hR_term : ∀ i', 0 ≤ ((∑ j, A i j * xR i' j) - b i + uR i' i) := fun i' => by
      linarith [hxR_A i' i, (huR_du i').1 i]
    have hC_term : ∀ j', 0 ≤ ((∑ j, A i j * xC j' j) - b i + uC j' i) := fun j' => by
      linarith [hxC_A j' i, (huC_du j').1 i]
    have hR_strict_i : 0 < ((∑ j, A i j * xR i j) - b i + uR i i) := hR_strict i
    have hR_sum_id : (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i))
        = (∑ i', ∑ j, A i j * xR i' j) + (∑ i', uR i' i) - (Fintype.card I : 𝕜) * b i := by
      rw [show (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i))
          = (∑ i', ((∑ j, A i j * xR i' j) + uR i' i - b i)) from
            Finset.sum_congr rfl (fun i' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ i', ((∑ j, A i j * xR i' j) + uR i' i))
          = (∑ i', ∑ j, A i j * xR i' j) + (∑ i', uR i' i) from
            Finset.sum_add_distrib]
      rw [show (∑ _i' : I, b i) = (Fintype.card I : 𝕜) * b i from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hC_sum_id : (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i))
        = (∑ j', ∑ j, A i j * xC j' j) + (∑ j', uC j' i) - (n : 𝕜) * b i := by
      rw [show (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i))
          = (∑ j', ((∑ j, A i j * xC j' j) + uC j' i - b i)) from
            Finset.sum_congr rfl (fun j' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ j', ((∑ j, A i j * xC j' j) + uC j' i))
          = (∑ j', ∑ j, A i j * xC j' j) + (∑ j', uC j' i) from
            Finset.sum_add_distrib]
      rw [show (∑ _j' : Fin n, b i) = (n : 𝕜) * b i from by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    have hR_sum_pos : 0 < (∑ i', ((∑ j, A i j * xR i' j) - b i + uR i' i)) :=
      Finset.sum_pos' (fun i' _ => hR_term i') ⟨i, Finset.mem_univ _, hR_strict_i⟩
    have hC_sum_nn : 0 ≤ (∑ j', ((∑ j, A i j * xC j' j) - b i + uC j' i)) :=
      Finset.sum_nonneg (fun j' _ => hC_term j')
    linarith [hR_sum_id, hC_sum_id]
  -- (7) ∀ j, x_avg j + (c_j - (u_avgᵀA)_j) > 0.
  · intro j
    have hxj : x_avg j = ((∑ i', xR i' j) + (∑ j'', xC j'' j)) / N := hx_avg_def ▸ rfl
    have huA := huA_avg j
    rw [hxj, huA]
    rw [show ((∑ i', xR i' j) + (∑ j'', xC j'' j)) / N
        + (c j - ((∑ i', ∑ i, uR i' i * A i j) + (∑ j'', ∑ i, uC j'' i * A i j)) / N)
      = (((∑ i', xR i' j) + (∑ j'', xC j'' j)) + N * c j
         - ((∑ i', ∑ i, uR i' i * A i j) + (∑ j'', ∑ i, uC j'' i * A i j))) / N from by
      field_simp; ring]
    apply div_pos _ hN_pos
    rw [show N * c j = (Fintype.card I : 𝕜) * c j + (n : 𝕜) * c j from by
      rw [← hN_card]; ring]
    have hR_term : ∀ i', 0 ≤ (xR i' j + (c j - ∑ i, uR i' i * A i j)) := fun i' => by
      linarith [hxR_nn i' j, (huR_du i').2 j]
    have hC_term : ∀ j'', 0 ≤ (xC j'' j + (c j - ∑ i, uC j'' i * A i j)) := fun j'' => by
      linarith [hxC_nn j'' j, (huC_du j'').2 j]
    have hC_strict_j : 0 < (xC j j + (c j - ∑ i, uC j i * A i j)) := hC_strict j
    have hR_sum_id : (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j)))
        = (∑ i', xR i' j) + (Fintype.card I : 𝕜) * c j - (∑ i', ∑ i, uR i' i * A i j) := by
      rw [show (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j)))
          = (∑ i', (xR i' j + c j - ∑ i, uR i' i * A i j)) from
            Finset.sum_congr rfl (fun i' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ i', (xR i' j + c j)) = (∑ i', xR i' j) + (∑ _i' : I, c j) from
            Finset.sum_add_distrib]
      rw [show (∑ _i' : I, c j) = (Fintype.card I : 𝕜) * c j from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hC_sum_id : (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j)))
        = (∑ j'', xC j'' j) + (n : 𝕜) * c j - (∑ j'', ∑ i, uC j'' i * A i j) := by
      rw [show (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j)))
          = (∑ j'', (xC j'' j + c j - ∑ i, uC j'' i * A i j)) from
            Finset.sum_congr rfl (fun j'' _ => by ring)]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ j'', (xC j'' j + c j)) = (∑ j'', xC j'' j) + (∑ _j'' : Fin n, c j) from
            Finset.sum_add_distrib]
      rw [show (∑ _j'' : Fin n, c j) = (n : 𝕜) * c j from by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    have hR_sum_nn : 0 ≤ (∑ i', (xR i' j + (c j - ∑ i, uR i' i * A i j))) :=
      Finset.sum_nonneg (fun i' _ => hR_term i')
    have hC_sum_pos : 0 < (∑ j'', (xC j'' j + (c j - ∑ i, uC j'' i * A i j))) :=
      Finset.sum_pos' (fun j'' _ => hC_term j'') ⟨j, Finset.mem_univ _, hC_strict_j⟩
    linarith [hR_sum_id, hC_sum_id]

end EconCSLib.LinearProgramming
