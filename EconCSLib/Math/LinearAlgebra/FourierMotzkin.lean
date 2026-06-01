/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# EconCSLib.Math.LinearAlgebra.FourierMotzkin

Formalises the **Theorem of the Alternative** [MFoGT, Section 2.8, Exercise 7]
over any linearly ordered field (`[Field 𝕜] [LinearOrder 𝕜]
[IsStrictOrderedRing 𝕜]`). We prove the `Fin m × Fin n` version directly;
a general `Fintype I` form would transport via `Fintype.equivFin`.

For a finite system of weak linear inequalities `A x ≥ b` with
`A : Fin m → Fin n → 𝕜`, `b : Fin m → 𝕜`, exactly one of:

- the primal set `S = { x : Fin n → 𝕜 | ∀ i, ⟨A i, x⟩ ≥ b i }`, or
- the Farkas certificate set
  `T = { u : Fin m → 𝕜 | u ≥ 0, uᵀA = 0, ⟨u, b⟩ > 0 }`

is nonempty.

## Blueprint

* `docs/knowledge/nodes/core/linear_algebra.theorem_of_alternative.md`
* `docs/knowledge/nodes/core/linear_algebra.theorem_of_alternative.fourier_motzkin.md`
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace EconCSLib.LinearAlgebra

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### The primal feasibility set and Farkas certificate set

We parameterise the row index by an abstract `Fintype I` (rather than `Fin m`)
because the Fourier-Motzkin reduction produces a row index of the form
`I⁰ ⊕ (I⁺ × I⁻)`, which is naturally a `Fintype` but does not stay `Fin m`.
A user typically instantiates `I := Fin m` at the application boundary. -/

/-- Evaluate the LHS of row `i` of the matrix `A : I → Fin n → 𝕜` at the
point `x : Fin n → 𝕜`. -/
def rowEval {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜) (i : I)
    (x : Fin n → 𝕜) : 𝕜 :=
  ∑ j, A i j * x j

/-- Primal feasibility of the system `A x ≥ b`. -/
def IsFeasible {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ x : Fin n → 𝕜, ∀ i, b i ≤ rowEval A i x

/-- `u : I → 𝕜` is a Farkas certificate of infeasibility of `A x ≥ b`. -/
def IsCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) (u : I → 𝕜) : Prop :=
  (∀ i, 0 ≤ u i) ∧
  (∀ j : Fin n, ∑ i, u i * A i j = 0) ∧
  (0 < ∑ i, u i * b i)

/-- Existence of a Farkas certificate. -/
def HasCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ u : I → 𝕜, IsCertificate A b u

/-! ### Disjointness: `IsFeasible` and `HasCertificate` cannot both hold -/

theorem feas_cert_disjoint {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) (hcert : HasCertificate A b) : False := by
  obtain ⟨x, hx⟩ := hfeas
  obtain ⟨u, hu_nn, hu_zero, hu_pos⟩ := hcert
  -- ⟨u, b⟩ ≤ ⟨u, Ax⟩ = ⟨uᵀA, x⟩ = ⟨0, x⟩ = 0 < ⟨u, b⟩.
  have hweighted : ∑ i, u i * b i ≤ ∑ i, u i * rowEval A i x := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hx i) (hu_nn i)
  have hzero : ∑ i, u i * rowEval A i x = 0 := by
    have h1 : ∑ i, u i * rowEval A i x = ∑ i, ∑ j, u i * (A i j * x j) := by
      simp only [rowEval, Finset.mul_sum]
    have h2 : (∑ i, ∑ j, u i * (A i j * x j))
        = ∑ j, ∑ i, u i * A i j * x j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have h3 : (∑ j, ∑ i, u i * A i j * x j)
        = ∑ j, (∑ i, u i * A i j) * x j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    rw [h1, h2, h3]
    apply Finset.sum_eq_zero
    intro j _
    rw [hu_zero j, zero_mul]
  linarith

/-! ### Sign partition of rows by the last-column coefficient

For an `(n+1)`-column matrix `A : I → Fin (n+1) → 𝕜` over a `Fintype` row
index `I`, partition `I` into the three sign-of-`A i (Fin.last n)` cases.
We use `abbrev` so Lean's `Subtype.fintype` instances are transparent.

The generic-`I` formulation (rather than `Fin m`) is needed for the
induction in `theorem_of_alternative_aux`: after FM, the row index becomes
`ZeroRows ⊕ (PosRows × NegRows)`, which is itself a `Fintype` but not a
`Fin _`. -/

variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Rows where the last-column coefficient is zero. -/
abbrev ZeroRows (A : I → Fin (n+1) → 𝕜) : Type _ :=
  { i : I // A i (Fin.last n) = 0 }

/-- Rows where the last-column coefficient is strictly positive. -/
abbrev PosRows (A : I → Fin (n+1) → 𝕜) : Type _ :=
  { i : I // 0 < A i (Fin.last n) }

/-- Rows where the last-column coefficient is strictly negative. -/
abbrev NegRows (A : I → Fin (n+1) → 𝕜) : Type _ :=
  { i : I // A i (Fin.last n) < 0 }

/-- Reduced row index after Fourier-Motzkin elimination of the last column. -/
abbrev FMRowIndex (A : I → Fin (n+1) → 𝕜) : Type _ :=
  ZeroRows A ⊕ (PosRows A × NegRows A)

/-! ### Fourier-Motzkin reduced matrix and RHS

Per blueprint
`docs/knowledge/nodes/core/linear_algebra.theorem_of_alternative.fourier_motzkin.md`:

* zero rows: copy the original row, dropping the last column entry;
* combination rows: for `(p, q) ∈ PosRows × NegRows`, take the nonneg
  combination `αq · row p + βp · row q` with `αq = -A q last > 0` and
  `βp = A p last > 0`, which annihilates the last column. -/

/-- Reduced matrix coefficient. -/
def fmA (A : I → Fin (n+1) → 𝕜) (idx : FMRowIndex A) (j : Fin n) : 𝕜 :=
  match idx with
  | Sum.inl k => A k.val j.castSucc
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc

/-- Reduced right-hand side. -/
def fmB (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜) (idx : FMRowIndex A) : 𝕜 :=
  match idx with
  | Sum.inl k => b k.val
  | Sum.inr ⟨p, q⟩ =>
      (-A q.val (Fin.last n)) * b p.val
        + A p.val (Fin.last n) * b q.val

@[simp] theorem fmA_inl (A : I → Fin (n+1) → 𝕜) (k : ZeroRows A) (j : Fin n) :
    fmA A (Sum.inl k) j = A k.val j.castSucc := rfl

@[simp] theorem fmA_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (j : Fin n) :
    fmA A (Sum.inr (p, q)) j
      = (-A q.val (Fin.last n)) * A p.val j.castSucc
        + A p.val (Fin.last n) * A q.val j.castSucc := rfl

@[simp] theorem fmB_inl (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (k : ZeroRows A) : fmB A b (Sum.inl k) = b k.val := rfl

@[simp] theorem fmB_inr (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (p : PosRows A) (q : NegRows A) :
    fmB A b (Sum.inr (p, q))
      = (-A q.val (Fin.last n)) * b p.val
        + A p.val (Fin.last n) * b q.val := rfl

@[simp] theorem rowEval_def {I : Type*} {n : ℕ} [Fintype I]
    (A : I → Fin n → 𝕜) (i : I) (x : Fin n → 𝕜) :
    rowEval A i x = ∑ j, A i j * x j := rfl

/-! ### Feasibility transfer (`⇒` direction)

If `(x_0, ..., x_n)` satisfies the original `(n+1)`-variable system, then
`(x_0, ..., x_{n-1})` satisfies the reduced `n`-variable system. -/

theorem fm_feasible_of_feasible (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hfeas : IsFeasible A b) : IsFeasible (fmA A) (fmB A b) := by
  obtain ⟨x, hx⟩ := hfeas
  refine ⟨fun j => x j.castSucc, ?_⟩
  intro idx
  -- Split each original row sum into first n + last entry.
  have hsplit : ∀ i : I,
      rowEval A i x
        = (∑ j : Fin n, A i j.castSucc * x j.castSucc)
          + A i (Fin.last n) * x (Fin.last n) := by
    intro i
    rw [rowEval, Fin.sum_univ_castSucc]
  rcases idx with k | ⟨p, q⟩
  · -- Zero-row pass-through.
    have hk := hx k.val
    rw [hsplit, k.property, zero_mul, add_zero] at hk
    simp only [fmB_inl, rowEval_def, fmA_inl]
    exact hk
  · -- Combined-row inequality.
    have hp := hx p.val
    have hq := hx q.val
    rw [hsplit] at hp hq
    have hαq_pos : 0 < -A q.val (Fin.last n) := by linarith [q.property]
    have hβp_pos : 0 < A p.val (Fin.last n) := p.property
    -- αq · (hp stripped) + βp · (hq stripped) gives the combined inequality.
    have hcomb :
        (-A q.val (Fin.last n)) * b p.val
          + A p.val (Fin.last n) * b q.val
        ≤ (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      have hp_strip :
          b p.val - A p.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A p.val j.castSucc * x j.castSucc := by linarith
      have hq_strip :
          b q.val - A q.val (Fin.last n) * x (Fin.last n)
          ≤ ∑ j : Fin n, A q.val j.castSucc * x j.castSucc := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hp_strip hαq_pos.le,
        mul_le_mul_of_nonneg_left hq_strip hβp_pos.le]
    simp only [fmB_inr, rowEval_def, fmA_inr]
    -- Distribute the sum in the goal RHS.
    have hRHS :
        (∑ j : Fin n,
          ((-A q.val (Fin.last n)) * A p.val j.castSucc
            + A p.val (Fin.last n) * A q.val j.castSucc)
            * x j.castSucc)
        = (-A q.val (Fin.last n))
            * (∑ j : Fin n, A p.val j.castSucc * x j.castSucc)
          + A p.val (Fin.last n)
            * (∑ j : Fin n, A q.val j.castSucc * x j.castSucc) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    exact hcomb

/-! ### Reduced-pair lower-upper bound

From the reduced inequality at `(p, q) ∈ PosRows × NegRows`, derive that
the lower bound `L_p(x')` is at most the upper bound `U_q(x')`. This is
the algebraic content of "max lower ≤ min upper" needed to construct
`x_last`. -/

private theorem reduced_pair_ineq
    {A : I → Fin (n+1) → 𝕜} {b : I → 𝕜} {x' : Fin n → 𝕜}
    (hx' : ∀ idx, fmB A b idx ≤ rowEval (fmA A) idx x')
    (p : PosRows A) (q : NegRows A) :
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
    ≤ (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n) := by
  have h_pq := hx' (Sum.inr (p, q))
  simp only [fmB_inr, rowEval_def, fmA_inr] at h_pq
  -- Distribute the sum in h_pq's RHS.
  have hdist :
      (∑ j : Fin n,
        ((-A q.val (Fin.last n)) * A p.val j.castSucc
          + A p.val (Fin.last n) * A q.val j.castSucc) * x' j)
      = (-A q.val (Fin.last n))
          * (∑ j : Fin n, A p.val j.castSucc * x' j)
        + A p.val (Fin.last n)
          * (∑ j : Fin n, A q.val j.castSucc * x' j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hdist] at h_pq
  -- h_pq : (-A q last) · b p + A p last · b q ≤ (-A q last) · Σp + A p last · Σq
  have hβp : 0 < A p.val (Fin.last n) := p.property
  have hαq : 0 < -A q.val (Fin.last n) := by linarith [q.property]
  have hAql_neg : A q.val (Fin.last n) < 0 := q.property
  have hAql_ne : A q.val (Fin.last n) ≠ 0 := ne_of_lt hAql_neg
  -- Convert U_q's denominator (negative) to a positive form.
  set sumP := ∑ j : Fin n, A p.val j.castSucc * x' j with hsumP_def
  set sumQ := ∑ j : Fin n, A q.val j.castSucc * x' j with hsumQ_def
  have hUq_flip :
      (b q.val - sumQ) / A q.val (Fin.last n)
      = -(b q.val - sumQ) / (-A q.val (Fin.last n)) := by
    rw [neg_div_neg_eq]
  rw [hUq_flip]
  rw [div_le_div_iff₀ hβp hαq]
  -- Goal: (b p val - sumP) * (-A q val last) ≤ -(b q val - sumQ) * (A p val last)
  linarith

/-! ### Feasibility transfer (`⇐` direction)

If a solution `x'` of the reduced system exists, construct an `x_last`
such that `Fin.snoc x' x_last` solves the original `(n+1)`-variable
system. -/

theorem feasible_of_fm_feasible (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hred : IsFeasible (fmA A) (fmB A b)) : IsFeasible A b := by
  obtain ⟨x', hx'⟩ := hred
  classical
  -- Per-row lower/upper bounds (defined on subtypes).
  let L : PosRows A → 𝕜 := fun p =>
    (b p.val - ∑ j : Fin n, A p.val j.castSucc * x' j) / A p.val (Fin.last n)
  let U : NegRows A → 𝕜 := fun q =>
    (b q.val - ∑ j : Fin n, A q.val j.castSucc * x' j) / A q.val (Fin.last n)
  -- Choose x_last by case-split on emptiness of PosRows / NegRows.
  let x_last : 𝕜 :=
    if hPos : (Finset.univ : Finset (PosRows A)).Nonempty then
      Finset.univ.sup' hPos L
    else if hNeg : (Finset.univ : Finset (NegRows A)).Nonempty then
      Finset.univ.inf' hNeg U
    else (0 : 𝕜)
  refine ⟨Fin.snoc x' x_last, ?_⟩
  intro i
  -- Decompose original row evaluation: first n + last entry.
  have hsplit : rowEval A i (Fin.snoc x' x_last)
      = (∑ j : Fin n, A i j.castSucc * x' j)
        + A i (Fin.last n) * x_last := by
    rw [rowEval_def, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rcases lt_trichotomy (A i (Fin.last n)) 0 with hlt | heq | hgt
  · -- Negative last-column coefficient: i ∈ NegRows.
    let hiN : NegRows A := ⟨i, hlt⟩
    have hUbound : x_last ≤ U hiN := by
      by_cases hPos : (Finset.univ : Finset (PosRows A)).Nonempty
      · -- x_last = sup' L; need sup' L ≤ U(hiN), i.e., ∀ p, L p ≤ U hiN.
        change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dif_pos hPos]
        apply Finset.sup'_le
        intro p _
        exact reduced_pair_ineq hx' p hiN
      · -- x_last = inf' U (NegRows nonempty since hiN exists).
        have hNeg : (Finset.univ : Finset (NegRows A)).Nonempty :=
          ⟨hiN, Finset.mem_univ _⟩
        change (if h : _ then Finset.univ.sup' h L
                else if h' : _ then Finset.univ.inf' h' U else 0) ≤ U hiN
        rw [dif_neg hPos, dif_pos hNeg]
        exact Finset.inf'_le _ (Finset.mem_univ hiN)
    have hUval : A i (Fin.last n) * U hiN
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      show A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_lt hlt
      field_simp
    have hmul : A i (Fin.last n) * U hiN ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonpos_left hUbound hlt.le
    rw [hsplit]
    linarith
  · -- Zero last-column coefficient: i ∈ ZeroRows.
    let hiZ : ZeroRows A := ⟨i, heq⟩
    have h := hx' (Sum.inl hiZ)
    simp only [fmB_inl, rowEval_def, fmA_inl] at h
    rw [hsplit, heq, zero_mul, add_zero]
    exact h
  · -- Positive last-column coefficient: i ∈ PosRows.
    let hiP : PosRows A := ⟨i, hgt⟩
    have hPos : (Finset.univ : Finset (PosRows A)).Nonempty :=
      ⟨hiP, Finset.mem_univ _⟩
    have hLbound : L hiP ≤ x_last := by
      change L hiP ≤ (if h : _ then Finset.univ.sup' h L
                       else if h' : _ then Finset.univ.inf' h' U else 0)
      rw [dif_pos hPos]
      exact Finset.le_sup' _ (Finset.mem_univ hiP)
    have hLval : A i (Fin.last n) * L hiP
        = b i - ∑ j : Fin n, A i j.castSucc * x' j := by
      show A i (Fin.last n)
          * ((b i - ∑ j : Fin n, A i j.castSucc * x' j) / A i (Fin.last n)) = _
      have : A i (Fin.last n) ≠ 0 := ne_of_gt hgt
      field_simp
    have hmul : A i (Fin.last n) * L hiP ≤ A i (Fin.last n) * x_last :=
      mul_le_mul_of_nonneg_left hLbound hgt.le
    rw [hsplit]
    linarith

/-! ### Certificate lift via the transposed FM matrix

The FM reduction can be encoded as a matrix `L : FMRowIndex A → Fin m → 𝕜`
whose rows are the nonneg coefficients of the original rows feeding into
each reduced row. The Farkas certificate of the reduced system lifts to
the original via `u := L^T u'`, i.e. `u i = ∑ idx, L idx i * u' idx`. -/

/-- The FM lift coefficient `L idx i`: the weight with which original row
`i` enters the reduced row `idx`. -/
def liftCoeff (A : I → Fin (n+1) → 𝕜) (idx : FMRowIndex A) (i : I) : 𝕜 :=
  match idx with
  | Sum.inl k => if k.val = i then 1 else 0
  | Sum.inr (p, q) =>
      (if p.val = i then -A q.val (Fin.last n) else 0)
      + (if q.val = i then A p.val (Fin.last n) else 0)

theorem liftCoeff_inl (A : I → Fin (n+1) → 𝕜) (k : ZeroRows A)
    (i : I) :
    liftCoeff A (Sum.inl k) i = if k.val = i then 1 else 0 := rfl

theorem liftCoeff_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (i : I) :
    liftCoeff A (Sum.inr (p, q)) i
      = (if p.val = i then -A q.val (Fin.last n) else 0)
        + (if q.val = i then A p.val (Fin.last n) else 0) := rfl

/-- The lifted certificate `u i = ∑ idx, L idx i * u'(idx)`. -/
def liftCert (A : I → Fin (n+1) → 𝕜) (u' : FMRowIndex A → 𝕜)
    (i : I) : 𝕜 :=
  ∑ idx, liftCoeff A idx i * u' idx

/-- Pointwise nonneg lift. -/
theorem liftCert_nonneg (A : I → Fin (n+1) → 𝕜) {u' : FMRowIndex A → 𝕜}
    (hu' : ∀ idx, 0 ≤ u' idx) (i : I) : 0 ≤ liftCert A u' i := by
  apply Finset.sum_nonneg
  intro idx _
  apply mul_nonneg _ (hu' idx)
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_inl]; split_ifs <;> norm_num
  · simp only [liftCoeff_inr]
    apply add_nonneg
    · split_ifs with hp
      · linarith [q.property]
      · norm_num
    · split_ifs with hq
      · exact p.property.le
      · norm_num

/-- Inner-product-of-lift: `∑ i, liftCert u' i * g i = ∑ idx, u'(idx) * fmRow_at idx g`,
where the `fmRow_at` value depends on `g` and `idx`. The lemma uses
`Finset.sum_comm` to swap sums and `Finset.sum_ite_eq'` to evaluate the
indicators.

Specialised forms (`liftCert_weighted_A_castSucc`, `liftCert_weighted_A_last`,
`liftCert_weighted_b`) recognise the inner sum as `fmA`/`0`/`fmB`. -/
private theorem liftCert_weighted_sum_swap (A : I → Fin (n+1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) (g : I → 𝕜) :
    ∑ i, liftCert A u' i * g i
    = ∑ idx, u' idx * (∑ i, liftCoeff A idx i * g i) := by
  unfold liftCert
  -- ∑ i, (∑ idx, L idx i * u' idx) * g i
  --   = ∑ i, ∑ idx, L idx i * u' idx * g i
  --   = ∑ idx, ∑ i, L idx i * u' idx * g i
  --   = ∑ idx, u' idx * (∑ i, L idx i * g i)
  rw [show (∑ i, (∑ idx, liftCoeff A idx i * u' idx) * g i)
      = ∑ i, ∑ idx, liftCoeff A idx i * u' idx * g i from ?_,
      Finset.sum_comm]
  · refine Finset.sum_congr rfl ?_
    intro idx _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_mul]

/-- Inner sum at `Sum.inl k` collapses to the picked-out row: `∑ i, L (inl k) i * g i = g k.val`. -/
@[simp] private theorem liftCoeff_weighted_inl (A : I → Fin (n+1) → 𝕜)
    (k : ZeroRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inl k) i * g i = g k.val := by
  classical
  simp only [liftCoeff_inl, ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]

/-- Inner sum at `Sum.inr (p, q)` collapses to the combined row contributions. -/
@[simp] private theorem liftCoeff_weighted_inr (A : I → Fin (n+1) → 𝕜)
    (p : PosRows A) (q : NegRows A) (g : I → 𝕜) :
    ∑ i, liftCoeff A (Sum.inr (p, q)) i * g i
    = (-A q.val (Fin.last n)) * g p.val + A p.val (Fin.last n) * g q.val := by
  classical
  simp only [liftCoeff_inr, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
             Fintype.sum_ite_eq]

/-- Lifted column-zero condition for `j ∈ Fin n`: matches `fmA A · j = 0`. -/
private theorem liftCert_column_zero_castSucc (A : I → Fin (n+1) → 𝕜)
    (b : I → 𝕜) {u' : FMRowIndex A → 𝕜}
    (hu'_zero : ∀ j : Fin n, ∑ idx, u' idx * fmA A idx j = 0) (j : Fin n) :
    ∑ i, liftCert A u' i * A i j.castSucc = 0 := by
  rw [liftCert_weighted_sum_swap]
  -- ∑ idx, u' idx * (∑ i, L idx i * A i j.castSucc) = ∑ idx, u' idx * fmA A idx j
  have : ∀ idx, ∑ i, liftCoeff A idx i * A i j.castSucc = fmA A idx j := by
    intro idx
    rcases idx with k | ⟨p, q⟩
    · simp [liftCoeff_weighted_inl]
    · simp [liftCoeff_weighted_inr]
  simp_rw [this]
  exact hu'_zero j

/-- Lifted column-zero condition for `j = Fin.last n`: holds because the last
column of `L · A` is zero by FM design. -/
private theorem liftCert_column_zero_last (A : I → Fin (n+1) → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * A i (Fin.last n) = 0 := by
  rw [liftCert_weighted_sum_swap]
  apply Finset.sum_eq_zero
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp only [liftCoeff_weighted_inl, k.property, mul_zero]
  · simp only [liftCoeff_weighted_inr]
    -- (-A q last) * A p last + A p last * A q last = 0
    ring

/-- Lifted RHS-positivity: matches `∑ idx, u' idx * fmB idx > 0`. -/
private theorem liftCert_rhs (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (u' : FMRowIndex A → 𝕜) :
    ∑ i, liftCert A u' i * b i = ∑ idx, u' idx * fmB A b idx := by
  rw [liftCert_weighted_sum_swap]
  refine Finset.sum_congr rfl ?_
  intro idx _
  rcases idx with k | ⟨p, q⟩
  · simp [liftCoeff_weighted_inl]
  · simp [liftCoeff_weighted_inr]

/-- **Farkas certificate lift**: if `u'` certifies the reduced system,
`liftCert A u'` certifies the original. -/
theorem fm_cert_lift (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hred : HasCertificate (fmA A) (fmB A b)) : HasCertificate A b := by
  obtain ⟨u', hu'_nn, hu'_zero, hu'_pos⟩ := hred
  refine ⟨liftCert A u', liftCert_nonneg A hu'_nn, ?_, ?_⟩
  · -- ∀ j : Fin (n+1), ∑ i, u i * A i j = 0
    intro j
    refine Fin.lastCases ?_ ?_ j
    · exact liftCert_column_zero_last A u'
    · intro j'
      exact liftCert_column_zero_castSucc A b hu'_zero j'
  · rw [liftCert_rhs]
    exact hu'_pos

/-! ### Base case `n = 0`

For a 0-variable system, `rowEval A i x = ∑ j : Fin 0, … = 0` for every `i`,
so feasibility collapses to `∀ i, b i ≤ 0`. Negation yields a single `i`
with `0 < b i`, and the indicator at that `i` is the Farkas certificate. -/

private theorem theorem_of_alternative_base
    {I : Type*} [Fintype I] [DecidableEq I] (A : I → Fin 0 → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasCertificate A b := by
  classical
  refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
  intro hinf
  -- `IsFeasible ↔ ∀ i, b i ≤ 0`; the negation provides an index with `0 < b i`.
  have h_pick : ∃ i : I, 0 < b i := by
    by_contra hall
    push Not at hall
    apply hinf
    refine ⟨fun j : Fin 0 => Fin.elim0 j, fun i => ?_⟩
    have h_row_zero : rowEval A i (fun j : Fin 0 => Fin.elim0 j) = 0 := by
      unfold rowEval
      apply Finset.sum_eq_zero
      intro j _
      exact Fin.elim0 j
    rw [h_row_zero]
    exact hall i
  obtain ⟨i₀, hi₀⟩ := h_pick
  refine ⟨fun i => if i₀ = i then 1 else 0, ?_, ?_, ?_⟩
  · intro i
    show 0 ≤ if i₀ = i then (1 : 𝕜) else 0
    split_ifs <;> norm_num
  · intro j; exact Fin.elim0 j
  · -- ∑ i, (if i₀ = i then 1 else 0) * b i = b i₀ > 0
    show 0 < ∑ i, (if i₀ = i then (1 : 𝕜) else 0) * b i
    simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq]
    exact hi₀

/-! ### Strong induction on the number of columns

Combine: feasibility transfer (`feasible_of_fm_feasible`) is the contrapositive
direction that brings `¬ IsFeasible A b` to `¬ IsFeasible (fmA A) (fmB A b)`;
the inductive hypothesis then yields the reduced certificate, and `fm_cert_lift`
lifts it back to the original system. -/

private theorem theorem_of_alternative_aux :
    ∀ (n : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
      (A : I → Fin n → 𝕜) (b : I → 𝕜),
      ¬ IsFeasible A b ↔ HasCertificate A b := by
  intro n
  induction n with
  | zero =>
      intro I _ _ A b
      exact theorem_of_alternative_base A b
  | succ n ih =>
      intro I _ _ A b
      refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
      intro hinf
      have h_red_inf : ¬ IsFeasible (fmA A) (fmB A b) :=
        fun h => hinf (feasible_of_fm_feasible A b h)
      have h_red_cert : HasCertificate (fmA A) (fmB A b) :=
        (ih (fmA A) (fmB A b)).mp h_red_inf
      exact fm_cert_lift A b h_red_cert

/-! ### Final packaged theorem -/

/-- **Theorem of the Alternative** [MFoGT, Section 2.8, Exercise 7]: for a
finite system of weak linear inequalities `A x ≥ b` over a linearly ordered
field, exactly one of the primal `S = {x | Ax ≥ b}` and the Farkas
certificate set `T = {u ≥ 0 | uᵀA = 0, ⟨u, b⟩ > 0}` is nonempty.

Combines `feas_cert_disjoint` (disjointness) with the existence direction
proved by Fourier-Motzkin elimination + induction on the number of
variables (`theorem_of_alternative_aux`). -/
theorem theorem_of_alternative {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (A : I → Fin n → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasCertificate A b :=
  theorem_of_alternative_aux n A b

end EconCSLib.LinearAlgebra
