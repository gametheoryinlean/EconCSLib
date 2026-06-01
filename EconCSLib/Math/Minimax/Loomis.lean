/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Simplex
import EconCSLib.Math.Minimax.MinimaxLoomis
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.Compact

/-!
# EconCSLib.Math.Minimax.Loomis

LRS-style direct induction proof of the **general (positive-B) Loomis theorem**
[MFoGT, Theorem 2.5.1]:

> For matrices `A, B : I → J → ℝ` with `B` entrywise positive there exist
> `x : Δ(I)`, `y : Δ(J)`, and `v : ℝ` with `xA ≥ v · xB` and `Ay ≤ v · By`.

This file begins with the **scaffolding layer**:
positivity of the aggregates `xB` and `By`, the ratio-form auxiliaries
`lamB.aux` and `muB.aux`, and the Loomis scalars `lamB0`, `muB0`.

Subsequent layers (continuity / attainment / weak duality / induction /
packaged theorem) build on that scaffolding. The simplified-Loomis
(von Neumann minimax) `MinimaxLoomis.lam0 = MinimaxLoomis.mu0` is re-derived
as the `B = 𝟙` corollary `minmax_from_general` at the end of this file.

## Blueprint

* `docs/knowledge/nodes/zero_sum/loomis_theorem.md`
* `docs/knowledge/nodes/zero_sum/loomis_induction_proof.md`
* `docs/knowledge/nodes/zero_sum/loomis_induction_proof.positive_aggregate.md`

## Attribution

Structurally parallel to `EconCSLib.Math.Minimax.MinimaxLoomis` (ported from
`math-xmum/gametheory`'s `GameTheory/Zerosum.lean`), with `B` factors
threaded through where the simplified-Loomis route had `1`.
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace Loomis

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-! ### Entrywise positivity predicate -/

/-- A matrix `B : I → J → ℝ` is **entrywise positive** if every entry is `> 0`.
This is the hypothesis driving the general Loomis theorem, and the only
property of `B` the proof needs. -/
def IsPositive (B : I → J → ℝ) : Prop := ∀ i j, 0 < B i j

namespace IsPositive

/-- The all-ones matrix is positive; the simplified-Loomis specialisation
plugs `B := fun _ _ => 1` into the general theorem. -/
theorem one : IsPositive (fun (_ : I) (_ : J) => (1 : ℝ)) := fun _ _ => one_pos

end IsPositive

/-! ### Vector aggregates: `xA`, `xB`, `Ay`, `By`, and their positivity

The generic positivity lemma `wsum_pos` lives in `Math.Simplex`; the
Loomis-flavored aggregates below are one-line applications of it. -/

/-- Row-vector product `(xA)_j = ∑ᵢ xᵢ Aᵢⱼ`. -/
noncomputable def xA (A : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) : ℝ :=
  wsum x (fun i => A i j)

/-- Row-vector product `(xB)_j = ∑ᵢ xᵢ Bᵢⱼ`. -/
noncomputable def xB (B : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) : ℝ :=
  wsum x (fun i => B i j)

/-- Column-vector product `(Ay)_i = ∑ⱼ Aᵢⱼ yⱼ`. -/
noncomputable def Ay (A : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) : ℝ :=
  wsum y (fun j => A i j)

/-- Column-vector product `(By)_i = ∑ⱼ Bᵢⱼ yⱼ`. -/
noncomputable def By (B : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) : ℝ :=
  wsum y (fun j => B i j)

/-- Positivity of the row aggregate when `B` is entrywise positive. -/
theorem xB_pos {B : I → J → ℝ} (hB : IsPositive B)
    (x : stdSimplex ℝ I) (j : J) : 0 < xB B x j :=
  wsum_pos x (fun i => hB i j)

/-- Positivity of the column aggregate when `B` is entrywise positive. -/
theorem By_pos {B : I → J → ℝ} (hB : IsPositive B)
    (y : stdSimplex ℝ J) (i : I) : 0 < By B y i :=
  wsum_pos y (fun j => hB i j)

/-- Positivity of the bilinear pairing `xBy = ∑ᵢⱼ xᵢ Bᵢⱼ yⱼ`. -/
theorem xBy_pos {B : I → J → ℝ} (hB : IsPositive B)
    (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) :
    0 < wsum x (fun i => By B y i) :=
  wsum_pos x (fun i => By_pos hB y i)

/-! ### Loomis ratios and the scalars `lamB0`, `muB0` -/

/-- Row player's per-column Loomis ratio `(xA)_j / (xB)_j`. -/
noncomputable def colRatio (A B : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) : ℝ :=
  xA A x j / xB B x j

/-- Column player's per-row Loomis ratio `(Ay)_i / (By)_i`. -/
noncomputable def rowRatio (A B : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) : ℝ :=
  Ay A y i / By B y i

/-- Player I's guaranteed Loomis ratio under mixed strategy `x`: infimum over
pure columns. -/
noncomputable def lamB.aux (A B : I → J → ℝ) (x : stdSimplex ℝ I) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun j => colRatio A B x j)

/-- Player II's Loomis-ratio cap under mixed strategy `y`: supremum over
pure rows. -/
noncomputable def muB.aux (A B : I → J → ℝ) (y : stdSimplex ℝ J) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => rowRatio A B y i)

/-- Maxmin Loomis scalar `λ₀ = sup_x λ_aux(x)`. -/
noncomputable def lamB0 (A B : I → J → ℝ) : ℝ := iSup (lamB.aux A B)

/-- Minmax Loomis scalar `μ₀ = inf_y μ_aux(y)`. -/
noncomputable def muB0 (A B : I → J → ℝ) : ℝ := iInf (muB.aux A B)

/-- Characterisation: `lamB.aux A B x > c` iff every column ratio exceeds `c`. -/
theorem lamB.aux_gt_iff_gt (A B : I → J → ℝ) (c : ℝ) (x : stdSimplex ℝ I) :
    c < lamB.aux A B x ↔ ∀ j, c < colRatio A B x j := by
  simp [lamB.aux, Finset.lt_inf'_iff]

/-- Characterisation: `muB.aux A B y < c` iff every row ratio is below `c`. -/
theorem muB.aux_lt_iff_lt (A B : I → J → ℝ) (c : ℝ) (y : stdSimplex ℝ J) :
    muB.aux A B y < c ↔ ∀ i, rowRatio A B y i < c := by
  simp [muB.aux, Finset.sup'_lt_iff]

/-! ### Continuity, boundedness, and attainment

The Loomis ratios are continuous on the compact simplex (positive denominators by
`xB_pos` / `By_pos`), so the inf'/sup' aggregates are continuous and
their extrema `lamB0` / `muB0` are attained. -/

/-- Each column ratio `(xA)_j / (xB)_j` is continuous on `Δ(I)`. -/
theorem colRatio.continuous {A B : I → J → ℝ} (hB : IsPositive B) (j : J) :
    Continuous (fun x : stdSimplex ℝ I => colRatio A B x j) := by
  unfold colRatio xA xB
  exact (wsum_continuous (fun i => A i j)).div
    (wsum_continuous (fun i => B i j))
    (fun x => (xB_pos hB x j).ne')

/-- Each row ratio `(Ay)_i / (By)_i` is continuous on `Δ(J)`. -/
theorem rowRatio.continuous {A B : I → J → ℝ} (hB : IsPositive B) (i : I) :
    Continuous (fun y : stdSimplex ℝ J => rowRatio A B y i) := by
  unfold rowRatio Ay By
  exact (wsum_continuous (fun j => A i j)).div
    (wsum_continuous (fun j => B i j))
    (fun y => (By_pos hB y i).ne')

/-- `lamB.aux A B` is continuous on the simplex. -/
theorem lamB.aux.continuous {A B : I → J → ℝ} (hB : IsPositive B) :
    Continuous (lamB.aux A B) := by
  refine Continuous.finset_inf'_apply Finset.univ_nonempty ?_
  intro j _
  exact colRatio.continuous hB j

/-- `muB.aux A B` is continuous on the simplex. -/
theorem muB.aux.continuous {A B : I → J → ℝ} (hB : IsPositive B) :
    Continuous (muB.aux A B) := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty ?_
  intro i _
  exact rowRatio.continuous hB i

/-- `lamB.aux A B` is bounded above on the simplex (continuous function on a
compact set). -/
theorem lamB.aux.bddAbove {A B : I → J → ℝ} (hB : IsPositive B) :
    ∃ C, ∀ x, lamB.aux A B x ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ.image (lamB.aux.continuous hB)).bddAbove
  refine ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩

/-- `muB.aux A B` is bounded below on the simplex. -/
theorem muB.aux.bddBelow {A B : I → J → ℝ} (hB : IsPositive B) :
    ∃ C, ∀ y, C ≤ muB.aux A B y := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ.image (muB.aux.continuous hB)).bddBelow
  refine ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩

/-- Every `lamB.aux` value is bounded by the supremum `lamB0`. -/
theorem lamB.aux.le_lamB0 {A B : I → J → ℝ} (hB : IsPositive B)
    (x : stdSimplex ℝ I) :
    lamB.aux A B x ≤ lamB0 A B :=
  le_ciSup (bddAbove_def.2 (by
    obtain ⟨C, hC⟩ := lamB.aux.bddAbove hB
    exact ⟨C, by rintro r ⟨x, rfl⟩; exact hC x⟩)) x

/-- Every `muB.aux` value dominates the infimum `muB0`. -/
theorem muB.aux.ge_muB0 {A B : I → J → ℝ} (hB : IsPositive B)
    (y : stdSimplex ℝ J) :
    muB0 A B ≤ muB.aux A B y :=
  ciInf_le (bddBelow_def.2 (by
    obtain ⟨C, hC⟩ := muB.aux.bddBelow hB
    exact ⟨C, by rintro r ⟨y, rfl⟩; exact hC y⟩)) y

/-- Attainment of `lamB0`: there exists a mixed strategy `xx` with
`(xA xx)_j ≥ lamB0 · (xB xx)_j` for every column. -/
theorem exists_xx_lamB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ xx : stdSimplex ℝ I, ∀ j, lamB0 A B * xB B xx j ≤ xA A xx j := by
  obtain ⟨xx, _, hxx⟩ :=
    isCompact_univ.exists_isMaxOn (α := ℝ) (β := stdSimplex ℝ I)
      Set.univ_nonempty (lamB.aux.continuous hB).continuousOn
  rw [isMaxOn_iff] at hxx
  refine ⟨xx, fun j => ?_⟩
  have h1 : lamB0 A B ≤ lamB.aux A B xx :=
    ciSup_le fun y => hxx y (Set.mem_univ _)
  have h2 : lamB.aux A B xx ≤ colRatio A B xx j :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hxxB : 0 < xB B xx j := xB_pos hB xx j
  -- lamB0 ≤ xA / xB ⇒ lamB0 * xB ≤ xA  (since xB > 0)
  have hratio : lamB0 A B ≤ colRatio A B xx j := h1.trans h2
  unfold colRatio at hratio
  exact (le_div_iff₀ hxxB).mp hratio

/-- Attainment of `muB0`: there exists a mixed strategy `yy` with
`(Ay yy)_i ≤ muB0 · (By yy)_i` for every row. -/
theorem exists_yy_muB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ yy : stdSimplex ℝ J, ∀ i, Ay A yy i ≤ muB0 A B * By B yy i := by
  obtain ⟨yy, _, hyy⟩ :=
    isCompact_univ.exists_isMinOn (α := ℝ) (β := stdSimplex ℝ J)
      Set.univ_nonempty (muB.aux.continuous hB).continuousOn
  rw [isMinOn_iff] at hyy
  refine ⟨yy, fun i => ?_⟩
  have h1 : muB.aux A B yy ≤ muB0 A B :=
    le_ciInf fun z => hyy z (Set.mem_univ _)
  have h2 : rowRatio A B yy i ≤ muB.aux A B yy :=
    Finset.le_sup' (f := fun i => rowRatio A B yy i) (Finset.mem_univ i)
  have hyyB : 0 < By B yy i := By_pos hB yy i
  have hratio : rowRatio A B yy i ≤ muB0 A B := h2.trans h1
  unfold rowRatio at hratio
  exact (div_le_iff₀ hyyB).mp hratio

/-! ### Weak duality `lamB0 ≤ muB0` -/

/-- The bilinear pairing `xBy` and its symmetric variants. -/
private theorem xBy_swap (B : I → J → ℝ)
    (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) :
    wsum x (fun i => By B y i) = wsum y (fun j => xB B x j) := by
  unfold xB By
  exact wsum_wsum_comm x y B

/-- Weight a constant multiple under `wsum`: `wsum z (c · f) = c · wsum z f`.
A direct unfold of `wsum_smul`, restated here so chained rewrites match the
shape used in the weak-duality proof. -/
private theorem wsum_const_mul {K : Type*} [Fintype K] (z : stdSimplex ℝ K)
    (c : ℝ) (f : K → ℝ) :
    wsum z (fun a => c * f a) = c * wsum z f := by
  change (∑ a, z.val a * (c * f a)) = c * (∑ a, z.val a * f a)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

/-- **Weak duality** for the Loomis scalars: `lamB0 ≤ muB0`. -/
theorem lamB0_le_muB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    lamB0 A B ≤ muB0 A B := by
  obtain ⟨xx, Hxx⟩ := exists_xx_lamB0 A B hB
  obtain ⟨yy, Hyy⟩ := exists_yy_muB0 A B hB
  set xxByy : ℝ := wsum xx (fun i => By B yy i) with hxxByy_def
  have hxxByy_pos : 0 < xxByy := xBy_pos hB xx yy
  -- The pairing `xx A · yy`, written both ways.
  set pairing : ℝ := wsum xx (fun i => Ay A yy i) with hpairing_def
  have hswap : pairing = wsum yy (fun j => xA A xx j) := by
    rw [hpairing_def]
    unfold Ay xA
    exact wsum_wsum_comm xx yy A
  -- lamB0 · xxByy ≤ pairing
  have h_lam : lamB0 A B * xxByy ≤ pairing := by
    rw [hswap]
    calc lamB0 A B * xxByy
        = lamB0 A B * wsum yy (fun j => xB B xx j) := by
          rw [hxxByy_def, xBy_swap]
      _ = wsum yy (fun j => lamB0 A B * xB B xx j) := by
          rw [wsum_const_mul]
      _ ≤ wsum yy (fun j => xA A xx j) :=
          wsum_le_wsum yy (fun j => Hxx j)
  -- pairing ≤ muB0 · xxByy
  have h_mu : pairing ≤ muB0 A B * xxByy := by
    rw [hpairing_def]
    calc wsum xx (fun i => Ay A yy i)
        ≤ wsum xx (fun i => muB0 A B * By B yy i) :=
          wsum_le_wsum xx (fun i => Hyy i)
      _ = muB0 A B * wsum xx (fun i => By B yy i) := by
          rw [wsum_const_mul]
      _ = muB0 A B * xxByy := by rw [hxxByy_def]
  -- Combine and divide by the positive xxByy.
  have hcombo : lamB0 A B * xxByy ≤ muB0 A B * xxByy := h_lam.trans h_mu
  exact le_of_mul_le_mul_right hcombo hxxByy_pos

/-! ### Base case `|I| + |J| = 2` -/

/-- Base case of the Loomis induction: a 1×1 matrix pair has the single
ratio `A i₀ j₀ / B i₀ j₀` as the common Loomis value. -/
theorem loomis_value_IJ_2 (Hn : 2 = Fintype.card I + Fintype.card J)
    {A B : I → J → ℝ} (_hB : IsPositive B) :
    lamB0 A B = muB0 A B := by
  classical
  have ⟨HSI, HSJ⟩ : Fintype.card I = 1 ∧ Fintype.card J = 1 := by
    have p1 := @Fintype.card_pos I _ _
    have p2 := @Fintype.card_pos J _ _
    refine ⟨?_, ?_⟩ <;> omega
  obtain ⟨i0, hi⟩ := MinimaxLoomis.singleton_of_card_one HSI
  obtain ⟨j0, hj⟩ := MinimaxLoomis.singleton_of_card_one HSJ
  -- On a singleton simplex every distribution puts mass 1 at the single point.
  have Hxx0 : ∀ x : stdSimplex ℝ I, x.val i0 = 1 := by
    intro x
    have hsum : (∑ i : I, x.val i) = 1 := x.property.2
    have hcol : (∑ i : I, x.val i) = x.val i0 := by
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton]
    linarith
  have Hyy0 : ∀ y : stdSimplex ℝ J, y.val j0 = 1 := by
    intro y
    have hsum : (∑ j : J, y.val j) = 1 := y.property.2
    have hrow : (∑ j : J, y.val j) = y.val j0 := by
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton]
    linarith
  -- Both ratios reduce to A i0 j0 / B i0 j0 regardless of the strategy.
  have HlamB : ∀ x, lamB.aux A B x = A i0 j0 / B i0 j0 := by
    intro x
    simp only [lamB.aux, hj, Finset.inf'_singleton]
    show colRatio A B x j0 = A i0 j0 / B i0 j0
    unfold colRatio xA xB
    have hxA : wsum x (fun i => A i j0) = A i0 j0 := by
      change (∑ i, x.val i * A i j0) = A i0 j0
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton,
          Hxx0 x, one_mul]
    have hxB : wsum x (fun i => B i j0) = B i0 j0 := by
      change (∑ i, x.val i * B i j0) = B i0 j0
      rw [show (Finset.univ : Finset I) = {i0} from hi, Finset.sum_singleton,
          Hxx0 x, one_mul]
    rw [hxA, hxB]
  have HmuB : ∀ y, muB.aux A B y = A i0 j0 / B i0 j0 := by
    intro y
    simp only [muB.aux, hi, Finset.sup'_singleton]
    show rowRatio A B y i0 = A i0 j0 / B i0 j0
    unfold rowRatio Ay By
    have hAy : wsum y (fun j => A i0 j) = A i0 j0 := by
      change (∑ j, y.val j * A i0 j) = A i0 j0
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton,
          Hyy0 y, one_mul]
    have hBy : wsum y (fun j => B i0 j) = B i0 j0 := by
      change (∑ j, y.val j * B i0 j) = B i0 j0
      rw [show (Finset.univ : Finset J) = {j0} from hj, Finset.sum_singleton,
          Hyy0 y, one_mul]
    rw [hAy, hBy]
  rw [lamB0, iSup_congr HlamB, ciSup_const, muB0, iInf_congr HmuB, ciInf_const]

/-! ### Induction step

We linearise the Loomis inequalities by introducing the offset functionals
`G(x, j) := (xA)_j - λ₀ · (xB)_j` and `H(y, i) := μ₀ · (By)_i - (Ay)_i`,
turning the inequalities `xA ≥ λ₀ · xB` and `Ay ≤ μ₀ · By` into nonneg
conditions on functions linear in their simplex argument. Convex
combinations then reduce to the constant-`c = 0` `linear_comb_*` and
`mix_*_nbh` lemmas from `Core.Simplex`. -/

/-- Linearised column constraint: `colOffset A B λ x j = (xA)_j - λ · (xB)_j`.
Note that `colOffset A B λ x j = wsum x (fun i => A i j - λ * B i j)` is
linear in `x`. -/
private noncomputable def colOffset (A B : I → J → ℝ) (lam : ℝ)
    (x : stdSimplex ℝ I) (j : J) : ℝ :=
  xA A x j - lam * xB B x j

/-- Linearised row constraint: `rowOffset A B μ y i = μ · (By)_i - (Ay)_i`. -/
private noncomputable def rowOffset (A B : I → J → ℝ) (mu : ℝ)
    (y : stdSimplex ℝ J) (i : I) : ℝ :=
  mu * By B y i - Ay A y i

/-- `colOffset` is a `wsum` of `A i j - λ B i j` over `i`. -/
private theorem colOffset_eq_wsum (A B : I → J → ℝ) (lam : ℝ)
    (x : stdSimplex ℝ I) (j : J) :
    colOffset A B lam x j = wsum x (fun i => A i j - lam * B i j) := by
  unfold colOffset xA xB
  change (∑ i, x.val i * A i j) - lam * (∑ i, x.val i * B i j)
      = ∑ i, x.val i * (A i j - lam * B i j)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- `rowOffset` is a `wsum` of `μ B i j - A i j` over `j`. -/
private theorem rowOffset_eq_wsum (A B : I → J → ℝ) (mu : ℝ)
    (y : stdSimplex ℝ J) (i : I) :
    rowOffset A B mu y i = wsum y (fun j => mu * B i j - A i j) := by
  unfold rowOffset Ay By
  change mu * (∑ j, y.val j * B i j) - (∑ j, y.val j * A i j)
      = ∑ j, y.val j * (mu * B i j - A i j)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- Convex combination linearity for `colOffset` in the simplex argument. -/
private theorem colOffset_mix (A B : I → J → ℝ) (lam : ℝ)
    (x y : stdSimplex ℝ I) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (j : J) :
    colOffset A B lam (stdSimplex.mix t ht₀ ht₁ x y) j
      = t * colOffset A B lam x j + (1 - t) * colOffset A B lam y j := by
  simp only [colOffset_eq_wsum]
  exact wsum_mix t ht₀ ht₁ x y _

/-- Convex combination linearity for `rowOffset` in the simplex argument. -/
private theorem rowOffset_mix (A B : I → J → ℝ) (mu : ℝ)
    (x y : stdSimplex ℝ J) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : I) :
    rowOffset A B mu (stdSimplex.mix t ht₀ ht₁ x y) i
      = t * rowOffset A B mu x i + (1 - t) * rowOffset A B mu y i := by
  simp only [rowOffset_eq_wsum]
  exact wsum_mix t ht₀ ht₁ x y _

/-! ### Equivalence of the ratio form and the offset form -/

/-- `lamB.aux A B x` strictly exceeds `lam` iff every offset `colOffset` is
strictly positive at `x`. -/
private theorem lamB.aux_gt_of_colOffset_pos {A B : I → J → ℝ}
    (hB : IsPositive B) {lam : ℝ} {x : stdSimplex ℝ I}
    (H : ∀ j, 0 < colOffset A B lam x j) :
    lam < lamB.aux A B x := by
  rw [lamB.aux_gt_iff_gt]
  intro j
  unfold colRatio
  rw [lt_div_iff₀ (xB_pos hB x j)]
  -- Goal: lam * xB B x j < xA A x j
  have := H j
  unfold colOffset at this
  linarith

/-- `muB.aux A B y` is strictly below `mu` iff every offset `rowOffset` is
strictly positive at `y`. -/
private theorem muB.aux_lt_of_rowOffset_pos {A B : I → J → ℝ}
    (hB : IsPositive B) {mu : ℝ} {y : stdSimplex ℝ J}
    (H : ∀ i, 0 < rowOffset A B mu y i) :
    muB.aux A B y < mu := by
  rw [muB.aux_lt_iff_lt]
  intro i
  unfold rowRatio
  rw [div_lt_iff₀ (By_pos hB y i)]
  have := H i
  unfold rowOffset at this
  linarith

/-! ### Column / row extension to the unrestricted simplex -/

/-- Drop the `j₀`-column of `A` and view as a matrix on `I × {j // j ≠ j₀}`. -/
private noncomputable def dropCol [DecidableEq J] (A : I → J → ℝ) (j₀ : J) :
    I → {j : J // j ≠ j₀} → ℝ :=
  fun i j' => A i j'.val

/-- Drop the `i₀`-row of `A` and view as a matrix on `{i // i ≠ i₀} × J`. -/
private noncomputable def dropRow [DecidableEq I] (A : I → J → ℝ) (i₀ : I) :
    {i : I // i ≠ i₀} → J → ℝ :=
  fun i' j => A i'.val j

/-- Dropping a column preserves entrywise positivity. -/
private theorem dropCol.IsPositive [DecidableEq J] {B : I → J → ℝ}
    (hB : IsPositive B) (j₀ : J) : IsPositive (dropCol B j₀) :=
  fun i j' => hB i j'.val

/-- Dropping a row preserves entrywise positivity. -/
private theorem dropRow.IsPositive [DecidableEq I] {B : I → J → ℝ}
    (hB : IsPositive B) (i₀ : I) : IsPositive (dropRow B i₀) :=
  fun i' j => hB i'.val j

/-- Extending `y' ∈ Δ(J')` to `Δ(J)` by zero at `j₀` recovers the same row
aggregates from `A` (and `B`). -/
private theorem Ay_extendDropColumn [DecidableEq J] (i : I) (A : I → J → ℝ)
    (j₀ : J) (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    Ay A (MinimaxLoomis.extendDropColumn j₀ y') i = Ay (dropCol A j₀) y' i := by
  unfold Ay
  rw [MinimaxLoomis.wsum_extendDropColumn]
  rfl

private theorem By_extendDropColumn [DecidableEq J] (i : I) (B : I → J → ℝ)
    (j₀ : J) (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    By B (MinimaxLoomis.extendDropColumn j₀ y') i = By (dropCol B j₀) y' i := by
  unfold By
  rw [MinimaxLoomis.wsum_extendDropColumn]
  rfl

private theorem xA_extendDropRow [DecidableEq I] (j : J) (A : I → J → ℝ)
    (i₀ : I) (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    xA A (MinimaxLoomis.extendDropRow i₀ x') j = xA (dropRow A i₀) x' j := by
  unfold xA
  rw [MinimaxLoomis.wsum_extendDropRow]
  rfl

private theorem xB_extendDropRow [DecidableEq I] (j : J) (B : I → J → ℝ)
    (i₀ : I) (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    xB B (MinimaxLoomis.extendDropRow i₀ x') j = xB (dropRow B i₀) x' j := by
  unfold xB
  rw [MinimaxLoomis.wsum_extendDropRow]
  rfl

/-! ### The strong induction `loomis_value_eq` -/

/-- **Loomis induction**: `lamB0 A B = muB0 A B` for any finite positive-`B`
matrix pair with `2 ≤ |I| + |J|`, by strong induction on the total dimension. -/
private theorem loomis_value_eq_aux :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J],
      n = Fintype.card I + Fintype.card J →
      ∀ (A B : I → J → ℝ), IsPositive B → lamB0 A B = muB0 A B := by
  intro n Hgt
  induction n, Hgt using Nat.le_induction with
  | base =>
      intro I J _ _ _ _ Hn A B hB
      exact loomis_value_IJ_2 Hn hB
  | succ n _ IH =>
      intro I J _ _ _ _ Hn A B hB
      classical
      rcases (lamB0_le_muB0 A B hB).lt_or_eq with hlt | heq
      swap
      · exact heq
      exfalso
      obtain ⟨xx, Hxx⟩ := exists_xx_lamB0 A B hB
      obtain ⟨yy, Hyy⟩ := exists_yy_muB0 A B hB
      -- The Hxx/Hyy say `colOffset ≥ 0` / `rowOffset ≥ 0` everywhere.
      have HxxOff : ∀ j, 0 ≤ colOffset A B (lamB0 A B) xx j := by
        intro j; unfold colOffset; linarith [Hxx j]
      have HyyOff : ∀ i, 0 ≤ rowOffset A B (muB0 A B) yy i := by
        intro i; unfold rowOffset; linarith [Hyy i]
      -- If both are identically zero, we get `lamB0 = muB0`, contradiction.
      have exits_ij :
          (∃ j : J, 0 < colOffset A B (lamB0 A B) xx j)
            ∨ (∃ i : I, 0 < rowOffset A B (muB0 A B) yy i) := by
        by_contra HP
        push_neg at HP
        obtain ⟨HP1, HP2⟩ := HP
        have HxxZero : ∀ j, colOffset A B (lamB0 A B) xx j = 0 :=
          fun j => le_antisymm (HP1 j) (HxxOff j)
        have HyyZero : ∀ i, rowOffset A B (muB0 A B) yy i = 0 :=
          fun i => le_antisymm (HP2 i) (HyyOff i)
        -- These give wsum yy (colOffset xx ·) = 0 and wsum xx (rowOffset yy ·) = 0.
        set xxByy : ℝ := wsum xx (fun i => By B yy i)
        have hxxByy_pos : 0 < xxByy := xBy_pos hB xx yy
        -- wsum yy (xA xx ·) = lamB0 * (wsum yy (xB xx ·)) and
        -- wsum xx (Ay yy ·) = muB0 * (wsum xx (By yy ·)) = muB0 * xxByy
        have h_pair_swap :
            wsum xx (fun i => Ay A yy i) = wsum yy (fun j => xA A xx j) := by
          unfold Ay xA
          exact wsum_wsum_comm xx yy A
        have h_xxByy_swap :
            wsum yy (fun j => xB B xx j) = xxByy := by
          show wsum yy (fun j => xB B xx j) = wsum xx (fun i => By B yy i)
          exact (xBy_swap B xx yy).symm
        -- From HxxZero: wsum yy (xA xx ·) = lamB0 * wsum yy (xB xx ·)
        have h_lhs : wsum yy (fun j => xA A xx j) = lamB0 A B * xxByy := by
          rw [← h_xxByy_swap]
          have : wsum yy (fun j => xA A xx j)
              = wsum yy (fun j => lamB0 A B * xB B xx j) := by
            refine congrArg (wsum yy) (funext ?_)
            intro j
            have := HxxZero j
            unfold colOffset at this
            linarith
          rw [this, wsum_const_mul]
        -- From HyyZero: wsum xx (Ay yy ·) = muB0 * xxByy
        have h_rhs : wsum xx (fun i => Ay A yy i) = muB0 A B * xxByy := by
          have : wsum xx (fun i => Ay A yy i)
              = wsum xx (fun i => muB0 A B * By B yy i) := by
            refine congrArg (wsum xx) (funext ?_)
            intro i
            have := HyyZero i
            unfold rowOffset at this
            linarith
          rw [this, wsum_const_mul]
        have heq2 : lamB0 A B = muB0 A B := by
          have hcombo : lamB0 A B * xxByy = muB0 A B * xxByy := by
            linarith [h_lhs, h_pair_swap, h_rhs]
          exact mul_right_cancel₀ hxxByy_pos.ne' hcombo
        linarith
      rcases exits_ij with ⟨j₀, HJ⟩ | ⟨i₀, HI⟩
      · -------------------- Column-drop case --------------------
        -- |J| ≥ 2 because strict ineq at j₀ ⇒ otherwise lamB.aux xx > lamB0,
        -- contradicting lamB.aux ≤ lamB0.
        have cardJ_ne_one : Fintype.card J ≠ 1 := by
          intro hcardJ
          obtain ⟨j, hj⟩ := Finset.card_eq_one.1 (by simpa using hcardJ)
          have hj0_eq : j₀ = j := by
            have hmem : j₀ ∈ (Finset.univ : Finset J) := Finset.mem_univ _
            rw [hj] at hmem
            exact Finset.mem_singleton.1 hmem
          -- lamB.aux xx evaluated at the unique column j₀
          have hlamB_xx : lamB.aux A B xx = colRatio A B xx j₀ := by
            simp [lamB.aux, hj0_eq, hj]
          have hxxB : 0 < xB B xx j₀ := xB_pos hB xx j₀
          have hratio_gt : lamB0 A B < colRatio A B xx j₀ := by
            unfold colRatio
            rw [lt_div_iff₀ hxxB]
            have hHJ := HJ; unfold colOffset at hHJ; linarith
          have hle : lamB.aux A B xx ≤ lamB0 A B := lamB.aux.le_lamB0 hB xx
          rw [hlamB_xx] at hle
          linarith
        have cardJ_ge_two : 2 ≤ Fintype.card J := by
          have hpos : 1 ≤ Fintype.card J := Fintype.card_pos
          omega
        have nonempty_J' : Nonempty {j : J // j ≠ j₀} := by
          obtain ⟨j, hj⟩ : ∃ j : J, j ≠ j₀ := by
            by_contra H1
            push_neg at H1
            have hsubsing : Fintype.card J ≤ 1 := by
              have hsingle : (Finset.univ : Finset J) = {j₀} := by ext; simp [H1]
              simpa [← Finset.card_univ, hsingle]
            omega
          exact ⟨⟨j, hj⟩⟩
        haveI : Nonempty {j : J // j ≠ j₀} := nonempty_J'
        have cardn : n = Fintype.card I + Fintype.card {j : J // j ≠ j₀} := by
          have hJ' : Fintype.card {j : J // j ≠ j₀} = Fintype.card J - 1 := by
            simp [Fintype.card_subtype_compl]
          have hposJ : 1 ≤ Fintype.card J := Fintype.card_pos
          omega
        -- Apply IH to the column-dropped game.
        let A' : I → {j : J // j ≠ j₀} → ℝ := dropCol A j₀
        let B' : I → {j : J // j ≠ j₀} → ℝ := dropCol B j₀
        have hB' : IsPositive B' := dropCol.IsPositive hB j₀
        have IH' : lamB0 A' B' = muB0 A' B' := IH cardn A' B' hB'
        -- Show muB0 A B ≤ muB0 A' B' via the extend-by-zero trick.
        have h_mu_mono : muB0 A B ≤ muB0 A' B' := by
          apply le_ciInf
          intro y'
          have hwsum_Ay : ∀ i,
              Ay A (MinimaxLoomis.extendDropColumn j₀ y') i = Ay A' y' i :=
            fun i => Ay_extendDropColumn i A j₀ y'
          have hwsum_By : ∀ i,
              By B (MinimaxLoomis.extendDropColumn j₀ y') i = By B' y' i :=
            fun i => By_extendDropColumn i B j₀ y'
          have hmuA' : muB.aux A' B' y'
              = muB.aux A B (MinimaxLoomis.extendDropColumn j₀ y') := by
            simp only [muB.aux]
            congr 1
            ext i
            unfold rowRatio
            rw [hwsum_Ay i, hwsum_By i]
          rw [hmuA']
          exact muB.aux.ge_muB0 hB (MinimaxLoomis.extendDropColumn j₀ y')
        have lamB0_lt_lamB0' : lamB0 A B < lamB0 A' B' := by
          calc lamB0 A B < muB0 A B := hlt
            _ ≤ muB0 A' B' := h_mu_mono
            _ = lamB0 A' B' := IH'.symm
        -- Get the inductive optimiser `xx'` for the restricted game.
        obtain ⟨xx', Hxx'⟩ := exists_xx_lamB0 A' B' hB'
        -- On non-j₀ columns, `colOffset A B lamB0 xx' j > 0`.
        have HxxOff' : ∀ j : J, j ≠ j₀ →
            0 < colOffset A B (lamB0 A B) xx' j := by
          intro j hj
          have hxx'_j : lamB0 A' B' * xB B' xx' ⟨j, hj⟩
              ≤ xA A' xx' ⟨j, hj⟩ := Hxx' ⟨j, hj⟩
          have : lamB0 A B * xB B xx' j < xA A xx' j := by
            have hxB'_xB : xB B' xx' ⟨j, hj⟩ = xB B xx' j := rfl
            have hxA'_xA : xA A' xx' ⟨j, hj⟩ = xA A xx' j := rfl
            have hxBpos : 0 < xB B xx' j := xB_pos hB xx' j
            calc lamB0 A B * xB B xx' j
                < lamB0 A' B' * xB B xx' j := by
                  exact (mul_lt_mul_iff_of_pos_right hxBpos).mpr lamB0_lt_lamB0'
              _ ≤ xA A xx' j := by
                  rw [← hxB'_xB, ← hxA'_xA]; exact hxx'_j
          unfold colOffset; linarith
        -- For j = j₀ use the neighborhood-of-1 continuity lemma; for j ≠ j₀
        -- the convex combination keeps strict positivity.
        obtain ⟨t, ht0pos, ht1lt, hstrict_j0_raw⟩ :
            ∃ t : ℝ, 0 < t ∧ t < 1 ∧
              0 < t * colOffset A B (lamB0 A B) xx j₀
                + (1 - t) * colOffset A B (lamB0 A B) xx' j₀ :=
          mix_gt_of_gt_nbh _ _ _ HJ
        have ht₀ : 0 ≤ t := le_of_lt ht0pos
        have ht₁ : t ≤ 1 := le_of_lt ht1lt
        have hstrict_j0 :
            0 < colOffset A B (lamB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ xx xx') j₀ := by
          rw [colOffset_mix]; exact hstrict_j0_raw
        -- Assemble strict on every j.
        have hAll : ∀ j,
            0 < colOffset A B (lamB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ xx xx') j := by
          intro j
          by_cases hj : j = j₀
          · rw [hj]; exact hstrict_j0
          · rw [colOffset_mix]
            exact linear_comb_gt_of_ge_gt
              (colOffset A B (lamB0 A B) xx j)
              (colOffset A B (lamB0 A B) xx' j) 0
              (HxxOff j) (HxxOff' j hj) ht₀ ht1lt
        -- Hence lamB.aux at the combination strictly exceeds lamB0, contradiction.
        have hgt : lamB0 A B
            < lamB.aux A B (stdSimplex.mix t ht₀ ht₁ xx xx') :=
          lamB.aux_gt_of_colOffset_pos hB hAll
        have hle : lamB.aux A B (stdSimplex.mix t ht₀ ht₁ xx xx') ≤ lamB0 A B :=
          lamB.aux.le_lamB0 hB _
        linarith
      · -------------------- Row-drop case --------------------
        have cardI_ne_one : Fintype.card I ≠ 1 := by
          intro hcardI
          obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (by simpa using hcardI)
          have hi0_eq : i₀ = i := by
            have hmem : i₀ ∈ (Finset.univ : Finset I) := Finset.mem_univ _
            rw [hi] at hmem
            exact Finset.mem_singleton.1 hmem
          have hmuB_yy : muB.aux A B yy = rowRatio A B yy i₀ := by
            simp [muB.aux, hi0_eq, hi]
          have hyyB : 0 < By B yy i₀ := By_pos hB yy i₀
          have hratio_lt : rowRatio A B yy i₀ < muB0 A B := by
            unfold rowRatio
            rw [div_lt_iff₀ hyyB]
            have hHI := HI; unfold rowOffset at hHI; linarith
          have hge : muB0 A B ≤ muB.aux A B yy := muB.aux.ge_muB0 hB yy
          rw [hmuB_yy] at hge
          linarith
        have cardI_ge_two : 2 ≤ Fintype.card I := by
          have hpos : 1 ≤ Fintype.card I := Fintype.card_pos
          omega
        have nonempty_I' : Nonempty {i : I // i ≠ i₀} := by
          obtain ⟨i, hi⟩ : ∃ i : I, i ≠ i₀ := by
            by_contra H1
            push_neg at H1
            have hsubsing : Fintype.card I ≤ 1 := by
              have hsingle : (Finset.univ : Finset I) = {i₀} := by ext; simp [H1]
              simpa [← Finset.card_univ, hsingle]
            omega
          exact ⟨⟨i, hi⟩⟩
        haveI : Nonempty {i : I // i ≠ i₀} := nonempty_I'
        have cardn : n = Fintype.card {i : I // i ≠ i₀} + Fintype.card J := by
          have hI' : Fintype.card {i : I // i ≠ i₀} = Fintype.card I - 1 := by
            simp [Fintype.card_subtype_compl]
          have hposI : 1 ≤ Fintype.card I := Fintype.card_pos
          omega
        let A' : {i : I // i ≠ i₀} → J → ℝ := dropRow A i₀
        let B' : {i : I // i ≠ i₀} → J → ℝ := dropRow B i₀
        have hB' : IsPositive B' := dropRow.IsPositive hB i₀
        have IH' : lamB0 A' B' = muB0 A' B' := IH cardn A' B' hB'
        have h_lam_mono : lamB0 A' B' ≤ lamB0 A B := by
          apply ciSup_le
          intro x'
          have hwsum_xA : ∀ j,
              xA A (MinimaxLoomis.extendDropRow i₀ x') j = xA A' x' j :=
            fun j => xA_extendDropRow j A i₀ x'
          have hwsum_xB : ∀ j,
              xB B (MinimaxLoomis.extendDropRow i₀ x') j = xB B' x' j :=
            fun j => xB_extendDropRow j B i₀ x'
          have hlamA' : lamB.aux A' B' x'
              = lamB.aux A B (MinimaxLoomis.extendDropRow i₀ x') := by
            simp only [lamB.aux]
            congr 1
            ext j
            unfold colRatio
            rw [hwsum_xA j, hwsum_xB j]
          rw [hlamA']
          exact lamB.aux.le_lamB0 hB (MinimaxLoomis.extendDropRow i₀ x')
        have muB0_gt_muB0' : muB0 A' B' < muB0 A B := by
          calc muB0 A' B' = lamB0 A' B' := IH'.symm
            _ ≤ lamB0 A B := h_lam_mono
            _ < muB0 A B := hlt
        obtain ⟨yy', Hyy'⟩ := exists_yy_muB0 A' B' hB'
        have HyyOff' : ∀ i : I, i ≠ i₀ →
            0 < rowOffset A B (muB0 A B) yy' i := by
          intro i hi
          have hyy'_i : Ay A' yy' ⟨i, hi⟩
              ≤ muB0 A' B' * By B' yy' ⟨i, hi⟩ := Hyy' ⟨i, hi⟩
          have : Ay A yy' i < muB0 A B * By B yy' i := by
            have hAy'_Ay : Ay A' yy' ⟨i, hi⟩ = Ay A yy' i := rfl
            have hBy'_By : By B' yy' ⟨i, hi⟩ = By B yy' i := rfl
            have hBypos : 0 < By B yy' i := By_pos hB yy' i
            calc Ay A yy' i
                = Ay A' yy' ⟨i, hi⟩ := hAy'_Ay.symm
              _ ≤ muB0 A' B' * By B' yy' ⟨i, hi⟩ := hyy'_i
              _ = muB0 A' B' * By B yy' i := by rw [hBy'_By]
              _ < muB0 A B * By B yy' i :=
                  (mul_lt_mul_iff_of_pos_right hBypos).mpr muB0_gt_muB0'
          unfold rowOffset; linarith
        obtain ⟨t, ht0pos, ht1lt, hstrict_i0_raw⟩ :
            ∃ t : ℝ, 0 < t ∧ t < 1 ∧
              0 < t * rowOffset A B (muB0 A B) yy i₀
                + (1 - t) * rowOffset A B (muB0 A B) yy' i₀ :=
          mix_gt_of_gt_nbh _ _ _ HI
        have ht₀ : 0 ≤ t := le_of_lt ht0pos
        have ht₁ : t ≤ 1 := le_of_lt ht1lt
        have hstrict_i0 :
            0 < rowOffset A B (muB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ yy yy') i₀ := by
          rw [rowOffset_mix]; exact hstrict_i0_raw
        have hAll : ∀ i,
            0 < rowOffset A B (muB0 A B)
                  (stdSimplex.mix t ht₀ ht₁ yy yy') i := by
          intro i
          by_cases hi : i = i₀
          · rw [hi]; exact hstrict_i0
          · rw [rowOffset_mix]
            exact linear_comb_gt_of_ge_gt
              (rowOffset A B (muB0 A B) yy i)
              (rowOffset A B (muB0 A B) yy' i) 0
              (HyyOff i) (HyyOff' i hi) ht₀ ht1lt
        have hlt' : muB.aux A B (stdSimplex.mix t ht₀ ht₁ yy yy') < muB0 A B :=
          muB.aux_lt_of_rowOffset_pos hB hAll
        have hge : muB0 A B ≤ muB.aux A B (stdSimplex.mix t ht₀ ht₁ yy yy') :=
          muB.aux.ge_muB0 hB _
        linarith

/-- **Loomis scalar equality**: every finite positive-`B` matrix pair over `ℝ`
has equal maxmin and minmax Loomis ratios. -/
theorem loomis_value_eq (A B : I → J → ℝ) (hB : IsPositive B) :
    lamB0 A B = muB0 A B := by
  let n := Fintype.card I + Fintype.card J
  have ngetwo : 2 ≤ n := by
    have p1 : 1 ≤ Fintype.card I := Fintype.card_pos
    have p2 : 1 ≤ Fintype.card J := Fintype.card_pos
    omega
  exact loomis_value_eq_aux n ngetwo rfl A B hB

/-! ### Packaged Loomis theorem -/

/-- **Loomis Theorem** [MFoGT, Theorem 2.5.1].

For any pair of matrices `A B : I → J → ℝ` with `B` entrywise positive,
there exist mixed strategies `x : Δ(I)`, `y : Δ(J)` and a value `v : ℝ`
such that for every column `j ∈ J` and every row `i ∈ I`,
$$
  v \cdot (xB)_j \le (xA)_j, \qquad (Ay)_i \le v \cdot (By)_i.
$$
The common value `v = lamB0 A B = muB0 A B`. -/
theorem loomis_theorem (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) (v : ℝ),
      (∀ j, v * xB B x j ≤ xA A x j) ∧
      (∀ i, Ay A y i ≤ v * By B y i) := by
  obtain ⟨x, Hx⟩ := exists_xx_lamB0 A B hB
  obtain ⟨y, Hy⟩ := exists_yy_muB0 A B hB
  refine ⟨x, y, lamB0 A B, Hx, fun i => ?_⟩
  rw [loomis_value_eq A B hB]
  exact Hy i

/-! ### Corollary: simplified Loomis = `B = 1` specialisation

The simplified-Loomis development in `MinimaxLoomis` proves
`lam0 A = mu0 A` directly by inlining the `B = 𝟙` specialisation of the
induction. This section re-derives that statement from the general
positive-`B` Loomis theorem above, validating the
`minimax_from_loomis` blueprint node's "all-ones specialisation"
claim. -/

private theorem xB_one (x : stdSimplex ℝ I) (j : J) :
    xB (fun (_ : I) (_ : J) => (1 : ℝ)) x j = 1 := by
  unfold xB
  exact wsum_const x 1

private theorem By_one (y : stdSimplex ℝ J) (i : I) :
    By (fun (_ : I) (_ : J) => (1 : ℝ)) y i = 1 := by
  unfold By
  exact wsum_const y 1

private theorem colRatio_one (A : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) :
    colRatio A (fun _ _ => 1) x j = wsum x (fun i => A i j) := by
  unfold colRatio
  rw [xB_one]
  unfold xA
  exact div_one _

private theorem rowRatio_one (A : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) :
    rowRatio A (fun _ _ => 1) y i = wsum y (fun j => A i j) := by
  unfold rowRatio
  rw [By_one]
  unfold Ay
  exact div_one _

private theorem lamB.aux_one (A : I → J → ℝ) (x : stdSimplex ℝ I) :
    lamB.aux A (fun _ _ => 1) x = MinimaxLoomis.lam.aux A x := by
  unfold lamB.aux MinimaxLoomis.lam.aux
  congr 1; ext j
  exact colRatio_one A x j

private theorem muB.aux_one (A : I → J → ℝ) (y : stdSimplex ℝ J) :
    muB.aux A (fun _ _ => 1) y = MinimaxLoomis.mu.aux A y := by
  unfold muB.aux MinimaxLoomis.mu.aux
  congr 1; ext i
  exact rowRatio_one A y i

theorem lamB0_one (A : I → J → ℝ) :
    lamB0 A (fun _ _ => 1) = MinimaxLoomis.lam0 A := by
  unfold lamB0 MinimaxLoomis.lam0
  exact iSup_congr (lamB.aux_one A)

theorem muB0_one (A : I → J → ℝ) :
    muB0 A (fun _ _ => 1) = MinimaxLoomis.mu0 A := by
  unfold muB0 MinimaxLoomis.mu0
  exact iInf_congr (muB.aux_one A)

/-- **Simplified Loomis as a corollary** of the general theorem: the finite
von Neumann minimax `MinimaxLoomis.lam0 A = MinimaxLoomis.mu0 A` follows by
instantiating `loomis_value_eq` at the all-ones matrix `B = 𝟙`.

This is the canonical "B = 𝟙 specialisation" route recorded by the
[[minimax_from_loomis]] blueprint node, and the **sole** route to the finite
von Neumann minimax: `MinimaxLoomis` keeps only the shared foundational layer
(aggregates, attainment, weak duality, drop/extend infra), and its scalar
equality is exported here rather than re-proved by a standalone induction. -/
theorem minmax_from_general (A : I → J → ℝ) :
    MinimaxLoomis.lam0 A = MinimaxLoomis.mu0 A := by
  have h := loomis_value_eq A (fun _ _ => 1) IsPositive.one
  rw [lamB0_one, muB0_one] at h
  exact h

end Loomis
