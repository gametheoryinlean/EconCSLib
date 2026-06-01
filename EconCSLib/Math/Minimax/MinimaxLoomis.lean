/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Simplex
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.Compact

/-!
# EconCSLib.Math.Minimax.MinimaxLoomis

LRS-style "simplified Loomis" proof of the finite minimax theorem.

This file ports the layered scaffolding from
[math-xmum/gametheory](https://github.com/math-xmum/gametheory)'s
`GameTheory/Zerosum.lean`. It is specialised to `ℝ` because the strategy
spaces use compactness + continuity for the existence of optimisers — the
ordered-field generalisation (any linearly ordered field) is
`Minimax.minimax`, proved separately by von Neumann symmetrisation.

This file provides the **foundational layer** for the simplified-Loomis
(von Neumann) minimax theorem: the mixed-strategy aggregates
`lam.aux` / `mu.aux`, the scalar values `lam0` / `mu0`, existence of
optimisers via compactness, weak duality `lam0 ≤ mu0`, and the
column/row dropping infrastructure (`extendDropColumn` / `extendDropRow`)
reused by the general development.

The scalar equality `lam0 A = mu0 A` is **not** re-proved here by a
standalone induction. It is the `B = 𝟙` specialisation of the general
(positive-`B`) Loomis theorem, exported as
`Loomis.minmax_from_general`. (Earlier revisions carried an inlined
copy of that induction, `minmax'`; it was removed as redundant once the
general proof subsumed it.)

## Attribution

Ported from `GameTheory/Zerosum.lean` in
[math-xmum/gametheory](https://github.com/math-xmum/gametheory).
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace MinimaxLoomis

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-! ### Expected payoff in mixed strategies -/

/-- Expected payoff of a matrix game `A : I → J → ℝ` under mixed strategies
`x : stdSimplex ℝ I` and `y : stdSimplex ℝ J`. -/
noncomputable def E (A : I → J → ℝ) (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) : ℝ :=
  wsum x (fun i => wsum y (A i))

/-! ### Row aggregate `lam.aux` and its scalar value `lam0` -/

/-- Player I's guaranteed payoff from mixed strategy `x`: the minimum over
pure columns of the expected payoff. -/
noncomputable def lam.aux (A : I → J → ℝ) (x : stdSimplex ℝ I) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun j => wsum x (fun i => A i j))

/-- Player I's maxmin value (the row player's best guarantee). -/
noncomputable def lam0 (A : I → J → ℝ) : ℝ := iSup (lam.aux A)

/-- `lam.aux A x > c` iff every pure-column expected payoff exceeds `c`. -/
theorem lam.aux_gt_iff_gt (A : I → J → ℝ) (c : ℝ) (x : stdSimplex ℝ I) :
    c < lam.aux A x ↔ ∀ j, c < wsum x (fun i => A i j) := by
  simp [lam.aux, Finset.lt_inf'_iff]

/-- `lam.aux A` is continuous as a function of the simplex point. -/
theorem lam.aux.continuous (A : I → J → ℝ) :
    Continuous (lam.aux A) := by
  refine Continuous.finset_inf'_apply Finset.univ_nonempty ?_
  intro j _
  exact wsum_continuous (fun i => A i j)

/-- `lam.aux A` is uniformly bounded above on the simplex. -/
theorem lam.aux.bddAbove (A : I → J → ℝ) :
    ∃ C, ∀ x, lam.aux A x ≤ C := by
  classical
  let C0 : ℝ :=
    Finset.sup' Finset.univ Finset.univ_nonempty
      (fun i => Finset.sup' Finset.univ Finset.univ_nonempty (A i))
  have hAij : ∀ i j, A i j ≤ C0 := by
    intro i j
    calc A i j
        ≤ Finset.sup' Finset.univ Finset.univ_nonempty (A i) :=
          Finset.le_sup' _ (Finset.mem_univ _)
      _ ≤ C0 :=
          Finset.le_sup'
            (fun i => Finset.sup' Finset.univ Finset.univ_nonempty (A i))
            (Finset.mem_univ _)
  refine ⟨C0, fun x => ?_⟩
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have hcol : wsum x (fun i => A i j₀) ≤ C0 := by
    calc wsum x (fun i => A i j₀)
        ≤ wsum x (fun _ => C0) := wsum_le_wsum x (fun i => hAij i j₀)
      _ = C0 := wsum_const x C0
  exact (Finset.inf'_le (fun j => wsum x (fun i => A i j))
    (Finset.mem_univ j₀)).trans hcol

/-- The supremum `lam0` dominates every `lam.aux` value. -/
theorem lam.aux.le_lam0 (A : I → J → ℝ) (x : stdSimplex ℝ I) :
    lam.aux A x ≤ lam0 A :=
  le_ciSup (bddAbove_def.2 (by
    obtain ⟨C, hC⟩ := lam.aux.bddAbove A
    exact ⟨C, by rintro r ⟨x, rfl⟩; exact hC x⟩)) x

/-- There exists a mixed strategy `xx` whose column-payoffs all dominate
`lam0 A`. Compactness + continuity gives a maximiser of `lam.aux`; that
maximiser realises the supremum and beats every pure-column expectation. -/
theorem exists_xx_lam0 (A : I → J → ℝ) :
    ∃ xx : stdSimplex ℝ I, ∀ j, lam0 A ≤ wsum xx (fun i => A i j) := by
  obtain ⟨xx, _, hxx⟩ :=
    isCompact_univ.exists_isMaxOn (α := ℝ) (β := stdSimplex ℝ I)
      Set.univ_nonempty (lam.aux.continuous A).continuousOn
  rw [isMaxOn_iff] at hxx
  refine ⟨xx, fun j => ?_⟩
  have h1 : lam0 A ≤ lam.aux A xx := ciSup_le fun y => hxx y (Set.mem_univ _)
  have h2 : lam.aux A xx ≤ wsum xx (fun i => A i j) :=
    Finset.inf'_le _ (Finset.mem_univ j)
  exact h1.trans h2

/-! ### Column aggregate `mu.aux` and its scalar value `mu0` -/

/-- Player II's maximum loss against mixed strategy `y`: the maximum over
pure rows of the expected payoff. -/
noncomputable def mu.aux (A : I → J → ℝ) (y : stdSimplex ℝ J) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => wsum y (fun j => A i j))

/-- Player II's minmax value (the column player's best cap). -/
noncomputable def mu0 (A : I → J → ℝ) : ℝ := iInf (mu.aux A)

/-- `mu.aux A y < c` iff every pure-row expected payoff is below `c`. -/
theorem mu.aux_lt_iff_lt (A : I → J → ℝ) (c : ℝ) (y : stdSimplex ℝ J) :
    mu.aux A y < c ↔ ∀ i, wsum y (fun j => A i j) < c := by
  simp [mu.aux, Finset.sup'_lt_iff]

/-- `mu.aux A` is continuous as a function of the simplex point. -/
theorem mu.aux.continuous (A : I → J → ℝ) :
    Continuous (mu.aux A) := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty ?_
  intro i _
  exact wsum_continuous (fun j => A i j)

/-- `mu.aux A` is uniformly bounded below on the simplex. -/
theorem mu.aux.bddBelow (A : I → J → ℝ) :
    ∃ C, ∀ y, C ≤ mu.aux A y := by
  classical
  let C0 : ℝ :=
    Finset.inf' Finset.univ Finset.univ_nonempty
      (fun j => Finset.inf' Finset.univ Finset.univ_nonempty (fun i => A i j))
  have hAij : ∀ i j, C0 ≤ A i j := by
    intro i j
    calc C0
        ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun i => A i j) :=
          Finset.inf'_le _ (Finset.mem_univ _)
      _ ≤ A i j := Finset.inf'_le _ (Finset.mem_univ _)
  refine ⟨C0, fun y => ?_⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hrow : C0 ≤ wsum y (fun j => A i₀ j) := by
    calc C0 = wsum y (fun _ => C0) := (wsum_const y C0).symm
      _ ≤ wsum y (fun j => A i₀ j) := wsum_le_wsum y (fun j => hAij i₀ j)
  exact hrow.trans (Finset.le_sup' (fun i => wsum y (fun j => A i j))
    (Finset.mem_univ i₀))

/-- The infimum `mu0` is dominated by every `mu.aux` value. -/
theorem mu.aux.ge_mu0 (A : I → J → ℝ) (y : stdSimplex ℝ J) :
    mu0 A ≤ mu.aux A y :=
  ciInf_le (bddBelow_def.2 (by
    obtain ⟨C, hC⟩ := mu.aux.bddBelow A
    exact ⟨C, by rintro r ⟨y, rfl⟩; exact hC y⟩)) y

/-- There exists a mixed strategy `yy` whose row-payoffs are all dominated by
`mu0 A`. -/
theorem exists_yy_mu0 (A : I → J → ℝ) :
    ∃ yy : stdSimplex ℝ J, ∀ i, wsum yy (fun j => A i j) ≤ mu0 A := by
  obtain ⟨yy, _, hyy⟩ :=
    isCompact_univ.exists_isMinOn (α := ℝ) (β := stdSimplex ℝ J)
      Set.univ_nonempty (mu.aux.continuous A).continuousOn
  rw [isMinOn_iff] at hyy
  refine ⟨yy, fun i => ?_⟩
  have h1 : mu.aux A yy ≤ mu0 A := le_ciInf fun z => hyy z (Set.mem_univ _)
  have h2 : wsum yy (fun j => A i j) ≤ mu.aux A yy :=
    Finset.le_sup' (f := fun i => wsum yy (fun j => A i j)) (Finset.mem_univ i)
  exact h2.trans h1

/-! ### Weak duality: `lam0 ≤ mu0` -/

/-- Weak duality for the two-player zero-sum matrix game: every maxmin value
is bounded by every minmax value. -/
theorem lam0_le_mu0 (A : I → J → ℝ) : lam0 A ≤ mu0 A := by
  obtain ⟨xx, Hxx⟩ := exists_xx_lam0 A
  obtain ⟨yy, Hyy⟩ := exists_yy_mu0 A
  calc lam0 A
      ≤ E A xx yy := by
        rw [E, wsum_wsum_comm]
        exact (ge_iff_simplex_ge.mp Hxx) yy
    _ ≤ mu0 A := by
        rw [E]
        exact (le_iff_simplex_le.mp Hyy) xx

/-! ### Singleton reduction for `|I| = |J| = 1`

`singleton_of_card_one` is the shared helper feeding the base case of the
general Loomis induction in `Loomis`. -/

/-- When the row index type has cardinality 1, every simplex point is the
unique pure strategy and `Finset.univ` is a singleton. -/
theorem singleton_of_card_one {K : Type*} [Fintype K] [DecidableEq K]
    (H : Fintype.card K = 1) :
    ∃ a : K, (Finset.univ : Finset K) = {a} := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 H
  exact ⟨a, by ext; simp [ha]⟩

/-! ### Restricting a matrix game by dropping a column / row -/

/-- The equivalence `J ≃ Option {j // j ≠ j₀}`: `j₀ ↦ none`, other `j ↦ some j`. -/
noncomputable def dropEquiv [DecidableEq J] (j₀ : J) : J ≃ Option {j : J // j ≠ j₀} where
  toFun j := if h : j = j₀ then none else some ⟨j, h⟩
  invFun o := match o with | none => j₀ | some j => j.val
  left_inv j := by by_cases h : j = j₀ <;> simp [h]
  right_inv o := by cases o with
    | none => simp
    | some j => simp [j.property]

/-- Sum-splitting lemma: any function on `J` decomposes as the value at `j₀`
plus the sum over `{j // j ≠ j₀}`. -/
theorem sum_split_at [DecidableEq J] (j₀ : J) (f : J → ℝ) :
    ∑ j : J, f j = f j₀ + ∑ j' : {j : J // j ≠ j₀}, f j'.val := by
  have hbij : ∑ j : J, f j =
      ∑ o : Option {j : J // j ≠ j₀}, f ((dropEquiv j₀).symm o) :=
    Fintype.sum_equiv (dropEquiv j₀) f (fun o => f ((dropEquiv j₀).symm o))
      (fun j => by simp)
  rw [hbij, Fintype.sum_option]
  rfl

/-- Extend a mixed strategy on `J' = {j // j ≠ j₀}` to a mixed strategy on `J`
by putting zero mass on `j₀`. -/
noncomputable def extendDropColumn [DecidableEq J] (j₀ : J)
    (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    stdSimplex ℝ J := by
  refine ⟨fun j => if h : j = j₀ then 0 else y'.val ⟨j, h⟩, ?_, ?_⟩
  · intro j
    by_cases h : j = j₀
    · simp [h]
    · simp [h]; exact y'.property.1 ⟨j, h⟩
  · rw [sum_split_at j₀]
    have h0 : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) = 0 := by simp
    rw [h0, zero_add]
    have : ∀ j' : {j : J // j ≠ j₀},
        (if h : j'.val = j₀ then (0 : ℝ) else y'.val ⟨j'.val, h⟩) = y'.val j' := by
      intro j'; simp [j'.property]
    simp_rw [this]
    exact y'.property.2

/-- Dual: extend a mixed strategy on `I' = {i // i ≠ i₀}` to one on `I`. -/
noncomputable def extendDropRow [DecidableEq I] (i₀ : I)
    (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    stdSimplex ℝ I :=
  extendDropColumn (J := I) i₀ x'

/-- `wsum (extendDropColumn j₀ y') f` equals the `wsum` of `y'` restricted
to the corresponding sub-function on `{j // j ≠ j₀}`. -/
theorem wsum_extendDropColumn [DecidableEq J] (j₀ : J)
    (y' : stdSimplex ℝ {j : J // j ≠ j₀}) (f : J → ℝ) :
    wsum (extendDropColumn j₀ y') f
      = ∑ j' : {j : J // j ≠ j₀}, y'.val j' * f j'.val := by
  change (∑ j, (if h : j = j₀ then (0 : ℝ) else y'.val ⟨j, h⟩) * f j)
       = ∑ j' : {j : J // j ≠ j₀}, y'.val j' * f j'.val
  rw [sum_split_at j₀]
  have h0 : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) * f j₀ = 0 := by
    have : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) = 0 := by simp
    rw [this, zero_mul]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro j' _
  congr 1
  simp [j'.property]

/-- Companion for row extension. -/
theorem wsum_extendDropRow [DecidableEq I] (i₀ : I)
    (x' : stdSimplex ℝ {i : I // i ≠ i₀}) (f : I → ℝ) :
    wsum (extendDropRow i₀ x') f
      = ∑ i' : {i : I // i ≠ i₀}, x'.val i' * f i'.val :=
  wsum_extendDropColumn (J := I) i₀ x' f

end MinimaxLoomis
