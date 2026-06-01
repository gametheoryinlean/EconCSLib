/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
import EconCSLib.Math.Minimax.Minimax

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash

Existence of a mixed Nash equilibrium for a finite matrix game.

## Main statements

* `MatrixGame.IsMixedNashEq xx yy` — saddle-point definition: `xx` is a best
  response to `yy` for the row player, and `yy` is a best response to `xx`
  for the column player (zero-sum convention: column player minimises the
  same `A`).
* `MatrixGame.exists_mixed_nash_equilibrium` — every finite matrix game **over
  any linearly ordered field** has a pair `(xx, yy)` satisfying `IsMixedNashEq`;
  packaged from `Minimax.minimax` (von Neumann symmetrisation).
* `MatrixGame.toStrategicGame` — the explicit two-player zero-sum strategic
  game whose mixed Nash equilibria correspond to saddle points of `A`.

The intermediate `IsMixedNashEq` defined here is on the matrix game itself
(not on the strategic-game embedding) because it is exactly the textbook
statement of "matrix game has a value" and is easier to reason about than
the dependently-typed `Fin 2`-indexed strategic game.

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Theorems 5.11 and 5.13.
* [LRS] Laraki, Renault, Sorin, *Mathematical Foundations of Game Theory*,
  Theorem 2.3.1.
-/

open Finset BigOperators

set_option linter.unusedSectionVars false

namespace MatrixGame

-- The strategic-game embedding below uses a single `strategy : Fin 2 → Type u`,
-- so we constrain `I` and `J` to live at the same universe.
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
variable (A : MatrixGame I J ℝ)

/-! ### Saddle-point mixed Nash equilibrium -/

/-- Saddle-point form of a mixed Nash equilibrium for a matrix game.

    For zero-sum two-player games, the standard mixed-strategy Nash
    equilibrium is exactly the saddle point of the bilinear payoff: the row
    player cannot improve by deviating to any mixed row, and the column
    player cannot improve (i.e., decrease the row player's payoff) by
    deviating to any mixed column.

    Field-generic: the saddle-point inequalities only need a linearly ordered
    field, not order-completeness. -/
def IsMixedNashEq {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : Prop :=
  (∀ x' : stdSimplex 𝕜 I, A.E x' yy ≤ A.E xx yy) ∧
  (∀ y' : stdSimplex 𝕜 J, A.E xx yy ≤ A.E xx y')

/-- A pair of mixed strategies is a **saddle point** when player I's payoff is
maximised by the row strategy against the column strategy and minimised by
the column strategy against the row strategy. For a matrix game this is
synonymous with the mixed Nash equilibrium predicate
[`MatrixGame.IsMixedNashEq`]. -/
abbrev IsSaddlePoint {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : Prop :=
  A.IsMixedNashEq xx yy

/-- **Nash equilibrium ↔ saddle point** for matrix games. Both sides unfold to
the same saddle-point inequality system; the equivalence is therefore
definitional. -/
theorem isMixedNashEq_iff_isSaddlePoint
    {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) :
    A.IsMixedNashEq xx yy ↔ A.IsSaddlePoint xx yy := Iff.rfl

/-- The **value** of a matrix game (`sSup`-based; needs order completeness).

Equal to both maximin and minimax by the minimax theorem
([`MatrixGame.minimax_theorem`]); the maximin = minimax equality is the
ℝ-bound piece (Loomis). Field-generic existence of a value (without
`sSup`) is the `IsValue` predicate in `Minimax.lean`. -/
noncomputable def value {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : 𝕜 := A.maximin

theorem value_eq_maximin {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : A.value = A.maximin := rfl

theorem value_eq_minimax : A.value = A.minimax := A.minimax_theorem

/-- **Point-wise duality gap** at a strategy pair: the column player's
realised loss-cap minus the row player's realised guarantee.
Always nonnegative, zero exactly at optimal pairs.

Field-generic: just the difference of two L2 guarantees, no sup/inf. -/
noncomputable def dualityGap {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : 𝕜 :=
  A.guarantee_II yy - A.guarantee_I xx

/-- The set of **optimal row strategies**: mixed strategies that achieve the
maximin value. -/
def optimalRowStrategies {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : Set (stdSimplex 𝕜 I) :=
  { xx | A.guarantee_I xx = A.value }

/-- The set of **optimal column strategies**: mixed strategies that achieve
the minimax value. -/
def optimalColumnStrategies {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : Set (stdSimplex 𝕜 J) :=
  { yy | A.guarantee_II yy = A.value }

/-- An **ε-optimal row strategy** guarantees at least `value - ε`. -/
def IsEpsilonOptimalRow {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (ε : 𝕜) (xx : stdSimplex 𝕜 I) : Prop :=
  A.value - ε ≤ A.guarantee_I xx

/-- An **ε-optimal column strategy** caps player I's payoff at `value + ε`. -/
def IsEpsilonOptimalColumn {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (ε : 𝕜) (yy : stdSimplex 𝕜 J) : Prop :=
  A.guarantee_II yy ≤ A.value + ε

/-- `w` is a **guarantee for player I** when some mixed row strategy achieves
expected payoff `≥ w` against every pure column. Equivalent to `w ≤ A.maximin`. -/
def IsPlayerIGuarantee {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (w : 𝕜) : Prop :=
  ∃ xx : stdSimplex 𝕜 I, ∀ j, w ≤ A.Ej xx j

/-- `w` is a **guarantee for player II** when some mixed column strategy caps
expected payoff `≤ w` against every pure row. Equivalent to `A.minimax ≤ w`. -/
def IsPlayerIIGuarantee {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (w : 𝕜) : Prop :=
  ∃ yy : stdSimplex 𝕜 J, ∀ i, A.Ei i yy ≤ w

/-- **Support** of a mixed strategy: the indices with positive probability. -/
noncomputable def support {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [DecidableEq I] (xx : stdSimplex 𝕜 I) : Finset I :=
  Finset.univ.filter (fun i => 0 < xx.val i)

/-! ### Optimal pairs ↔ saddle points -/

/-- A row strategy is optimal iff against every mixed column it secures the
value. -/
theorem mem_optimalRowStrategies_iff_E_ge (xx : stdSimplex ℝ I) :
    xx ∈ A.optimalRowStrategies ↔ ∀ y' : stdSimplex ℝ J, A.value ≤ A.E xx y' := by
  classical
  unfold optimalRowStrategies
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hxx y'
    have hj : ∀ j, A.value ≤ A.Ej xx j := by
      intro j
      have : A.guarantee_I xx ≤ A.Ej xx j :=
        Finset.inf'_le (fun j => A.Ej xx j) (Finset.mem_univ j)
      linarith [hxx]
    have heq : A.E xx y' = wsum y' (fun j => A.Ej xx j) := by
      show wsum xx (fun i => wsum y' (A.g i)) = wsum y' (fun j => wsum xx (fun i => A.g i j))
      exact wsum_wsum_comm xx y' A.g
    rw [heq]
    exact (ge_iff_simplex_ge.mp hj) y'
  · intro h
    have hj : ∀ j, A.value ≤ A.Ej xx j := by
      intro j
      have := h (stdSimplex.pure j)
      have heq : A.E xx (stdSimplex.pure j) = A.Ej xx j := by
        show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = wsum xx (fun i => A.g i j)
        apply Finset.sum_congr rfl
        intro i _
        show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
        rw [wsum_pure_apply]
      rwa [heq] at this
    have hge : A.value ≤ A.guarantee_I xx := by
      show A.value ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
      rw [Finset.le_inf'_iff]; intro j _; exact hj j
    have hle : A.guarantee_I xx ≤ A.value := by
      have hmax : A.guarantee_I xx ≤ A.maximin :=
        le_ciSup (bddAbove_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
      have hv : A.value = A.maximin := A.value_eq_maximin
      linarith
    linarith

/-- A column strategy is optimal iff against every mixed row it caps payoff
at the value. -/
theorem mem_optimalColumnStrategies_iff_E_le (yy : stdSimplex ℝ J) :
    yy ∈ A.optimalColumnStrategies ↔ ∀ x' : stdSimplex ℝ I, A.E x' yy ≤ A.value := by
  classical
  unfold optimalColumnStrategies
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hyy x'
    have hi : ∀ i, A.Ei i yy ≤ A.value := by
      intro i
      have : A.Ei i yy ≤ A.guarantee_II yy :=
        Finset.le_sup' (fun i => A.Ei i yy) (Finset.mem_univ i)
      linarith [hyy]
    have heq : A.E x' yy = wsum x' (fun i => A.Ei i yy) := rfl
    rw [heq]
    exact (le_iff_simplex_le.mp hi) x'
  · intro h
    have hi : ∀ i, A.Ei i yy ≤ A.value := by
      intro i
      have := h (stdSimplex.pure i)
      have heq : A.E (stdSimplex.pure i) yy = A.Ei i yy := by
        show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = wsum yy (A.g i)
        rw [wsum_pure_apply]
      rwa [heq] at this
    have hle : A.guarantee_II yy ≤ A.value := by
      show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ A.value
      rw [Finset.sup'_le_iff]; intro i _; exact hi i
    have hge : A.value ≤ A.guarantee_II yy := by
      have hv := A.value_eq_minimax
      have : A.minimax ≤ A.guarantee_II yy :=
        ciInf_le (bddBelow_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
      linarith
    linarith

/-- **Support complementarity (row).** For an optimal pair `(xx, yy)`, every
row `i` with positive probability under `xx` is a best response to `yy`,
i.e., `A.Ei i yy = A.value`. -/
theorem support_complementarity_row [DecidableEq I]
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J)
    (hxx : xx ∈ A.optimalRowStrategies) (hyy : yy ∈ A.optimalColumnStrategies)
    {i : I} (hi : 0 < xx.val i) :
    A.Ei i yy = A.value := by
  have hE_eq : A.E xx yy = A.value := by
    have h1 := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx yy
    have h2 := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy xx
    linarith
  have hi_le : ∀ i', A.Ei i' yy ≤ A.value := by
    intro i'
    have h := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy (stdSimplex.pure i')
    have heq : A.E (stdSimplex.pure i') yy = A.Ei i' yy := by
      show wsum (stdSimplex.pure i') (fun i'' => wsum yy (A.g i'')) = wsum yy (A.g i')
      rw [wsum_pure_apply]
    linarith [heq]
  have hsum_one : (∑ i', xx.val i') = 1 := xx.property.2
  have hsum_zero : (∑ i', xx.val i' * (A.value - A.Ei i' yy)) = 0 := by
    have hexpand : (∑ i', xx.val i' * (A.value - A.Ei i' yy))
        = (∑ i', xx.val i') * A.value - (∑ i', xx.val i' * A.Ei i' yy) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i' _; ring
    rw [hexpand, hsum_one, one_mul]
    show A.value - A.E xx yy = 0
    linarith
  have hnonneg : ∀ i' ∈ Finset.univ, 0 ≤ xx.val i' * (A.value - A.Ei i' yy) := by
    intro i' _
    exact mul_nonneg (xx.property.1 i') (sub_nonneg.mpr (hi_le i'))
  have hzero : xx.val i * (A.value - A.Ei i yy) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith

/-- **Support complementarity (column).** For an optimal pair `(xx, yy)`, every
column `j` with positive probability under `yy` is a best response to `xx`,
i.e., `A.Ej xx j = A.value`. -/
theorem support_complementarity_column [DecidableEq J]
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J)
    (hxx : xx ∈ A.optimalRowStrategies) (hyy : yy ∈ A.optimalColumnStrategies)
    {j : J} (hj : 0 < yy.val j) :
    A.Ej xx j = A.value := by
  have hE_eq : A.E xx yy = A.value := by
    have h1 := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx yy
    have h2 := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy xx
    linarith
  have hj_ge : ∀ j', A.value ≤ A.Ej xx j' := by
    intro j'
    have h := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx (stdSimplex.pure j')
    have heq : A.E xx (stdSimplex.pure j') = A.Ej xx j' := by
      show wsum xx (fun i => wsum (stdSimplex.pure j') (A.g i)) = wsum xx (fun i => A.g i j')
      apply Finset.sum_congr rfl
      intro i _
      show xx.val i * wsum (stdSimplex.pure j') (A.g i) = xx.val i * A.g i j'
      rw [wsum_pure_apply]
    linarith [heq]
  -- Express E xx yy as a column-side weighted sum: ∑ j, yy.val j * Ej xx j.
  have hE_col : A.E xx yy = ∑ j', yy.val j' * A.Ej xx j' := by
    show wsum xx (fun i => wsum yy (A.g i)) = ∑ j', yy.val j' * (wsum xx (fun i => A.g i j'))
    rw [wsum_wsum_comm xx yy A.g]
    rfl
  have hsum_one : (∑ j', yy.val j') = 1 := yy.property.2
  have hsum_zero : (∑ j', yy.val j' * (A.Ej xx j' - A.value)) = 0 := by
    have hexpand : (∑ j', yy.val j' * (A.Ej xx j' - A.value))
        = (∑ j', yy.val j' * A.Ej xx j') - (∑ j', yy.val j') * A.value := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j' _; ring
    rw [hexpand, hsum_one, one_mul, ← hE_col]
    linarith
  have hnonneg : ∀ j' ∈ Finset.univ, 0 ≤ yy.val j' * (A.Ej xx j' - A.value) := by
    intro j' _
    exact mul_nonneg (yy.property.1 j') (sub_nonneg.mpr (hj_ge j'))
  have hzero : yy.val j * (A.Ej xx j - A.value) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith

/-- **Common guarantee gives the value.** If both players guarantee the same
scalar `w`, then `w` equals the game value. -/
theorem common_guarantee_eq_value (w : ℝ)
    (h1 : A.IsPlayerIGuarantee w) (h2 : A.IsPlayerIIGuarantee w) :
    w = A.value := by
  obtain ⟨xx, hxx⟩ := h1
  obtain ⟨yy, hyy⟩ := h2
  have hw_le_GI : w ≤ A.guarantee_I xx := by
    show w ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
    rw [Finset.le_inf'_iff]; intro j _; exact hxx j
  have hGII_le_w : A.guarantee_II yy ≤ w := by
    show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ w
    rw [Finset.sup'_le_iff]; intro i _; exact hyy i
  have h_GI_max : A.guarantee_I xx ≤ A.maximin :=
    le_ciSup (bddAbove_def.2 (by
      obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
      exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
  have h_min_GII : A.minimax ≤ A.guarantee_II yy :=
    ciInf_le (bddBelow_def.2 (by
      obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
      exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
  have hvm := A.minimax_theorem
  have hvval := A.value_eq_maximin
  linarith

/-- **Optimal pairs ↔ saddle points.** A pair of mixed strategies is in the
product `X(A) × Y(A)` of optimal strategy sets iff it is a saddle point. -/
theorem optimal_pairs_iff_saddle_point
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J) :
    (xx ∈ A.optimalRowStrategies ∧ yy ∈ A.optimalColumnStrategies)
      ↔ A.IsSaddlePoint xx yy := by
  rw [A.mem_optimalRowStrategies_iff_E_ge, A.mem_optimalColumnStrategies_iff_E_le]
  refine ⟨?_, ?_⟩
  · rintro ⟨hxx, hyy⟩
    have hE : A.E xx yy = A.value := le_antisymm (hyy xx) (hxx yy)
    refine ⟨fun x' => ?_, fun y' => ?_⟩
    · calc A.E x' yy ≤ A.value := hyy x'
        _ = A.E xx yy := hE.symm
    · calc A.E xx yy = A.value := hE
        _ ≤ A.E xx y' := hxx y'
  · rintro ⟨hsad_row, hsad_col⟩
    classical
    have hjE : ∀ j, A.E xx yy ≤ A.Ej xx j := by
      intro j
      have := hsad_col (stdSimplex.pure j)
      have heq : A.E xx (stdSimplex.pure j) = A.Ej xx j := by
        show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = wsum xx (fun i => A.g i j)
        apply Finset.sum_congr rfl
        intro i _
        show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
        rw [wsum_pure_apply]
      linarith [heq]
    have hiE : ∀ i, A.Ei i yy ≤ A.E xx yy := by
      intro i
      have := hsad_row (stdSimplex.pure i)
      have heq : A.E (stdSimplex.pure i) yy = A.Ei i yy := by
        show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = wsum yy (A.g i)
        rw [wsum_pure_apply]
      linarith [heq]
    have hGI : A.E xx yy ≤ A.guarantee_I xx := by
      show A.E xx yy ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
      rw [Finset.le_inf'_iff]; intro j _; exact hjE j
    have hGII : A.guarantee_II yy ≤ A.E xx yy := by
      show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ A.E xx yy
      rw [Finset.sup'_le_iff]; intro i _; exact hiE i
    have hI_le : A.guarantee_I xx ≤ A.value :=
      le_ciSup (bddAbove_def.2 (by
        obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
        exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
    have hII_ge : A.value ≤ A.guarantee_II yy := by
      have hv := A.value_eq_minimax
      have : A.minimax ≤ A.guarantee_II yy :=
        ciInf_le (bddBelow_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
      linarith
    refine ⟨fun y' => ?_, fun x' => ?_⟩
    · have hEval : A.E xx yy = A.value := by linarith
      calc A.value = A.E xx yy := hEval.symm
        _ ≤ A.E xx y' := hsad_col y'
    · have hEval : A.E xx yy = A.value := by linarith
      calc A.E x' yy ≤ A.E xx yy := hsad_row x'
        _ = A.value := hEval

/-! ### Existence -/

/-- Helper: writing `A.E` as an iterated `wsum` exposes the structure that
    the saddle-point bounds rely on. -/
private theorem E_eq_wsum_wsum
    {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) :
    A.E x y = wsum x (fun i => wsum y (A.g i)) := rfl

/-- Helper: swap order of the iterated `wsum` in `A.E`. -/
private theorem E_eq_wsum_wsum_swap
    {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) :
    A.E x y = wsum y (fun j => wsum x (fun i => A.g i j)) := by
  rw [E_eq_wsum_wsum, wsum_wsum_comm]

/-- **Pure-strategy guarantees give a mixed Nash equilibrium.** If `xx`
guarantees value `v` against every pure column and `yy` caps the row player's
payoff at `v` against every pure row, then `(xx, yy)` is a saddle-point mixed
Nash equilibrium. Field-generic — only the saddle inequalities are used
(no order-completeness). -/
theorem isMixedNashEq_of_pure {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (A : MatrixGame I J 𝕜)
    {xx : stdSimplex 𝕜 I} {yy : stdSimplex 𝕜 J} {v : 𝕜}
    (Hxx : ∀ j, v ≤ wsum xx (fun i => A.g i j))
    (Hyy : ∀ i, wsum yy (A.g i) ≤ v) :
    A.IsMixedNashEq xx yy := by
  refine ⟨?_, ?_⟩
  · -- Row player cannot improve: `A.E x' yy ≤ v ≤ A.E xx yy`.
    intro x'
    have hE_x'_le : A.E x' yy ≤ v := by
      rw [E_eq_wsum_wsum]
      calc wsum x' (fun i => wsum yy (A.g i))
          ≤ wsum x' (fun _ => v) := wsum_le_wsum x' Hyy
        _ = v := wsum_const x' v
    have hE_xx_ge : v ≤ A.E xx yy := by
      rw [E_eq_wsum_wsum_swap]
      calc v = wsum yy (fun _ => v) := (wsum_const yy v).symm
        _ ≤ wsum yy (fun j => wsum xx (fun i => A.g i j)) := wsum_le_wsum yy Hxx
    linarith
  · -- Column player cannot improve: `A.E xx yy ≤ v ≤ A.E xx y'`.
    intro y'
    have hE_xx_le : A.E xx yy ≤ v := by
      rw [E_eq_wsum_wsum]
      calc wsum xx (fun i => wsum yy (A.g i))
          ≤ wsum xx (fun _ => v) := wsum_le_wsum xx Hyy
        _ = v := wsum_const xx v
    have hE_xx_y'_ge : v ≤ A.E xx y' := by
      rw [E_eq_wsum_wsum_swap]
      calc v = wsum y' (fun _ => v) := (wsum_const y' v).symm
        _ ≤ wsum y' (fun j => wsum xx (fun i => A.g i j)) := wsum_le_wsum y' Hxx
    linarith

/-- **Matrix games have a mixed Nash equilibrium — over any linearly ordered
field.** Packages the field-generic saddle `Minimax.minimax` (proved by
von Neumann symmetrisation; no compactness, no order-completeness) into the
`IsMixedNashEq` saddle-point form. The ℝ case is the `𝕜 := ℝ` instance, so all
ℝ consumers are unaffected. -/
theorem exists_mixed_nash_equilibrium {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (A : MatrixGame I J 𝕜) :
    ∃ (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J), A.IsMixedNashEq xx yy := by
  classical
  obtain ⟨x, y, v, hx_nn, hx_sum, hy_nn, hy_sum, hxA, hAy⟩ := Minimax.minimax A.g
  refine ⟨⟨x, hx_nn, hx_sum⟩, ⟨y, hy_nn, hy_sum⟩, ?_⟩
  apply isMixedNashEq_of_pure A (v := v)
  · intro j; exact hxA j
  · intro i
    show (∑ j, y j * A.g i j) ≤ v
    calc (∑ j, y j * A.g i j) = ∑ j, A.g i j * y j :=
          Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ ≤ v := hAy i

/-! ### Strategic-game embedding

A matrix game `A : I → J → 𝕜` lifts to a two-player zero-sum strategic game
with players `Fin 2`, strategy spaces `I` and `J`, and payoffs `A` (for the
row player) and `−A` (for the column player). Polymorphic in the scalar
field `𝕜`. The standard [`StrategicGame.IsMixedNashEq`] then unfolds —
modulo a 2-player profile expansion — to the saddle-point form
`MatrixGame.IsMixedNashEq` above. -/

/-- The two-player zero-sum strategic game associated with a matrix game.

See `MatrixGame.toStrategicGame_isZeroSum` for the proof that this game
satisfies the abstract `StrategicGame.IsZeroSum` predicate, so results stated
against `IsZeroSum` (e.g. `IsZeroSum.nash_payoff_eq`) can be invoked on
`A.toStrategicGame` without re-unfolding the definition. -/
noncomputable def toStrategicGame {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : StrategicGame (Fin 2) 𝕜 where
  strategy
  | 0 => I
  | 1 => J
  payoff σ
  | 0 => A.g (σ 0) (σ 1)
  | 1 => -(A.g (σ 0) (σ 1))

/-- `A.toStrategicGame` satisfies the abstract zero-sum predicate: by
construction player 1's payoff is the negation of player 0's. -/
theorem toStrategicGame_isZeroSum {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) :
    StrategicGame.IsZeroSum A.toStrategicGame := by
  intro σ
  show A.g (σ 0) (σ 1) + -(A.g (σ 0) (σ 1)) = 0
  ring

/-! ### `toStrategicGame` instance synthesis -/

instance {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) [DecidableEq I] [DecidableEq J] (i : Fin 2) :
    DecidableEq (A.toStrategicGame.strategy i) := by
  match i with
  | 0 => exact ‹DecidableEq I›
  | 1 => exact ‹DecidableEq J›

instance {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (i : Fin 2) :
    Fintype (A.toStrategicGame.strategy i) := by
  match i with
  | 0 => exact ‹Fintype I›
  | 1 => exact ‹Fintype J›

instance {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (i : Fin 2) :
    Nonempty (A.toStrategicGame.strategy i) := by
  match i with
  | 0 => exact ‹Nonempty I›
  | 1 => exact ‹Nonempty J›

variable [DecidableEq I] [DecidableEq J]

/-- Build a `MixedProfile` of `toStrategicGame` from a saddle-point pair. -/
noncomputable def toMixedProfile {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) :
    StrategicGame.MixedProfile A.toStrategicGame
  | 0 => xx
  | 1 => yy

@[simp] theorem toMixedProfile_zero {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) :
    A.toMixedProfile xx yy 0 = xx := rfl

@[simp] theorem toMixedProfile_one {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) :
    A.toMixedProfile xx yy 1 = yy := rfl

/-! ### Profile expansion for `Fin 2`

Player-0's strategic-game expected payoff on `toStrategicGame` reduces to
`A.E`, and player-1's to `-A.E`. This is the technical core of the bridge
from saddle-point Nash to `StrategicGame.IsMixedNashEq`. -/

/-- Bridge lemma: `expectedPayoff A.toStrategicGame p 0 = A.E (p 0) (p 1)`.
    Reduces both sides to the canonical double sum
    `∑ i, ∑ j, (p 0)ᵢ · (p 1)ⱼ · A i j`. -/
theorem expectedPayoff_toStrategicGame_zero {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (p : StrategicGame.MixedProfile A.toStrategicGame) :
    StrategicGame.expectedPayoff A.toStrategicGame p 0
      = A.E (p 0) (p 1) := by
  let double : 𝕜 := ∑ i : I, ∑ j : J, (p 0).val i * (p 1).val j * A.g i j
  have hLHS : StrategicGame.expectedPayoff A.toStrategicGame p 0 = double := by
    unfold StrategicGame.expectedPayoff
    rw [show
          (∑ σ : (∀ i : Fin 2, A.toStrategicGame.strategy i),
              (∏ i : Fin 2, (p i).val (σ i)) * A.toStrategicGame.payoff σ 0)
          = ∑ ij : I × J, (p 0).val ij.1 * (p 1).val ij.2 * A.g ij.1 ij.2
        from ?_]
    · exact Fintype.sum_prod_type _
    · apply Fintype.sum_equiv (piFinTwoEquiv A.toStrategicGame.strategy)
      intro σ; rw [Fin.prod_univ_two]; rfl
  have hRHS : A.E (p 0) (p 1) = double := by
    -- A.E (p 0) (p 1) unfolds to ∑ i, (p 0).val i * (∑ j, (p 1).val j * A.g i j).
    change (∑ i, (p 0).val i * (∑ j, (p 1).val j * A.g i j)) = double
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hLHS, hRHS]

/-- Mirror: `expectedPayoff A.toStrategicGame p 1 = -(A.E (p 0) (p 1))`. -/
theorem expectedPayoff_toStrategicGame_one {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (p : StrategicGame.MixedProfile A.toStrategicGame) :
    StrategicGame.expectedPayoff A.toStrategicGame p 1
      = -(A.E (p 0) (p 1)) := by
  let double : 𝕜 := ∑ i : I, ∑ j : J, (p 0).val i * (p 1).val j * A.g i j
  have hLHS : StrategicGame.expectedPayoff A.toStrategicGame p 1 = -double := by
    unfold StrategicGame.expectedPayoff
    rw [show
          (∑ σ : (∀ i : Fin 2, A.toStrategicGame.strategy i),
              (∏ i : Fin 2, (p i).val (σ i)) * A.toStrategicGame.payoff σ 1)
          = ∑ ij : I × J, -((p 0).val ij.1 * (p 1).val ij.2 * A.g ij.1 ij.2)
        from ?_]
    · rw [Finset.sum_neg_distrib, Fintype.sum_prod_type]
    · apply Fintype.sum_equiv (piFinTwoEquiv A.toStrategicGame.strategy)
      intro σ
      rw [Fin.prod_univ_two]
      -- Unfold `payoff σ 1 = -(A.g (σ 0) (σ 1))` and use ring.
      show ((p 0).val (σ 0) * (p 1).val (σ 1)) * (-(A.g (σ 0) (σ 1)))
         = -((p 0).val (σ 0) * (p 1).val (σ 1) * A.g (σ 0) (σ 1))
      ring
  have hRHS : A.E (p 0) (p 1) = double := by
    change (∑ i, (p 0).val i * (∑ j, (p 1).val j * A.g i j)) = double
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hLHS, hRHS]

/-! ### Main theorem: mixed Nash equilibrium of the embedded strategic game -/

/-- **The strategic-game embedding of a finite matrix game admits a mixed Nash
    equilibrium.** Combines `MatrixGame.exists_mixed_nash_equilibrium` with the
    profile-expansion bridge lemmas above. -/
theorem exists_strategic_game_nash_equilibrium :
    ∃ p : StrategicGame.MixedProfile A.toStrategicGame,
      StrategicGame.IsMixedNashEq A.toStrategicGame p := by
  classical
  obtain ⟨xx, yy, hxx, hyy⟩ := A.exists_mixed_nash_equilibrium
  refine ⟨A.toMixedProfile xx yy, ?_⟩
  intro who s'
  -- Manually split on who ∈ {0, 1} so the substitution makes `who` literally 0 or 1.
  have hcases : who = 0 ∨ who = 1 := by
    rcases who with ⟨_ | _ | n, hn⟩
    · left; rfl
    · right; rfl
    · omega
  rcases hcases with rfl | rfl
  · -- Player 0 (row): deviating to pure s' ∈ I cannot improve.
    rw [expectedPayoff_toStrategicGame_zero, expectedPayoff_toStrategicGame_zero]
    have hdev0 : (StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 0 s') 0
                = StrategicGame.pureToMixed s' := by
      simp [StrategicGame.deviateMixed, Function.update]
    have hdev1 : (StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 0 s') 1
                = yy := by
      simp [StrategicGame.deviateMixed, Function.update]
    rw [hdev0, hdev1, toMixedProfile_zero, toMixedProfile_one]
    exact hxx (StrategicGame.pureToMixed s')
  · -- Player 1 (column): deviating to pure s' ∈ J cannot improve player 1's payoff.
    rw [expectedPayoff_toStrategicGame_one, expectedPayoff_toStrategicGame_one]
    have hdev0 : (StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 1 s') 0
                = xx := by
      simp [StrategicGame.deviateMixed, Function.update]
    have hdev1 : (StrategicGame.deviateMixed A.toStrategicGame
                    (A.toMixedProfile xx yy) 1 s') 1
                = StrategicGame.pureToMixed s' := by
      simp [StrategicGame.deviateMixed, Function.update]
    rw [hdev0, hdev1, toMixedProfile_zero, toMixedProfile_one]
    have h := hyy (StrategicGame.pureToMixed s')
    linarith

end MatrixGame
