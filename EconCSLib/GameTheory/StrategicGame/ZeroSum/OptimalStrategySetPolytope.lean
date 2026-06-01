/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGameNash

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.OptimalStrategySetPolytope

For a finite matrix game `A`, the sets of optimal mixed row and column
strategies are nonempty polytopes in the ambient mixed-strategy space.
We supply the four structural properties that together characterise an
H-polytope (Mathlib does not yet ship a packaged `IsPolytope`):

* **Nonempty**, via the minimax theorem.
* **Convex**, via Mathlib's `Convex.inter` and the half-space form.
* **Closed**, via continuity of the defining linear functionals.
* **Compact**, as a closed subset of the compact standard simplex.

The deliverable is stated on the image of `MatrixGame.optimalRowStrategies`
in `I → ℝ` (under the subtype value map), which is the natural ambient
vector space for polytope vocabulary.

## Main results

* `MatrixGame.image_optimalRowStrategies_eq` — H-representation:
  `Subtype.val '' A.optimalRowStrategies =
     stdSimplex ℝ I ∩ ⋂ j, {f | A.value ≤ ∑ i, f i * A.g i j}`.
* `MatrixGame.optimalRowStrategies_image_isPolytope` — bundles the
  convex / closed / compact / nonempty conclusion.
* Symmetric results for `optimalColumnStrategies`.

## References

* [LRS] Laraki, Renault, Sorin, *Mathematical Foundations of Game
  Theory*, Proposition 2.4.1(a).
-/

open Finset BigOperators Set

set_option linter.unusedSectionVars false

namespace MatrixGame

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
variable (A : MatrixGame I J ℝ)

/-! ### H-representation of the row-optimal set -/

/-- H-representation of the row-optimal strategy set in the ambient
    space `I → ℝ`: the standard simplex intersected with the finitely
    many half-spaces `A.value ≤ ∑ i, f i * A.g i j`, one per pure
    column `j`. -/
def optimalRowSet : Set (I → ℝ) :=
  stdSimplex ℝ I ∩ ⋂ j : J, {f : I → ℝ | A.value ≤ ∑ i, f i * A.g i j}

/-- H-representation of the column-optimal strategy set in the ambient
    space `J → ℝ`. -/
def optimalColumnSet : Set (J → ℝ) :=
  stdSimplex ℝ J ∩ ⋂ i : I, {g : J → ℝ | ∑ j, g j * A.g i j ≤ A.value}

/-- The image of the row-optimal subtype set equals the H-representation
    polytope `A.optimalRowSet`. -/
theorem image_optimalRowStrategies_eq :
    (Subtype.val '' A.optimalRowStrategies) = A.optimalRowSet := by
  classical
  ext f
  constructor
  · rintro ⟨xx, hxx, rfl⟩
    refine ⟨xx.property, ?_⟩
    rw [mem_iInter]
    intro j
    have hpair := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx (stdSimplex.pure j)
    have heq : A.E xx (stdSimplex.pure j) = ∑ i, xx.val i * A.g i j := by
      show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = ∑ i, xx.val i * A.g i j
      apply Finset.sum_congr rfl
      intro i _
      show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
      rw [wsum_pure_apply]
    show A.value ≤ ∑ i, xx.val i * A.g i j
    rw [← heq]; exact hpair
  · rintro ⟨hf, hineq⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    rw [mem_iInter] at hineq
    rw [A.mem_optimalRowStrategies_iff_E_ge ⟨f, hf⟩]
    intro y'
    have hEeq : A.E ⟨f, hf⟩ y' = wsum y' (fun j => ∑ i, f i * A.g i j) := by
      show wsum ⟨f, hf⟩ (fun i => wsum y' (A.g i)) = wsum y' (fun j => ∑ i, f i * A.g i j)
      have hcomm : wsum ⟨f, hf⟩ (fun i => wsum y' (A.g i))
                 = wsum y' (fun j => wsum ⟨f, hf⟩ (fun i => A.g i j)) :=
        wsum_wsum_comm ⟨f, hf⟩ y' A.g
      rw [hcomm]
      rfl
    rw [hEeq]
    have hbound : ∀ j, A.value ≤ ∑ i, f i * A.g i j := hineq
    exact (ge_iff_simplex_ge.mp hbound) y'

/-! ### Convex / closed / compact / nonempty -/

theorem optimalRowSet_convex : Convex ℝ A.optimalRowSet := by
  apply Convex.inter (convex_stdSimplex ℝ I)
  apply convex_iInter
  intro j
  -- Half-space {f | A.value ≤ ∑ i, f i * A.g i j} is convex.
  intro f hf g hg a b ha hb hab
  show A.value ≤ ∑ i, (a • f + b • g) i * A.g i j
  have hf' : A.value ≤ ∑ i, f i * A.g i j := hf
  have hg' : A.value ≤ ∑ i, g i * A.g i j := hg
  have hexpand : ∑ i, (a • f + b • g) i * A.g i j =
      a * (∑ i, f i * A.g i j) + b * (∑ i, g i * A.g i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  calc A.value
      = (a + b) * A.value := by rw [hab]; ring
    _ = a * A.value + b * A.value := by ring
    _ ≤ a * (∑ i, f i * A.g i j) + b * (∑ i, g i * A.g i j) := by gcongr

theorem optimalRowSet_isClosed : IsClosed A.optimalRowSet := by
  have hsimplex : IsClosed (stdSimplex ℝ I) := isClosed_stdSimplex ℝ I
  apply IsClosed.inter hsimplex
  apply isClosed_iInter
  intro j
  -- {f | A.value ≤ ∑ i, f i * A.g i j} is closed: preimage of [A.value, ∞)
  -- under the continuous functional f ↦ ∑ i, f i * A.g i j.
  refine IsClosed.preimage ?_ isClosed_Ici
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)

theorem optimalRowSet_isCompact : IsCompact A.optimalRowSet := by
  have hsimplex : IsCompact (stdSimplex ℝ I) := isCompact_stdSimplex ℝ I
  exact hsimplex.of_isClosed_subset A.optimalRowSet_isClosed inter_subset_left

theorem optimalRowSet_nonempty : A.optimalRowSet.Nonempty := by
  obtain ⟨xx, yy, v, Hxx, Hyy⟩ := A.minimax_optimal_strategies
  refine ⟨xx.val, xx.property, ?_⟩
  rw [mem_iInter]
  intro j
  -- We need: A.value ≤ ∑ i, xx.val i * A.g i j = A.Ej xx j.
  have hv : v = A.value := by
    have h_le : v ≤ A.maximin := by
      have hxx_guarantee : v ≤ A.guarantee_I xx := by
        show v ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
        rw [Finset.le_inf'_iff]; intro j _; exact Hxx j
      have hg_le : A.guarantee_I xx ≤ A.maximin :=
        le_ciSup (bddAbove_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
      linarith
    have h_ge_min : A.minimax ≤ v := by
      have hyy_guarantee : A.guarantee_II yy ≤ v := by
        show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ v
        rw [Finset.sup'_le_iff]; intro i _; exact Hyy i
      have hg_ge : A.minimax ≤ A.guarantee_II yy := by
        have hbb : BddBelow (Set.range (A.guarantee_II)) := by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩
        exact ciInf_le hbb yy
      linarith
    have hmm : A.maximin ≤ A.minimax := A.maximin_le_minimax
    have : v = A.maximin := by linarith
    rw [this, ← A.value_eq_maximin]
  show A.value ≤ ∑ i, xx.val i * A.g i j
  have h1 : A.value ≤ A.Ej xx j := by rw [← hv]; exact Hxx j
  exact h1

/-- The row-optimal strategy set is a nonempty polytope: convex, closed,
    compact, and nonempty. -/
theorem optimalRowStrategies_image_isPolytope :
    Convex ℝ (Subtype.val '' A.optimalRowStrategies) ∧
    IsClosed (Subtype.val '' A.optimalRowStrategies) ∧
    IsCompact (Subtype.val '' A.optimalRowStrategies) ∧
    (Subtype.val '' A.optimalRowStrategies).Nonempty := by
  rw [A.image_optimalRowStrategies_eq]
  exact ⟨A.optimalRowSet_convex, A.optimalRowSet_isClosed,
         A.optimalRowSet_isCompact, A.optimalRowSet_nonempty⟩

/-! ### Column-side: dual statement -/

theorem image_optimalColumnStrategies_eq :
    (Subtype.val '' A.optimalColumnStrategies) = A.optimalColumnSet := by
  classical
  ext g
  constructor
  · rintro ⟨yy, hyy, rfl⟩
    refine ⟨yy.property, ?_⟩
    rw [mem_iInter]
    intro i
    have hpair := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy (stdSimplex.pure i)
    have heq : A.E (stdSimplex.pure i) yy = ∑ j, yy.val j * A.g i j := by
      show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = ∑ j, yy.val j * A.g i j
      rw [wsum_pure_apply]
      rfl
    show ∑ j, yy.val j * A.g i j ≤ A.value
    rw [← heq]; exact hpair
  · rintro ⟨hg, hineq⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [mem_iInter] at hineq
    rw [A.mem_optimalColumnStrategies_iff_E_le ⟨g, hg⟩]
    intro x'
    have hEeq : A.E x' ⟨g, hg⟩ = wsum x' (fun i => ∑ j, g j * A.g i j) := rfl
    rw [hEeq]
    have hbound : ∀ i, ∑ j, g j * A.g i j ≤ A.value := hineq
    exact (le_iff_simplex_le.mp hbound) x'

theorem optimalColumnSet_convex : Convex ℝ A.optimalColumnSet := by
  apply Convex.inter (convex_stdSimplex ℝ J)
  apply convex_iInter
  intro i
  intro f hf g hg a b ha hb hab
  show ∑ j, (a • f + b • g) j * A.g i j ≤ A.value
  have hf' : ∑ j, f j * A.g i j ≤ A.value := hf
  have hg' : ∑ j, g j * A.g i j ≤ A.value := hg
  have hexpand : ∑ j, (a • f + b • g) j * A.g i j =
      a * (∑ j, f j * A.g i j) + b * (∑ j, g j * A.g i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  calc a * (∑ j, f j * A.g i j) + b * (∑ j, g j * A.g i j)
      ≤ a * A.value + b * A.value := by gcongr
    _ = (a + b) * A.value := by ring
    _ = A.value := by rw [hab]; ring

theorem optimalColumnSet_isClosed : IsClosed A.optimalColumnSet := by
  have hsimplex : IsClosed (stdSimplex ℝ J) := isClosed_stdSimplex ℝ J
  apply IsClosed.inter hsimplex
  apply isClosed_iInter
  intro i
  exact IsClosed.preimage
    (continuous_finset_sum _ (fun j _ => (continuous_apply j).mul continuous_const))
    isClosed_Iic

theorem optimalColumnSet_isCompact : IsCompact A.optimalColumnSet := by
  have hsimplex : IsCompact (stdSimplex ℝ J) := isCompact_stdSimplex ℝ J
  exact hsimplex.of_isClosed_subset A.optimalColumnSet_isClosed inter_subset_left

theorem optimalColumnSet_nonempty : A.optimalColumnSet.Nonempty := by
  obtain ⟨xx, yy, v, Hxx, Hyy⟩ := A.minimax_optimal_strategies
  refine ⟨yy.val, yy.property, ?_⟩
  rw [mem_iInter]
  intro i
  have hv : v = A.value := by
    have h_le : v ≤ A.maximin := by
      have hxx_guarantee : v ≤ A.guarantee_I xx := by
        show v ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
        rw [Finset.le_inf'_iff]; intro j _; exact Hxx j
      have hg_le : A.guarantee_I xx ≤ A.maximin :=
        le_ciSup (bddAbove_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
      linarith
    have h_ge_min : A.minimax ≤ v := by
      have hyy_guarantee : A.guarantee_II yy ≤ v := by
        show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ v
        rw [Finset.sup'_le_iff]; intro i _; exact Hyy i
      have hg_ge : A.minimax ≤ A.guarantee_II yy := by
        have hbb : BddBelow (Set.range (A.guarantee_II)) := by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩
        exact ciInf_le hbb yy
      linarith
    have hmm : A.maximin ≤ A.minimax := A.maximin_le_minimax
    have : v = A.maximin := by linarith
    rw [this, ← A.value_eq_maximin]
  show ∑ j, yy.val j * A.g i j ≤ A.value
  have h1 : A.Ei i yy ≤ A.value := by rw [← hv]; exact Hyy i
  exact h1

theorem optimalColumnStrategies_image_isPolytope :
    Convex ℝ (Subtype.val '' A.optimalColumnStrategies) ∧
    IsClosed (Subtype.val '' A.optimalColumnStrategies) ∧
    IsCompact (Subtype.val '' A.optimalColumnStrategies) ∧
    (Subtype.val '' A.optimalColumnStrategies).Nonempty := by
  rw [A.image_optimalColumnStrategies_eq]
  exact ⟨A.optimalColumnSet_convex, A.optimalColumnSet_isClosed,
         A.optimalColumnSet_isCompact, A.optimalColumnSet_nonempty⟩

end MatrixGame
