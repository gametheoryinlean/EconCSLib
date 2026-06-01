/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Minimax.SkewSymmetric
import EconCSLib.Math.Simplex

/-!
# EconCSLib.Math.Minimax.Minimax

Finite two-player zero-sum minimax over any linearly ordered field
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, with NO compactness and
NO LP-optimum-attainment lemma. The route is von Neumann symmetrisation:
embed the game `A` (after a positivity shift) into the skew-symmetric matrix
`S` on `I ⊕ J ⊕ Unit`; `SkewSymmetric.optimal` (Theorem of the Alternative)
gives a value-0 optimal `z = (p, q, λ)`; reading off the blocks and normalising
by `∑ p` yields the optimal mixed strategies and the value.
-/

open Finset BigOperators

namespace Minimax

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `SkewSymmetric.optimal` transported to an arbitrary nonempty finite index. -/
theorem skew_optimal {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    (S : K → K → 𝕜) (hS : ∀ k l, S k l = - S l k) :
    ∃ z : K → 𝕜, (∀ k, 0 ≤ z k) ∧ (∑ k, z k = 1) ∧ (∀ l, 0 ≤ ∑ k, z k * S k l) := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  haveI : NeZero (Fintype.card K) := ⟨Fintype.card_ne_zero⟩
  set S' : Fin (Fintype.card K) → Fin (Fintype.card K) → 𝕜 :=
    fun a b => S (e.symm a) (e.symm b) with hS'
  obtain ⟨z', hz'_nn, hz'_sum, hz'_col⟩ :=
    SkewSymmetric.optimal S' (fun a b => hS _ _)
  refine ⟨fun k => z' (e k), fun k => hz'_nn _, ?_, ?_⟩
  · rw [Equiv.sum_comp e z']; exact hz'_sum
  · intro l
    have h := hz'_col (e l)
    have heq : (∑ k, z' (e k) * S k l) = ∑ a, z' a * S' a (e l) := by
      rw [← Equiv.sum_comp e (fun a => z' a * S' a (e l))]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hS', Equiv.symm_apply_apply]
    rw [heq]; exact h

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Nonempty I] [Nonempty J]

/-- The skew-symmetric symmetrisation of a game `A` on `I ⊕ J ⊕ Unit`. -/
def symMat (A : I → J → 𝕜) : (I ⊕ J ⊕ Unit) → (I ⊕ J ⊕ Unit) → 𝕜
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl i, Sum.inr (Sum.inl j) => A i j
  | Sum.inl _, Sum.inr (Sum.inr _) => -1
  | Sum.inr (Sum.inl j), Sum.inl i => -A i j
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 1
  | Sum.inr (Sum.inr _), Sum.inl _ => 1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => 0

theorem symMat_skew (A : I → J → 𝕜) : ∀ k l, symMat A k l = - symMat A l k := by
  rintro (i | (j | _)) (i' | (j' | _)) <;> simp [symMat]

/-- Split a sum over `I ⊕ J ⊕ Unit` into the three blocks. -/
private theorem sum_blocks (f : (I ⊕ J ⊕ Unit) → 𝕜) :
    ∑ k, f k = (∑ i, f (Sum.inl i)) + (∑ j, f (Sum.inr (Sum.inl j)))
      + f (Sum.inr (Sum.inr ())) := by
  have hu : (∑ u : Unit, f (Sum.inr (Sum.inr u))) = f (Sum.inr (Sum.inr ())) := by simp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hu, ← add_assoc]

/-- **Minimax for a strictly positive game.** -/
theorem minimax_pos (A : I → J → 𝕜) (hA : ∀ i j, 0 < A i j) :
    ∃ (x : I → 𝕜) (y : J → 𝕜) (v : 𝕜),
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ (∀ j, 0 ≤ y j) ∧ (∑ j, y j = 1) ∧
      (∀ j, v ≤ ∑ i, x i * A i j) ∧ (∀ i, ∑ j, A i j * y j ≤ v) := by
  classical
  obtain ⟨z, hz_nn, hz_sum, hz_col⟩ := skew_optimal (symMat A) (symMat_skew A)
  set p : I → 𝕜 := fun i => z (Sum.inl i) with hp
  set q : J → 𝕜 := fun j => z (Sum.inr (Sum.inl j)) with hq
  set lam : 𝕜 := z (Sum.inr (Sum.inr ())) with hlam
  have hpe : ∀ i, z (Sum.inl i) = p i := fun _ => rfl
  have hqe : ∀ j, z (Sum.inr (Sum.inl j)) = q j := fun _ => rfl
  have hle : z (Sum.inr (Sum.inr ())) = lam := rfl
  have hp_nn : ∀ i, 0 ≤ p i := fun i => hz_nn _
  have hq_nn : ∀ j, 0 ≤ q j := fun j => hz_nn _
  have hlam_nn : 0 ≤ lam := hz_nn _
  -- Column `inl i`: `(A q)_i ≤ λ`.
  have hcolI : ∀ i, (∑ j, A i j * q j) ≤ lam := by
    intro i
    have h := hz_col (Sum.inl i)
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_zero, Finset.sum_const_zero, zero_add,
      mul_one] at h
    have hb : (∑ j, q j * -(A i j)) = -(∑ j, A i j * q j) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hb] at h; linarith
  -- Column `inr (inl j)`: `λ ≤ (p A)_j`.
  have hcolJ : ∀ j, lam ≤ ∑ i, p i * A i j := by
    intro j
    have h := hz_col (Sum.inr (Sum.inl j))
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_zero, Finset.sum_const_zero, add_zero,
      mul_neg_one] at h
    linarith
  -- Column `inr (inr ())`: `∑ p ≤ ∑ q`.
  have hcolU : (∑ i, p i) ≤ ∑ j, q j := by
    have h := hz_col (Sum.inr (Sum.inr ()))
    rw [sum_blocks] at h
    simp only [symMat, hpe, hqe, hle, mul_one, mul_neg_one, mul_zero, add_zero] at h
    rw [Finset.sum_neg_distrib] at h; linarith
  -- `∑ p > 0`.
  have hsump_pos : 0 < ∑ i, p i := by
    rcases (Finset.sum_nonneg (fun i _ => hp_nn i)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hp0 : ∀ i, p i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp_nn i)).mp heq.symm i (Finset.mem_univ i)
      obtain ⟨j₀⟩ := ‹Nonempty J›
      have hlam0 : lam ≤ 0 := by
        have hz := hcolJ j₀
        rw [show (∑ i, p i * A i j₀) = 0 from
          Finset.sum_eq_zero (fun i _ => by rw [hp0 i, zero_mul])] at hz
        exact hz
      have hlam_eq0 : lam = 0 := le_antisymm hlam0 hlam_nn
      have hsumq1 : (∑ j, q j) = 1 := by
        have hs := hz_sum
        rw [sum_blocks z] at hs
        simp only [hpe, hqe, hle] at hs
        rw [show (∑ i, p i) = 0 from heq.symm, hlam_eq0] at hs; linarith
      obtain ⟨i₀⟩ := ‹Nonempty I›
      have hAq_pos : 0 < ∑ j, A i₀ j * q j := by
        obtain ⟨j₁, -, hj₁⟩ : ∃ j ∈ (Finset.univ : Finset J), 0 < q j := by
          by_contra hc; push_neg at hc
          exact one_ne_zero (hsumq1.symm.trans
            (Finset.sum_eq_zero (fun j hj => le_antisymm (hc j hj) (hq_nn j))))
        exact Finset.sum_pos' (fun j _ => mul_nonneg (hA i₀ j).le (hq_nn j))
          ⟨j₁, Finset.mem_univ j₁, mul_pos (hA i₀ j₁) hj₁⟩
      have := hcolI i₀; linarith
  -- `∑ q > 0`.
  have hsumq_pos : 0 < ∑ j, q j := lt_of_lt_of_le hsump_pos hcolU
  -- Normalise: `x = p / ∑p`, `y = q / ∑q`, value `λ / ∑p`.
  refine ⟨fun i => p i / (∑ i, p i), fun j => q j / (∑ j, q j), lam / (∑ i, p i),
    fun i => div_nonneg (hp_nn i) hsump_pos.le, ?_,
    fun j => div_nonneg (hq_nn j) hsumq_pos.le, ?_, ?_, ?_⟩
  · simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hsump_pos.ne'
  · simp only [div_eq_mul_inv]; rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ hsumq_pos.ne'
  · intro j
    have hkey : (∑ i, p i / (∑ i, p i) * A i j) = (∑ i, p i * A i j) / (∑ i, p i) := by
      simp only [div_eq_mul_inv]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hkey]
    exact (div_le_div_iff₀ hsump_pos hsump_pos).mpr
      (mul_le_mul_of_nonneg_right (hcolJ j) hsump_pos.le)
  · intro i
    have hkey : (∑ j, A i j * (q j / (∑ j, q j))) = (∑ j, A i j * q j) / (∑ j, q j) := by
      simp only [div_eq_mul_inv]; rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hkey]
    refine (div_le_div_iff₀ hsumq_pos hsump_pos).mpr ?_
    calc (∑ j, A i j * q j) * (∑ i, p i)
        ≤ lam * (∑ i, p i) := mul_le_mul_of_nonneg_right (hcolI i) hsump_pos.le
      _ ≤ lam * (∑ j, q j) := mul_le_mul_of_nonneg_left hcolU hlam_nn

/-- **Ordered-field von Neumann minimax.** Every finite two-player zero-sum
game over a linearly ordered field has a value and optimal mixed strategies. -/
theorem minimax (A : I → J → 𝕜) :
    ∃ (x : I → 𝕜) (y : J → 𝕜) (v : 𝕜),
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ (∀ j, 0 ≤ y j) ∧ (∑ j, y j = 1) ∧
      (∀ j, v ≤ ∑ i, x i * A i j) ∧ (∀ i, ∑ j, A i j * y j ≤ v) := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty I›; obtain ⟨j0⟩ := ‹Nonempty J›
  set c : 𝕜 := 1 - Finset.inf' Finset.univ ⟨(i0, j0), Finset.mem_univ _⟩
    (fun r : I × J => A r.1 r.2) with hc
  have hApos : ∀ i j, 0 < A i j + c := by
    intro i j
    have hle : Finset.inf' Finset.univ ⟨(i0, j0), Finset.mem_univ _⟩
        (fun r : I × J => A r.1 r.2) ≤ A i j :=
      Finset.inf'_le _ (Finset.mem_univ (i, j))
    rw [hc]; linarith
  obtain ⟨x, y, v, hxnn, hxsum, hynn, hysum, hxA, hAy⟩ :=
    minimax_pos (fun i j => A i j + c) hApos
  refine ⟨x, y, v - c, hxnn, hxsum, hynn, hysum, ?_, ?_⟩
  · intro j
    have h := hxA j
    rw [show (∑ i, x i * (A i j + c)) = (∑ i, x i * A i j) + c from by
        rw [show (∑ i, x i * (A i j + c)) = ∑ i, (x i * A i j + x i * c) from
          Finset.sum_congr rfl (fun i _ => by ring), Finset.sum_add_distrib,
          ← Finset.sum_mul, hxsum, one_mul]] at h
    linarith
  · intro i
    have h := hAy i
    rw [show (∑ j, (A i j + c) * y j) = (∑ j, A i j * y j) + c from by
        rw [show (∑ j, (A i j + c) * y j) = ∑ j, (A i j * y j + c * y j) from
          Finset.sum_congr rfl (fun j _ => by ring), Finset.sum_add_distrib,
          ← Finset.mul_sum, hysum, mul_one]] at h
    linarith

end Minimax
