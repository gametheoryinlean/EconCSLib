/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.DisprovingStrongMSP.Problem

/-!
# DisprovingStrongMSP: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Cardinal and ordinal matroid-secretary models

Mathlib supplies matroids and EconCSLib supplies lotteries. Weights are arbitrary
nonnegative reals; no computational restriction is imposed on online strategies.

An outcome law describes the final accepted set. `online` equates the joint law of all
prefix decisions for identical observations. Intersecting the final set with each
revealed prefix makes acceptance irrevocable; hereditary independence gives prefix
feasibility.

Ordinal observations resolve equal weights by fixed public label priority, without
revealing a separate equality bit. See [Feldman–Svensson–Zenklusen 2014, §1, footnote
2] for arbitrary tie-breaking. The lower-bound problem gives the strategy the entire
matroid in advance, as specified in the source problem statement.
-/

open scoped BigOperators NNReal

namespace EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

noncomputable section

/-- Higher weight precedes; a smaller label wins an equal-weight tie. -/
def weightPrecedes {n : ℕ} (w : WeightVector n) (a b : Fin n) : Prop :=
  w b < w a ∨ (w a = w b ∧ a < b)

/-- The same arriving labels and tie-broken rankings of revealed elements only. -/
def SameOrdinalHistoryThrough {n : ℕ} (w w' : WeightVector n)
    (order order' : ArrivalOrder n) (t : Fin n) : Prop :=
  (∀ s : Fin n, s ≤ t → order s = order' s) ∧
    ∀ s u : Fin n, s ≤ t → u ≤ t →
      (weightPrecedes w (order s) (order u) ↔
        weightPrecedes w' (order' s) (order' u))

/-- The joint decision law depends only on ordinal prefix observations and randomness. -/
def IsOrdinal {n : ℕ} {M : Matroid (Fin n)}
    (algorithm : MatroidSecretaryAlgorithm M) : Prop :=
  ∀ w w' order order' t,
    SameOrdinalHistoryThrough w w' order order' t → ∀ A,
      acceptedPrefixProbability (algorithm.outcome w order) (revealedSet order t) A =
        acceptedPrefixProbability (algorithm.outcome w' order')
          (revealedSet order' t) A

end

end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

end


section

/-!
## Conditional decisions of a causal secretary strategy

Joint prefix laws determine the next accept/reject probability, including a fixed
reject convention at zero-probability histories. This section proves one-step
disintegration and that the conditional kernel uses only observed history.
-/

open scoped BigOperators
namespace EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP
noncomputable section

/-- The labels observed strictly before the current arrival. -/
def revealedBeforeSet {n : ℕ} (order : ArrivalOrder n) (t : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun s => s < t).image order

/-- The current label is indeed among the observations through this time. -/
theorem current_mem_revealedSet {n : ℕ} (order : ArrivalOrder n) (t : Fin n) :
    order t ∈ revealedSet order t := by
  exact Finset.mem_image.mpr ⟨t, by simp, rfl⟩

/-- Removing the current label leaves exactly the earlier observations. -/
theorem revealedSet_erase_current {n : ℕ} (order : ArrivalOrder n) (t : Fin n) :
    (revealedSet order t).erase (order t) = revealedBeforeSet order t := by
  ext e
  simp only [revealedSet, revealedBeforeSet, Finset.mem_erase, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, s, hs, hse⟩
    refine ⟨s, lt_of_le_of_ne hs ?_, hse⟩
    intro hst
    exact hne (hst ▸ hse.symm)
  · rintro ⟨s, hs, hse⟩
    refine ⟨?_, s, le_of_lt hs, hse⟩
    intro heq
    exact (ne_of_lt hs) (order.injective (hse.trans heq))

/-- Every joint prefix pattern has nonnegative probability. -/
theorem acceptedPrefixProbability_nonneg {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) :
    0 ≤ acceptedPrefixProbability L seen A := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (L.property.1 S) (by split_ifs <;> norm_num)

/-- Removing the currently revealed item partitions the previous pattern into its reject
and accept extensions. No positive-probability premise is needed. -/
theorem acceptedPrefixProbability_split {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) (e : Fin n)
    (he : e ∈ seen) (hA : e ∉ A) :
    acceptedPrefixProbability L (seen.erase e) A =
      acceptedPrefixProbability L seen A +
        acceptedPrefixProbability L seen (insert e A) := by
  unfold acceptedPrefixProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  have hnot : e ∉ S ∩ seen.erase e := by simp
  have hinj : insert e (S ∩ seen.erase e) = insert e A ↔ S ∩ seen.erase e = A := by
    constructor
    · intro h
      have hh := congrArg (fun B : Finset (Fin n) => B.erase e) h
      simpa [hnot, hA] using hh
    · exact congrArg (insert e)
  have hseen : insert e (seen.erase e) = seen := Finset.insert_erase he
  by_cases hs : e ∈ S
  · have hinter : S ∩ seen = insert e (S ∩ seen.erase e) := by
      conv_lhs => rw [← hseen]
      exact Finset.inter_insert_of_mem hs
    have hne : insert e (S ∩ seen.erase e) ≠ A := by
      intro h
      exact hA (h ▸ Finset.mem_insert_self e (S ∩ seen.erase e))
    simp only [hinter, hne, if_false, mul_zero, zero_add, hinj]
  · have hinter : S ∩ seen = S ∩ seen.erase e := by
      conv_lhs => rw [← hseen]
      exact Finset.inter_insert_of_notMem hs
    have hne : S ∩ seen.erase e ≠ insert e A :=
      Finset.ne_insert_of_notMem _ _ hnot
    simp only [hinter, hne, if_false, mul_zero, add_zero]

/-- Accept with the conditional mass of the accept extension; when both extensions have
zero mass, reject. The real-number convention `0 / 0 = 0` implements this explicitly
without any assumption on reachable histories. -/
def conditionalAcceptance {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (seen A : Finset (Fin n)) (e : Fin n) : ℝ :=
  acceptedPrefixProbability L seen (insert e A) /
    (acceptedPrefixProbability L seen A +
      acceptedPrefixProbability L seen (insert e A))

/-- The conditional acceptance kernel is a valid Bernoulli parameter. -/
theorem conditionalAcceptance_bounds {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) (e : Fin n) :
    0 ≤ conditionalAcceptance L seen A e ∧ conditionalAcceptance L seen A e ≤ 1 := by
  have hreject := acceptedPrefixProbability_nonneg L seen A
  have haccept := acceptedPrefixProbability_nonneg L seen (insert e A)
  constructor
  · exact div_nonneg haccept (add_nonneg hreject haccept)
  · unfold conditionalAcceptance
    by_cases hz : acceptedPrefixProbability L seen A +
        acceptedPrefixProbability L seen (insert e A) = 0
    · simp only [hz, div_zero, zero_le_one]
    · apply (div_le_iff₀ (lt_of_le_of_ne (add_nonneg hreject haccept) (Ne.symm hz))).2
      simpa only [one_mul] using le_add_of_nonneg_left hreject

/-- The conditional kernel reconstructs the accept extension, including zero-probability
histories. Thus the quotient does not introduce new mass. -/
theorem conditionalAcceptance_reconstructs_accept {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) (e : Fin n)
    (he : e ∈ seen) (hA : e ∉ A) :
    acceptedPrefixProbability L (seen.erase e) A * conditionalAcceptance L seen A e =
      acceptedPrefixProbability L seen (insert e A) := by
  rw [acceptedPrefixProbability_split L seen A e he hA]
  unfold conditionalAcceptance
  by_cases hz : acceptedPrefixProbability L seen A +
      acceptedPrefixProbability L seen (insert e A) = 0
  · have hreject := acceptedPrefixProbability_nonneg L seen A
    have haccept := acceptedPrefixProbability_nonneg L seen (insert e A)
    have ha : acceptedPrefixProbability L seen (insert e A) = 0 := by linarith
    simp [ha]
  · exact mul_div_cancel₀ _ hz

/-- The complementary conditional probability reconstructs rejection too. -/
theorem conditionalAcceptance_reconstructs_reject {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) (e : Fin n)
    (he : e ∈ seen) (hA : e ∉ A) :
    acceptedPrefixProbability L (seen.erase e) A *
        (1 - conditionalAcceptance L seen A e) =
      acceptedPrefixProbability L seen A := by
  rw [mul_sub, mul_one, conditionalAcceptance_reconstructs_accept L seen A e he hA,
    acceptedPrefixProbability_split L seen A e he hA]
  exact add_sub_cancel_right _ _

/-- Applied to an online strategy, the kernel propagates the mass of every earlier
accepted pattern to the corresponding new accepted pattern. -/
theorem MatroidSecretaryAlgorithm.conditionalAcceptance_step
    {n : ℕ} {M : Matroid (Fin n)} (algorithm : MatroidSecretaryAlgorithm M)
    (w : WeightVector n) (order : ArrivalOrder n) (t : Fin n)
    (A : Finset (Fin n)) (hA : A ⊆ revealedBeforeSet order t) :
    acceptedPrefixProbability (algorithm.outcome w order) (revealedBeforeSet order t) A *
        conditionalAcceptance (algorithm.outcome w order) (revealedSet order t) A
          (order t) =
      acceptedPrefixProbability (algorithm.outcome w order) (revealedSet order t)
        (insert (order t) A) := by
  have hnot : order t ∉ A := by
    intro he
    have := hA he
    rw [← revealedSet_erase_current order t] at this
    exact Finset.notMem_erase (order t) (revealedSet order t) this
  simpa only [revealedSet_erase_current] using
    conditionalAcceptance_reconstructs_accept (algorithm.outcome w order)
      (revealedSet order t) A (order t) (current_mem_revealedSet order t) hnot

/-- A positive-mass accepted prefix is independent because it is contained in some
positive-mass feasible final outcome. -/
theorem MatroidSecretaryAlgorithm.prefix_feasible
    {n : ℕ} {M : Matroid (Fin n)} (algorithm : MatroidSecretaryAlgorithm M)
    (w : WeightVector n) (order : ArrivalOrder n) (seen A : Finset (Fin n))
    (hpos : 0 < acceptedPrefixProbability (algorithm.outcome w order) seen A) :
    M.Indep (A : Set (Fin n)) := by
  have hnonneg : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 ≤ (algorithm.outcome w order).val S * if S ∩ seen = A then 1 else 0 := by
    intro S _
    exact mul_nonneg ((algorithm.outcome w order).property.1 S)
      (by split_ifs <;> norm_num)
  obtain ⟨S, _, hS⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).mp hpos
  by_cases hSA : S ∩ seen = A
  · have hmass : 0 < (algorithm.outcome w order).val S := by simpa [hSA] using hS
    apply (algorithm.feasible w order S hmass).subset
    rw [← hSA]
    exact Finset.coe_subset.mpr Finset.inter_subset_left
  · simp [hSA] at hS

/-- The derived kernel never assigns positive acceptance probability to an infeasible
extension, even when called on an arbitrary earlier pattern. -/
theorem MatroidSecretaryAlgorithm.conditionalAcceptance_feasible
    {n : ℕ} {M : Matroid (Fin n)} (algorithm : MatroidSecretaryAlgorithm M)
    (w : WeightVector n) (order : ArrivalOrder n) (t : Fin n) (A : Finset (Fin n))
    (hpos : 0 < conditionalAcceptance (algorithm.outcome w order)
      (revealedSet order t) A (order t)) : M.Indep (insert (order t) A : Set (Fin n)) := by
  rw [← Finset.coe_insert]
  apply algorithm.prefix_feasible w order (revealedSet order t) (insert (order t) A)
  by_contra hn
  have hz : acceptedPrefixProbability (algorithm.outcome w order)
      (revealedSet order t) (insert (order t) A) = 0 :=
    le_antisymm (le_of_not_gt hn) (acceptedPrefixProbability_nonneg _ _ _)
  simp [conditionalAcceptance, hz] at hpos

/-- Identical observed histories give the same conditional decision after every
accepted-prefix pattern, independently of unseen weights and arrivals. -/
theorem MatroidSecretaryAlgorithm.conditionalAcceptance_online
    {n : ℕ} {M : Matroid (Fin n)} (algorithm : MatroidSecretaryAlgorithm M)
    (w w' : WeightVector n) (order order' : ArrivalOrder n) (t : Fin n)
    (hh : SameHistoryThrough w w' order order' t) (A : Finset (Fin n)) :
    conditionalAcceptance (algorithm.outcome w order) (revealedSet order t) A (order t) =
      conditionalAcceptance (algorithm.outcome w' order') (revealedSet order' t) A
        (order' t) := by
  have he := (hh t le_rfl).1
  unfold conditionalAcceptance
  rw [algorithm.online w w' order order' t hh A,
    algorithm.online w w' order order' t hh (insert (order t) A), he]

/-- For an ordinal strategy, only the observed labels and relative rankings are needed by
the conditional decision kernel. -/
theorem IsOrdinal.conditionalAcceptance_online
    {n : ℕ} {M : Matroid (Fin n)} {algorithm : MatroidSecretaryAlgorithm M}
    (hordinal : IsOrdinal algorithm)
    (w w' : WeightVector n) (order order' : ArrivalOrder n) (t : Fin n)
    (hh : SameOrdinalHistoryThrough w w' order order' t) (A : Finset (Fin n)) :
    conditionalAcceptance (algorithm.outcome w order) (revealedSet order t) A (order t) =
      conditionalAcceptance (algorithm.outcome w' order') (revealedSet order' t) A
        (order' t) := by
  have he := hh.1 t le_rfl
  unfold conditionalAcceptance
  rw [hordinal w w' order order' t hh A,
    hordinal w w' order order' t hh (insert (order t) A), he]

end
end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

end


section

/-!
## Finite-horizon realization of the joint decision law

Multiplying the derived Bernoulli transition probabilities reproduces each
accepted-prefix probability and every final-outcome mass, including impossible
histories. Together with `conditionalAcceptance_online`, this realizes a causal
sequential law. It adds no runtime or machine-implementation claim.
-/

open scoped BigOperators
namespace EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP
noncomputable section

/-- Arrival positions strictly below a natural-number horizon. -/
def prefixTimes (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t => t.val < k

/-- Labels revealed in the first k arrivals, with an empty prefix at k = 0. -/
def prefixLabels {n : ℕ} (order : ArrivalOrder n) (k : ℕ) : Finset (Fin n) :=
  (prefixTimes n k).image order

@[simp] theorem prefixTimes_zero (n : ℕ) : prefixTimes n 0 = ∅ := by
  simp [prefixTimes]

@[simp] theorem prefixLabels_zero {n : ℕ} (order : ArrivalOrder n) :
    prefixLabels order 0 = ∅ := by
  simp [prefixLabels]

theorem prefixTimes_succ {n k : ℕ} (hk : k < n) :
    prefixTimes n (k + 1) = insert (⟨k, hk⟩ : Fin n) (prefixTimes n k) := by
  ext t
  simp only [prefixTimes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  omega

theorem prefixLabels_before {n : ℕ} (order : ArrivalOrder n) (t : Fin n) :
    prefixLabels order t.val = revealedBeforeSet order t := rfl

theorem prefixLabels_through {n : ℕ} (order : ArrivalOrder n) (t : Fin n) :
    prefixLabels order (t.val + 1) = revealedSet order t := by
  apply congrArg (fun times : Finset (Fin n) => times.image order)
  ext s
  simp only [prefixTimes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Nat.lt_succ_iff

theorem prefixLabels_succ {n k : ℕ} (order : ArrivalOrder n) (hk : k < n) :
    prefixLabels order (k + 1) = insert (order ⟨k, hk⟩) (prefixLabels order k) := by
  simp only [prefixLabels, prefixTimes_succ hk, Finset.image_insert]

@[simp] theorem prefixTimes_full (n : ℕ) : prefixTimes n n = Finset.univ := by
  ext t
  simp [prefixTimes]

@[simp] theorem prefixLabels_full {n : ℕ} (order : ArrivalOrder n) :
    prefixLabels order n = Finset.univ := by
  ext e
  simp only [prefixLabels, prefixTimes_full, Finset.mem_image, Finset.mem_univ,
    true_and, iff_true]
  exact order.surjective e

/-- Probability of following the prescribed accept/reject choice at this step. Only the
prescribed earlier accepted set enters the conditional kernel. -/
def sequentialStepProbability {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (order : ArrivalOrder n) (S : Finset (Fin n)) (t : Fin n) : ℝ :=
  let q := conditionalAcceptance L (revealedSet order t)
    (S ∩ revealedBeforeSet order t) (order t)
  if order t ∈ S then q else 1 - q

/-- Both accept and reject branches have valid probability, at every history. -/
theorem sequentialStepProbability_bounds {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (order : ArrivalOrder n)
    (S : Finset (Fin n)) (t : Fin n) :
    0 ≤ sequentialStepProbability L order S t ∧
      sequentialStepProbability L order S t ≤ 1 := by
  have h := conditionalAcceptance_bounds L (revealedSet order t)
    (S ∩ revealedBeforeSet order t) (order t)
  unfold sequentialStepProbability
  split_ifs
  · exact h
  · constructor <;> linarith

/-- Product of the successive Bernoulli probabilities along a prescribed path. -/
def sequentialPrefixProbability {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (order : ArrivalOrder n) (S : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∏ t ∈ prefixTimes n k, sequentialStepProbability L order S t

theorem sequentialPrefixProbability_succ {n k : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (order : ArrivalOrder n)
    (S : Finset (Fin n)) (hk : k < n) :
    sequentialPrefixProbability L order S (k + 1) =
      sequentialPrefixProbability L order S k *
        sequentialStepProbability L order S ⟨k, hk⟩ := by
  unfold sequentialPrefixProbability
  rw [prefixTimes_succ hk, Finset.prod_insert]
  · exact mul_comm _ _
  · simp [prefixTimes]

/-- Initially the unique empty accepted history has probability one. -/
theorem acceptedPrefixProbability_empty {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) : acceptedPrefixProbability L ∅ ∅ = 1 := by
  simpa [acceptedPrefixProbability] using L.property.2

/-- After all labels have arrived, a prefix mass is exactly its outcome mass. -/
theorem acceptedPrefixProbability_full {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (S : Finset (Fin n)) :
    acceptedPrefixProbability L Finset.univ S = L.val S := by
  simp [acceptedPrefixProbability, mul_ite]

/-- Each product prefix equals the original joint accepted-prefix mass. Zero-mass
histories are included; no conditional-positivity premise is used. -/
theorem sequentialPrefixProbability_eq {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (order : ArrivalOrder n)
    (S : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) :
    sequentialPrefixProbability L order S k =
      acceptedPrefixProbability L (prefixLabels order k) (S ∩ prefixLabels order k) := by
  induction k with
  | zero => simp [sequentialPrefixProbability, acceptedPrefixProbability_empty]
  | succ k ih =>
      have hlt : k < n := by omega
      let t : Fin n := ⟨k, hlt⟩
      have hbefore : prefixLabels order k = revealedBeforeSet order t := rfl
      have hthrough : prefixLabels order (k + 1) = revealedSet order t :=
        prefixLabels_through order t
      have hnot : order t ∉ S ∩ revealedBeforeSet order t := by
        intro h
        have hm := (Finset.mem_inter.mp h).2
        rw [← revealedSet_erase_current order t] at hm
        exact Finset.notMem_erase (order t) (revealedSet order t) hm
      have hseen : revealedSet order t =
          insert (order t) (revealedBeforeSet order t) := by
        rw [← hthrough, prefixLabels_succ order hlt, hbefore]
      rw [sequentialPrefixProbability_succ L order S hlt, ih (by omega),
        hbefore, hthrough]
      change acceptedPrefixProbability L (revealedBeforeSet order t)
          (S ∩ revealedBeforeSet order t) * sequentialStepProbability L order S t = _
      by_cases hmem : order t ∈ S
      · have h := conditionalAcceptance_reconstructs_accept L (revealedSet order t)
          (S ∩ revealedBeforeSet order t) (order t)
          (current_mem_revealedSet order t) hnot
        rw [revealedSet_erase_current] at h
        simpa only [sequentialStepProbability, if_pos hmem,
          hseen, Finset.inter_insert_of_mem hmem] using h
      · have h := conditionalAcceptance_reconstructs_reject L (revealedSet order t)
          (S ∩ revealedBeforeSet order t) (order t)
          (current_mem_revealedSet order t) hnot
        rw [revealedSet_erase_current] at h
        simpa only [sequentialStepProbability, if_neg hmem,
          hseen, Finset.inter_insert_of_notMem hmem] using h

/-- The complete sequential accept/reject process reproduces the original law. -/
theorem sequentialProbability_eq_outcome {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (order : ArrivalOrder n) (S : Finset (Fin n)) :
    (∏ t, sequentialStepProbability L order S t) = L.val S := by
  simpa [sequentialPrefixProbability, acceptedPrefixProbability_full] using
    sequentialPrefixProbability_eq L order S n le_rfl

/-- The path products form a normalized lottery; no separate normalization constant or
exclusion of zero-probability paths is introduced. -/
def sequentialLottery {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (order : ArrivalOrder n) : Lottery ℝ (Finset (Fin n)) :=
  ⟨fun S => ∏ t, sequentialStepProbability L order S t, by
    constructor
    · intro S
      change 0 ≤ ∏ t, sequentialStepProbability L order S t
      rw [sequentialProbability_eq_outcome]
      exact L.property.1 S
    · simp only [sequentialProbability_eq_outcome]
      exact L.property.2⟩

/-- Equality of the full joint laws. -/
theorem sequentialLottery_eq {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (order : ArrivalOrder n) : sequentialLottery L order = L := by
  apply Subtype.ext
  funext S
  exact sequentialProbability_eq_outcome L order S

/-- For an online secretary strategy, the causal Bernoulli decisions reproduce the entire
joint accepted-set law. -/
theorem MatroidSecretaryAlgorithm.sequential_realization
    {n : ℕ} {M : Matroid (Fin n)} (algorithm : MatroidSecretaryAlgorithm M)
    (w : WeightVector n) (order : ArrivalOrder n) (S : Finset (Fin n)) :
    (∏ t, sequentialStepProbability (algorithm.outcome w order) order S t) =
      (algorithm.outcome w order).val S :=
  sequentialProbability_eq_outcome _ order S

end
end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

end


section

/-!
## Two strong matroid-secretary disproof targets

Both targets use `∃ matroid, ∃ ε > 0, ∀ algorithm, ∃ weights`. Weights are chosen
after the strategy but before arrival order and internal randomness. Positive OPT
excludes the all-zero instance. An existential positive gap avoids assuming that an
infimum over weights is attained with the same gap at its boundary.

Cardinal and ordinal targets are independent questions. Neither restricts strategies
to polynomial time or a query budget.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

/-- The separate ordinal target, with rank at least two expressed by an independent pair.
An ordinal disproof alone does not disprove the cardinal conjecture. -/
def OrdinalStrongMSPDisproofStatement : Prop :=
  ∃ n : ℕ, ∃ M : Matroid (Fin n), M.E = Set.univ ∧
    (∃ a b : Fin n, a ≠ b ∧ M.Indep ({a, b} : Set (Fin n))) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ algorithm : MatroidSecretaryAlgorithm M,
          IsOrdinal algorithm → ∃ w : WeightVector n,
            0 < matroidOPT M w ∧
              expectedSecretaryWeight algorithm w ≤
                (1 / Real.exp 1 - ε) * matroidOPT M w

end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

end
