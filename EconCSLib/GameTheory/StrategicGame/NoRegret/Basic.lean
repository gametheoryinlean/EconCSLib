/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Simplex
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Basic definitions for finite no-regret learning

This module contains the shared asymptotic predicates, external-regret
quantities, finite histories, and abstract online-strategy interfaces used by
the Section 7.3 development.

## References

* [MFoGT] Chapter 7, Section 7.3.1
-/

open Finset BigOperators Filter Topology

namespace StrategicGame

universe uK uL uN uS uΩ uOut

/-! ### Asymptotic predicates -/

/-- A real sequence is asymptotically nonpositive: for every positive tolerance,
eventually `a n ≤ ε`. This is the one-sided form used for regret criteria. -/
def VanishesAboveZero (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, a n ≤ ε

/-- Positive part of a real number. -/
noncomputable def posPart (x : ℝ) : ℝ :=
  max x 0

@[simp] lemma posPart_nonneg (x : ℝ) : 0 ≤ posPart x := le_max_right x 0

/-- The positive part vanishes exactly when the number is already nonpositive. -/
lemma posPart_eq_zero_iff {x : ℝ} : posPart x = 0 ↔ x ≤ 0 := by
  unfold posPart
  constructor
  · intro h
    by_contra hx
    push Not at hx
    have hlt : (0 : ℝ) < max x 0 := lt_of_lt_of_le hx (le_max_left x 0)
    linarith [h ▸ hlt]
  · intro hx
    exact le_antisymm (max_le hx le_rfl) (le_max_right x 0)

/-- `VanishesAboveZero` applied to a pointwise-nonnegative sequence upgrades to genuine
convergence to zero: the nonnegativity of `posPart` turns the one-sided asymptotic bound into
two-sided convergence, which is what the compactness arguments below need. -/
lemma tendsto_zero_of_vanishesAboveZero_posPart {f : ℕ → ℝ}
    (h : VanishesAboveZero fun n => posPart (f n)) :
    Tendsto (fun n => posPart (f n)) atTop (nhds 0) :=
  Metric.tendsto_atTop.mpr fun ε hε => by
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (posPart_nonneg _)]
      exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)⟩

/-! ### External regret: MFoGT 7.3.1 -/

/-- The external regret vector `R(ℓ, U)`, comparing the realized component `ℓ`
with a fixed alternative component `k`. -/
def externalRegretStage {K : Type uK} (choice : K) (payoff : K → ℝ) (k : K) : ℝ :=
  payoff k - payoff choice

/-- Average external regret up to stage `n + 1` against a fixed component `k`. -/
noncomputable def averageExternalRegret {K : Type uK}
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) (k : K) : ℝ :=
  ((n + 1 : ℝ)⁻¹) *
    ∑ t : Fin (n + 1), externalRegretStage (play t.val) (payoff t.val) k

/-- Realized-path external-regret criterion. MFoGT Definition 7.3.1 is the
almost-sure strategy property obtained by requiring this criterion for the
random path generated against every admissible payoff process. -/
def HasNoExternalRegret {K : Type uK}
    (play : ℕ → K) (payoff : ℕ → K → ℝ) : Prop :=
  ∀ k : K, VanishesAboveZero fun n => posPart (averageExternalRegret play payoff n k)

/-- The maximum positive average external regret at stage `n + 1`, matching
the scalar criterion in MFoGT Definition 7.3.1. -/
noncomputable def maximalPositiveAverageExternalRegret
    {K : Type uK} [Fintype K] [Nonempty K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k =>
    posPart (averageExternalRegret play payoff n k)

/-- For a finite action set, the coordinatewise definition of no external
regret is equivalent to the maximum criterion in MFoGT Definition 7.3.1. -/
theorem hasNoExternalRegret_iff_maximalPositiveAverageExternalRegret
    {K : Type uK} [Fintype K] [Nonempty K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) :
    HasNoExternalRegret play payoff ↔
      VanishesAboveZero (maximalPositiveAverageExternalRegret play payoff) := by
  classical
  constructor
  · intro h ε hε
    choose N hN using fun k : K => h k ε hε
    refine ⟨∑ k : K, N k, fun n hn => ?_⟩
    unfold maximalPositiveAverageExternalRegret
    apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro k _
    apply hN k n
    exact le_trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ k)) hn
  · intro h k ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    exact (Finset.le_sup' (fun j : K =>
      posPart (averageExternalRegret play payoff n j)) (Finset.mem_univ k)).trans
        (hN n hn)

/-- The maximum positive average external regret is nonnegative. -/
lemma maximalPositiveAverageExternalRegret_nonneg
    {K : Type uK} [Fintype K] [Nonempty K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) :
    0 ≤ maximalPositiveAverageExternalRegret play payoff n := by
  classical
  let k : K := Classical.choice (inferInstance : Nonempty K)
  exact (posPart_nonneg (averageExternalRegret play payoff n k)).trans
    (Finset.le_sup' (fun j : K =>
      posPart (averageExternalRegret play payoff n j)) (Finset.mem_univ k))

/-- Exact limit form of MFoGT Definition 7.3.1: on a finite nonempty action
set, no external regret is equivalent to the maximum positive average regret
converging to zero. -/
theorem hasNoExternalRegret_iff_tendsto_maximalPositiveAverageExternalRegret_zero
    {K : Type uK} [Fintype K] [Nonempty K]
    (play : ℕ → K) (payoff : ℕ → K → ℝ) :
    HasNoExternalRegret play payoff ↔
      Tendsto (maximalPositiveAverageExternalRegret play payoff) atTop (nhds 0) := by
  rw [hasNoExternalRegret_iff_maximalPositiveAverageExternalRegret]
  constructor
  · intro h
    exact Metric.tendsto_atTop.mpr fun ε hε => by
      obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
      exact ⟨N, fun n hn => by
        rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (maximalPositiveAverageExternalRegret_nonneg play payoff n)]
        exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h ε hε
    exact ⟨N, fun n hn => by
      have hdist := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (maximalPositiveAverageExternalRegret_nonneg play payoff n)] at hdist
      exact hdist.le⟩

/-- A bounded payoff process taking values in `[-1, 1]^K`, as in [MFoGT 7.3]. -/
def IsBoundedPayoffProcess {K : Type uK} (payoff : ℕ → K → ℝ) : Prop :=
  ∀ n k, -1 ≤ payoff n k ∧ payoff n k ≤ 1

/-- Histories for finite online prediction with action set `K`. -/
abbrev ExternalHistory (K : Type uK) (n : ℕ) :=
  (Fin n → K) × (Fin n → K → ℝ)

/-- An online strategy chooses a distribution over components after every finite
history. -/
abbrev ExternalOnlineStrategy (K : Type uK) [Fintype K] :=
  (n : ℕ) → ExternalHistory K n → stdSimplex ℝ K

/-- The finite history generated by a realized play/payoff path before stage
`n`. -/
def externalHistoryOf {K : Type uK}
    (play : ℕ → K) (payoff : ℕ → K → ℝ) (n : ℕ) : ExternalHistory K n :=
  (fun t => play t.val, fun t => payoff t.val)

/-- Pathwise support relation: after every realized history, the realized
action has positive probability under the strategy. This is weaker than the
conditional-law generation predicate used for almost-sure results. -/
def IsSupportedByExternalStrategy {K : Type uK} [Fintype K]
    (σ : ExternalOnlineStrategy K) (play : ℕ → K) (payoff : ℕ → K → ℝ) : Prop :=
  ∀ n : ℕ, 0 < (σ n (externalHistoryOf play payoff n)).val (play n)

/-- A pathwise strategy has no external regret against every bounded realized
path whose chosen actions remain in the support of the prescribed mixed action.
This is a robust pathwise notion, not a stochastic generation statement. -/
def IsRobustPathwiseNoExternalRegretStrategy {K : Type uK} [Fintype K]
    (σ : ExternalOnlineStrategy K) : Prop :=
  ∀ play payoff,
    IsSupportedByExternalStrategy σ play payoff →
    IsBoundedPayoffProcess payoff →
    HasNoExternalRegret play payoff

end StrategicGame
