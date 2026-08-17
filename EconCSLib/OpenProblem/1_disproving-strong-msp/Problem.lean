/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.DisprovingStrongMSP

/-- Arrival orders of an `n`-element ground set. -/
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)

/-- Elements revealed through time `t`. -/
def revealedSet
    {n : ℕ} (order : ArrivalOrder n) (t : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Probability of seeing exactly `A` as the accepted portion of a prefix. -/
noncomputable def acceptedPrefixProbability
    {n : ℕ} (L : Lottery ℝ (Finset (Fin n)))
    (seen A : Finset (Fin n)) : ℝ :=
  ∑ S, L.val S * if S ∩ seen = A then 1 else 0

/-- Two weighted arrival histories agree through time `t`. -/
def SameHistoryThrough
    {n : ℕ} (w w' : Fin n → ℝ)
    (order order' : ArrivalOrder n) (t : Fin n) : Prop :=
  ∀ s : Fin n, s ≤ t →
    order s = order' s ∧ w (order s) = w' (order' s)

/-- A randomized online matroid-secretary algorithm.  Non-anticipation is
imposed on the complete distribution of accepted decisions in every revealed
prefix, not merely on one-element marginals. -/
structure MatroidSecretaryAlgorithm {n : ℕ} (M : Matroid (Fin n)) where
  /-- Distribution of the final accepted set. -/
  outcome :
    (Fin n → ℝ) → ArrivalOrder n → Lottery ℝ (Finset (Fin n))
  /-- Every set in the support is independent in the matroid. -/
  feasible :
    ∀ w order S, 0 < (outcome w order).val S → M.Indep (S : Set (Fin n))
  /-- Decisions do not use future arrivals or values. -/
  online :
    ∀ w w' order order' t,
      SameHistoryThrough w w' order order' t →
        ∀ A,
          acceptedPrefixProbability (outcome w order) (revealedSet order t) A =
            acceptedPrefixProbability (outcome w' order')
              (revealedSet order' t) A

/-- Expected weight selected under a uniformly random arrival order. -/
noncomputable def expectedSecretaryWeight
    {n : ℕ} {M : Matroid (Fin n)}
    (algorithm : MatroidSecretaryAlgorithm M) (w : Fin n → ℝ) : ℝ :=
  Lottery.expectedValue (uniformLottery (ArrivalOrder n)) fun order =>
    Lottery.expectedValue (algorithm.outcome w order) fun S =>
      ∑ e ∈ S, w e

/-- Offline maximum-weight base value. -/
noncomputable def matroidOPT
    {n : ℕ} (M : Matroid (Fin n)) (w : Fin n → ℝ) : ℝ :=
  ⨆ B : {S : Finset (Fin n) // M.IsBase (S : Set (Fin n))},
    ∑ e ∈ B.1, w e

/-- An ordinal algorithm is invariant under every change of numerical weights
that preserves their weak ordering. -/
def IsOrdinal
    {n : ℕ} {M : Matroid (Fin n)}
    (algorithm : MatroidSecretaryAlgorithm M) : Prop :=
  ∀ w w' : Fin n → ℝ,
    (∀ a b, (w a ≤ w b ↔ w' a ≤ w' b)) →
      ∀ order, algorithm.outcome w order = algorithm.outcome w' order

/-- The optional ordinal subgoal from the Markdown problem. -/
def OrdinalStrongMSPDisproofStatement : Prop :=
  ∃ n : ℕ, ∃ M : Matroid (Fin n), M.E = Set.univ ∧
    -- The ordinal subgoal in the source is restricted to matroids of rank
    -- at least two.  For a finite matroid this is witnessed by an independent
    -- pair of distinct ground-set elements.
    (∃ a b : Fin n, a ≠ b ∧
      M.Indep ({a, b} : Set (Fin n))) ∧
    ∃ ε : ℝ, 0 < ε ∧
    ∀ algorithm : MatroidSecretaryAlgorithm M,
      IsOrdinal algorithm →
        ∃ w : Fin n → ℝ, (∀ e, 0 ≤ w e) ∧
          0 < matroidOPT M w ∧
          expectedSecretaryWeight algorithm w ≤
            (1 / Real.exp 1 - ε) * matroidOPT M w

/-- Primary open-problem statement: some finite matroid defeats the `1/e`
guarantee for every (cardinal) online algorithm. -/
def StrongMatroidSecretaryDisproofStatement : Prop :=
  ∃ n : ℕ, ∃ M : Matroid (Fin n), M.E = Set.univ ∧
    ∃ ε : ℝ, 0 < ε ∧
    ∀ algorithm : MatroidSecretaryAlgorithm M,
      ∃ w : Fin n → ℝ, (∀ e, 0 ≤ w e) ∧
        0 < matroidOPT M w ∧
        expectedSecretaryWeight algorithm w ≤
          (1 / Real.exp 1 - ε) * matroidOPT M w

/-- English version: "Does there exist a matroid whose optimal matroid
secretary competitive ratio is strictly below `1/e`?" -/
theorem strongMatroidSecretaryDisproof :
    answer(sorry) ↔ StrongMatroidSecretaryDisproofStatement := by
  sorry

/-- The separate ordinal research goal from the Markdown problem. -/
theorem ordinalStrongMatroidSecretaryDisproof :
    answer(sorry) ↔ OrdinalStrongMSPDisproofStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.DisprovingStrongMSP
