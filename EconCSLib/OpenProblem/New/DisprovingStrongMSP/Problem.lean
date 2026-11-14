/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

/-!
# 04. Disproving the strong matroid secretary conjecture
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

/-- Nonnegative real weights, without a machine encoding restriction. -/
abbrev WeightVector (n : ℕ) := Fin n → ℝ≥0

/-- A permutation mapping arrival positions to element labels. -/
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)

/-- Elements revealed up to and including time `t`. -/
def revealedSet {n : ℕ} (order : ArrivalOrder n) (t : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter fun s => s ≤ t).image order

/-- Total weight of a set, in the same units as OPT and expected reward. -/
def setWeight {n : ℕ} (w : WeightVector n) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ S, (w e : ℝ)

/-- Probability of the entire accepted-prefix pattern `A`. -/
noncomputable def acceptedPrefixProbability {n : ℕ}
    (L : Lottery ℝ (Finset (Fin n))) (seen A : Finset (Fin n)) : ℝ :=
  ∑ S, L.val S * if S ∩ seen = A then 1 else 0

/-- Cardinal observations coincide through time `t`. -/
def SameHistoryThrough {n : ℕ} (w w' : WeightVector n)
    (order order' : ArrivalOrder n) (t : Fin n) : Prop :=
  ∀ s : Fin n, s ≤ t →
    order s = order' s ∧ w (order s) = w' (order' s)

/-- A randomized online strategy for a known matroid, fixed before weights and order. -/
structure MatroidSecretaryAlgorithm {n : ℕ} (M : Matroid (Fin n)) where
  /-- Law of the accepted set after averaging internal randomness. -/
  outcome : WeightVector n → ArrivalOrder n → Lottery ℝ (Finset (Fin n))
  /-- Every positive-probability accepted set is independent. -/
  feasible : ∀ w order S,
    0 < (outcome w order).val S → M.Indep (S : Set (Fin n))
  /-- Future weights and arrivals cannot affect the joint prefix decision law. -/
  online : ∀ w w' order order' t,
    SameHistoryThrough w w' order order' t → ∀ A,
      acceptedPrefixProbability (outcome w order) (revealedSet order t) A =
        acceptedPrefixProbability (outcome w' order') (revealedSet order' t) A

/-- Expectation over uniform arrival order and internal randomness, for fixed weights. -/
noncomputable def expectedSecretaryWeight {n : ℕ} {M : Matroid (Fin n)}
    (algorithm : MatroidSecretaryAlgorithm M) (w : WeightVector n) : ℝ :=
  (∑ order : ArrivalOrder n,
    Lottery.expectedValue (algorithm.outcome w order) (setWeight w)) /
      (Fintype.card (ArrivalOrder n) : ℝ)

/-- Maximum base weight. Finiteness makes this supremum an attained maximum; the algorithm
itself is only required to return an independent set. -/
noncomputable def matroidOPT {n : ℕ} (M : Matroid (Fin n))
    (w : WeightVector n) : ℝ :=
  ⨆ B : {S : Finset (Fin n) // M.IsBase (S : Set (Fin n))}, setWeight w B.1

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

/-- One finite matroid defeats every cardinal strategy by a common positive gap below
`1/e`. -/
def StrongMatroidSecretaryDisproofStatement : Prop :=
  ∃ n : ℕ, ∃ M : Matroid (Fin n), M.E = Set.univ ∧
    ∃ ε : ℝ, 0 < ε ∧
      ∀ algorithm : MatroidSecretaryAlgorithm M,
        ∃ w : WeightVector n,
          0 < matroidOPT M w ∧
            expectedSecretaryWeight algorithm w ≤
              (1 / Real.exp 1 - ε) * matroidOPT M w

end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP

/-- A uniform positive gap against every online matroid-secretary strategy. -/
theorem disprovingStrongMSP :
    answer(sorry) ↔ StrongMatroidSecretaryDisproofStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.DisprovingStrongMSP
