/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.MMS

namespace EconCSLib.OpenProblem.EconCSBench.PMMSExistence

open SocialChoice.FairDivision.Indivisible

/-- The two-way maximin share of agent `i` for a set of goods `S`. -/
noncomputable def pairMMSValue
    {N G : Type*} [DecidableEq G]
    (v : Valuation N G) (i : N) (S : Finset G) : ℝ :=
  mmsValue
    ({ val := fun _ bundle => v.val i bundle } : Valuation (Fin 2) G)
    S 0

/-- Pairwise maximin-share fairness. -/
def IsPMMS
    {N G : Type*} [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N,
    pairMMSValue v i (A i ∪ A j) ≤ v.val i (A i)

/-- Epistemic PMMS: each agent can keep their actual bundle and imagine a
complete reallocation under which that agent satisfies every pairwise MMS
comparison. -/
def IsEpistemicPMMS
    {N G : Type*} [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (X : Allocation N G) : Prop :=
  ∀ i : N, ∃ Y : Allocation N G,
    IsAllocation allGoods Y ∧ Y i = X i ∧
      ∀ j : N,
        pairMMSValue v i (Y i ∪ Y j) ≤ v.val i (X i)

/-- Exact PMMS existence for all nonnegative additive instances. -/
def PMMSExistenceStatement : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G]
      (problem : AdditiveInstance N G),
    (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
      ∃ A : Allocation N G,
        problem.feasible A ∧ IsPMMS problem.toValuation A

/-- Exact epistemic-PMMS existence for all nonnegative additive instances. -/
def EpistemicPMMSExistenceStatement : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G]
      (problem : AdditiveInstance N G),
    (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
      ∃ A : Allocation N G,
        problem.feasible A ∧
          IsEpistemicPMMS problem.toValuation problem.allGoods A

/-- Open Problem 1: does every nonnegative additive instance admit a PMMS
allocation? -/
theorem pmmsExistence :
    answer(sorry) ↔ PMMSExistenceStatement := by
  sorry

/-- Open Problem 2: does every nonnegative additive instance admit an
epistemic-PMMS allocation? -/
theorem epistemicPMMSExistence :
    answer(sorry) ↔ EpistemicPMMSExistenceStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.PMMSExistence
