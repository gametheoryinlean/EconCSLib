/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.MMS

/-!
# 08. PMMS and epistemic PMMS
-/



section

/-!
## PMMS and epistemic-PMMS existence

The two questions concern nonnegative additive real valuations on finitely many goods.
Both actual allocations and epistemic certificates are complete partitions.

Source: [Feldman–Fiat–Nissan–Ponitka 2026, Definitions 2.1, 2.4, 2.7],
arXiv:2606.18921. Native EconCSLib allocation and MMS definitions are reused. Fairness
predicates do not include feasibility; the final statements impose it. There is at
least one agent, while the good set and individual bundles may be empty.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.PMMSExistence

open SocialChoice.FairDivision.Indivisible

/-- The two-part maximin value `μ_i(2,S)`, evaluating both parts with agent `i`'s
valuation. The auxiliary label `0` is not an original agent. -/
noncomputable def pairMMSValue
    {N G : Type*} [DecidableEq G]
    (v : Valuation N G) (i : N) (S : Finset G) : ℝ :=
  mmsValue
    ({ val := fun _ bundle => v.val i bundle } : Valuation (Fin 2) G)
    S 0

/-- Exact PMMS for the actual bundles. Self-comparisons are harmless on the nonnegative
additive domain; feasibility is imposed separately. -/
def IsPMMS
    {N G : Type*} [DecidableEq G]
    (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N,
    pairMMSValue v i (A i ∪ A j) ≤ v.val i (A i)

/-- EPMMS has quantifier order `∀ i, ∃ Y, ∀ j`: a complete witness partition preserves `X
i` as a set and makes only agent `i` PMMS-satisfied. -/
def IsEpistemicPMMS
    {N G : Type*} [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (X : Allocation N G) : Prop :=
  ∀ i : N, ∃ Y : Allocation N G,
    IsAllocation allGoods Y ∧ Y i = X i ∧
      ∀ j : N,
        pairMMSValue v i (Y i ∪ Y j) ≤ v.val i (X i)

/-- Whether every nonnegative additive instance admits a complete PMMS allocation. -/
def PMMSExistenceStatement : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G]
      (problem : AdditiveInstance N G),
    (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
      ∃ A : Allocation N G,
        problem.feasible A ∧ IsPMMS problem.toValuation A

/-- Whether every nonnegative additive instance admits a complete epistemic-PMMS
allocation. -/
def EpistemicPMMSExistenceStatement : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G]
      (problem : AdditiveInstance N G),
    (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
      ∃ A : Allocation N G,
        problem.feasible A ∧
          IsEpistemicPMMS problem.toValuation problem.allGoods A

end EconCSLib.OpenProblem.New.EconCSBench.PMMSExistence

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.PMMSExistence

/-- Complete pairwise maximin-share allocation existence. -/
theorem pmmsExistence :
    answer(sorry) ↔ PMMSExistenceStatement := by
  sorry

/-- Independent epistemic-PMMS existence question. -/
theorem epistemicPMMSExistence :
    answer(sorry) ↔ EpistemicPMMSExistenceStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.PMMSExistence
