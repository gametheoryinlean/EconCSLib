/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance

namespace EconCSLib.OpenProblem.EconCSBench.EFXAdditiveExistence

open SocialChoice.FairDivision.Indivisible

/-- Open-problem statement: every finite additive nonnegative instance with at
least four agents admits a complete EFX allocation. -/
def EFXAdditiveExistenceStatement : Prop :=
  ∀ (N G : Type*) [Fintype N] [DecidableEq G],
    4 ≤ Fintype.card N →
      ∀ problem : AdditiveInstance N G,
        (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
          ∃ allocation : Allocation N G,
            problem.feasible allocation ∧ problem.IsEFX allocation

/-- English version: "Do complete EFX allocations always exist for
nonnegative additive valuations with at least four agents?" -/
theorem efxAdditiveExistence :
    answer(sorry) ↔ EFXAdditiveExistenceStatement := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.EFXAdditiveExistence
