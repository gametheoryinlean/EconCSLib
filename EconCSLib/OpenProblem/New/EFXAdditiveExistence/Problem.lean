/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance

/-!
# 05. EFX existence for additive valuations
-/



section

/-!
## Exact EFX existence for additive valuations

This specification reuses EconCSLib's `AdditiveInstance`, complete feasibility, and
`IsEFX`; see [Plaut–Roughgarden 2020, §2, Definition 2.3]. The finite set `allGoods`
determines the instance even if the ambient label type is infinite. Weights need only
be nonnegative on that set. EFX checks every removed good, including zero-value goods;
self-comparisons follow from nonnegativity.

The question is unrestricted existence for at least four agents. Empty bundles are
allowed, and no efficiency, Pareto, encoding, or machine condition is added.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EFXAdditiveExistence

open SocialChoice.FairDivision.Indivisible

/-- Whether every nonnegative additive instance with at least four agents admits a
complete exact-EFX allocation; this definition does not assert the answer. -/
def EFXAdditiveExistenceStatement : Prop :=
  ∀ (N G : Type*) [Fintype N] [DecidableEq G],
    4 ≤ Fintype.card N →
      ∀ problem : AdditiveInstance N G,
        (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
          ∃ allocation : Allocation N G,
            problem.feasible allocation ∧ problem.IsEFX allocation

end EconCSLib.OpenProblem.New.EconCSBench.EFXAdditiveExistence

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.EFXAdditiveExistence

/-- Existence of a complete EFX allocation for every nonnegative additive instance. -/
theorem efxAdditiveExistence :
    answer(sorry) ↔ EFXAdditiveExistenceStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.EFXAdditiveExistence
