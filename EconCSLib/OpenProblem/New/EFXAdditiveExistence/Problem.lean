/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance

/-!
# EFX existence for additive valuations

Does every nonnegative additive instance with at least four agents admit a
complete EFX allocation?

The native `AdditiveInstance` represents additive values by real item weights.
Its `allGoods : Finset G` is the finite ground set; the ambient label type `G`
may be infinite. Nonnegativity is required on `allGoods`. Native `feasible`
means that the bundles partition this set, and `IsEFX` checks removal of every
good, including zero-valued goods. The library compares distinct agents;
self-comparisons follow from nonnegativity. Empty bundles are allowed.

This is an existence statement, with no computational or Pareto requirement.
The three-agent additive case is established in [Chaudhury–Garg–Mehlhorn 2024].

## References

* B. Plaut and T. Roughgarden, "Almost Envy-Freeness with General Valuations",
  SIAM Journal on Discrete Mathematics 34(2) (2020), Definition 2.3.
* B. R. Chaudhury, J. Garg, and K. Mehlhorn, "EFX Exists for Three Agents",
  Journal of the ACM 71(1) (2024), Article 4.
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

/-- The unresolved answer to complete EFX existence for nonnegative additive valuations. -/
theorem efxAdditiveExistence :
    answer(sorry) ↔ EFXAdditiveExistenceStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.EFXAdditiveExistence
