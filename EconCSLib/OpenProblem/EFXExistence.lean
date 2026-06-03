/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance

/-!
# EconCSLib.OpenProblem.EFXExistence

This file records the major open problem of whether complete EFX allocations
exist for indivisible goods with additive nonnegative valuations.

The nontrivial unresolved range is four or more agents. EconCSLib already proves
the two-agent additive case in
`SocialChoice.FairDivision.Indivisible.efx_exists_two_agents`; the three-agent
case is known in the literature but is not formalized here.

## References

* Plaut and Roughgarden, "Almost Envy-Freeness with General Valuations" (SODA
  2018).
* Chaudhury, Garg, and Mehlhorn, "EFX Allocations for Three Agents" (EC 2020).
-/

namespace SocialChoice
namespace FairDivision
namespace Indivisible

/-- Open-problem statement: every additive nonnegative indivisible-goods
instance with at least four agents has a complete EFX allocation. -/
def EFXExistenceStatement : Prop :=
  ∀ (N G : Type*) [Fintype N] [Fintype G] [DecidableEq G],
    4 ≤ Fintype.card N →
      ∀ I : AdditiveInstance N G,
        (∀ i g, 0 ≤ I.weight i g) →
          ∃ A : Allocation N G, I.feasible A ∧ I.IsEFX A

/-- English version: "For every finite additive nonnegative indivisible-goods
instance with at least four agents, does there exist a complete EFX allocation?"

The `answer(sorry)` marker records that the mathematical answer is unresolved;
it is not a proof of either side of the question. -/
theorem efxExistence : answer(sorry) ↔ EFXExistenceStatement := by
  sorry

end Indivisible
end FairDivision
end SocialChoice
