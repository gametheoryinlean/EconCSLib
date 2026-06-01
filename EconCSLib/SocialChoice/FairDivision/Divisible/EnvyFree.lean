/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Divisible.CutAndChoose

/-!
# EconCSLib.SocialChoice.FairDivision.Divisible.EnvyFree

Two-agent envy-free existence for divisible goods (cake cutting).

## Related definitions

The core fairness predicates now live in `Divisible.Basic`:

* `SocialChoice.FairDivision.Divisible.IsEnvyFree`
* `SocialChoice.FairDivision.Divisible.IsProportional`
* `SocialChoice.FairDivision.Divisible.IsEquitable`
* `SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional`

The bundled `MeasureInstance` interface and rule-style cut-and-choose entrypoints live in
`Divisible.Instance` and `Divisible.CutAndChoose`.

## Main result

* `SocialChoice.FairDivision.Divisible.ef_exists_two_agents` — EF allocations always exist for 2 agents with
  non-atomic measures on `[0,1]`

## References

* Steinhaus, "The Problem of Fair Division" (1948)
* Robertson–Webb, *Cake-Cutting Algorithms* (1998), Ch. 1
* Nisan et al., *Algorithmic Game Theory*, Ch. 13
-/

open MeasureTheory
open scoped unitInterval

namespace SocialChoice
namespace FairDivision
namespace Divisible

/-- **EF always exists for 2 agents** on the unit interval `[0,1]`.

    This is exactly the cut-and-choose theorem specialized to an existential statement:
    agent 0 cuts at a fair point, agent 1 chooses their preferred side, and the resulting
    allocation is envy-free. -/
theorem ef_exists_two_agents
    (μ : Fin 2 → Measure I)
    [IsFiniteMeasure (μ 0)] [IsFiniteMeasure (μ 1)]
    [NoAtoms (μ 0)] :
    ∃ A : Allocation (Fin 2) I,
      IsAllocation A ∧ IsEnvyFree (MeasureValuation μ) A :=
  cutAndChoose_ef_exists μ

end Divisible
end FairDivision
end SocialChoice
