/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import EconCSLib.SocialChoice.FairDivision.Welfare
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.SocialWelfare

Utilitarian and egalitarian social welfare for indivisible goods allocation.

## Main definitions

* `FairDivision.utilitarianWelfare v A` — sum of all agents' bundle values: `∑ i, v_i(A_i)`
* `FairDivision.egalitarianWelfare v A` — minimum over agents of bundle value: `min_i v_i(A_i)`
* `FairDivision.IsUtilitarianOptimal` — no complete allocation achieves higher utilitarian welfare
* `FairDivision.IsMaxmin` — no complete allocation achieves higher egalitarian welfare

## Design

Social welfare functions are the natural objectives for optimization-based allocation rules.

`utilitarianWelfare` requires `[Fintype N]`.
`egalitarianWelfare` requires `[Fintype N] [Nonempty N]` — the `Nonempty N`
constraint ensures the minimum over agents is well-defined (avoids min over an empty set).

Both are `noncomputable` because they sum/minimize over abstract types using `Finset.univ`.

**Egalitarian welfare and MMS**: `IsMaxmin` (egalitarian optimality) is a social optimality
notion (maximize the minimum across all agents simultaneously), whereas `IsMaxminShare`
(in `Fairness.lean`) is a per-agent guarantee (each agent could guarantee themselves at least
this much). These two notions are generally incomparable.

## References

* Bouveret, Chevaleyre, Maudet — "Fair Allocation of Indivisible Goods" (COMSOC Handbook, Ch. 12)
* Nisan et al., *Algorithmic Game Theory*, Ch. 11–12
-/

open BigOperators Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### Utilitarian social welfare -/

/-- Utilitarian social welfare: the sum of all agents' bundle values.

    `sw_U(A) = ∑_{i ∈ N} v_i(A_i)`.

    Maximizing utilitarian welfare produces *utilitarian optimal* allocations — generally
    not fair, since all value may concentrate on one agent. The ratio between utilitarian
    optimal welfare and the welfare of the best fair allocation is the *price of fairness*.

    Requires `[Fintype N]` to sum over all agents.
    [BCM Ch.12] -/
noncomputable abbrev utilitarianWelfare [Fintype N]
    (v : Valuation N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.utilitarianWelfare v.val A

/-! ### Egalitarian (maximin) social welfare -/

/-- Egalitarian social welfare: the minimum of all agents' bundle values.

    `sw_E(A) = min_{i ∈ N} v_i(A_i)`.

    Maximizing egalitarian welfare yields the *maximin* allocation: it makes the worst-off
    agent as well off as possible. For this to be meaningful, agent valuations should be
    comparable (e.g., all normalized to total value 1 over all goods).

    Requires `[Fintype N] [Nonempty N]` so the minimum is taken over a nonempty set.
    [BCM Ch.12, Def 12.6] -/
noncomputable abbrev egalitarianWelfare [Fintype N] [Nonempty N]
    (v : Valuation N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.egalitarianWelfare v.val A

/-! ### Optimality notions -/

/-- Utilitarian optimal: no complete allocation of `allGoods` achieves strictly higher
    utilitarian (sum) social welfare.

    `[Fintype N] [DecidableEq G]` are required by `IsAllocation`. -/
abbrev IsUtilitarianOptimal [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsUtilitarianOptimal (fun B => IsAllocation allGoods B) v.val A

/-- Maximin (egalitarian) optimal: no complete allocation of `allGoods` achieves higher
    egalitarian (minimum-agent) welfare.

    A maximin allocation makes the worst-off agent as well off as possible. This is the
    egalitarian counterpart to utilitarian optimality, and is distinct from the per-agent
    maximin share guarantee (`IsMaxminShare` in `Fairness.lean`):
    - `IsMaxmin` is a global property: it is the best possible for the social minimum.
    - `IsMaxminShare` is per-agent: each agent individually gets at least their MMS value.

    `[Nonempty N]` ensures `egalitarianWelfare` is well-defined.
    [BCM Ch.12, Def 12.6] -/
abbrev IsMaxmin [Fintype N] [Nonempty N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsMaxmin (fun B => IsAllocation allGoods B) v.val A

/-! ### Basic lemmas -/

section BasicLemmas

variable [Fintype N]

/-- Utilitarian welfare is monotone: pointwise improvement implies welfare improvement.

    The valuation codomain is fixed to `ℝ`, so no ordered-algebra assumptions are needed. -/
lemma utilitarianWelfare_mono
    (v : Valuation N G) (A B : Allocation N G)
    (h : ∀ i : N, v.val i (A i) ≤ v.val i (B i)) :
    utilitarianWelfare v A ≤ utilitarianWelfare v B :=
  SocialChoice.FairDivision.utilitarianWelfare_mono v.val A B h

/-- The utilitarian welfare of an allocation with a unique agent equals that agent's value. -/
@[simp]
lemma utilitarianWelfare_unique [Unique N]
    (v : Valuation N G) (A : Allocation N G) :
    utilitarianWelfare v A = v.val default (A default) := by
  simp [utilitarianWelfare]

/-- Egalitarian welfare is bounded above by any agent's bundle value. -/
lemma egalitarianWelfare_le [Nonempty N]
    (v : Valuation N G) (A : Allocation N G) (i : N) :
    egalitarianWelfare v A ≤ v.val i (A i) :=
  SocialChoice.FairDivision.egalitarianWelfare_le v.val A i

/-- Egalitarian welfare is bounded above by utilitarian welfare divided by n, informally.
    Formally (without division): `n • egalitarianWelfare v A ≤ utilitarianWelfare v A`
    for nonneg-valued additive allocations.

    The valuation codomain is fixed to `ℝ`, so no ordered-algebra assumptions are needed. -/
lemma nsmul_egalitarianWelfare_le_utilitarianWelfare
    [Nonempty N]
    (v : Valuation N G) (A : Allocation N G)
    (hle : ∀ i : N, egalitarianWelfare v A ≤ v.val i (A i)) :
    Fintype.card N • egalitarianWelfare v A ≤ utilitarianWelfare v A := by
  simpa [egalitarianWelfare, utilitarianWelfare] using
    (SocialChoice.FairDivision.nsmul_egalitarianWelfare_le_utilitarianWelfare v.val A hle)

end BasicLemmas

end Indivisible
end FairDivision
end SocialChoice
