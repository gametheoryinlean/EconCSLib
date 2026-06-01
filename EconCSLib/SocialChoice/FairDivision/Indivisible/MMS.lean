/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import EconCSLib.SocialChoice.FairDivision.Indivisible.Implications
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.MMS

Maximin share (MMS) value and α-MMS approximations for indivisible goods.

Valuations and approximation ratios are real-valued throughout this file.

The full-MMS **predicate** ("Is allocation A fair under MMS?") is `IsMaxminShare`, defined
in `Fairness.lean` alongside EF, EF1, EFX, and PROP.  This file adds:

* the **numerical MMS value** `mmsValue` (the actual worst-bundle value an agent can
  guarantee by self-partitioning),
* the **α-MMS approximation predicate** `IsAlphaMMS` (every agent receives ≥ α fraction
  of their MMS value), and
* basic results connecting these to `IsMaxminShare` and to each other.

## Main definitions

* `FairDivision.mmsValue v allGoods i` — the MMS value of agent `i`:
  `sup_{B : n-partition} inf_{j : N} v_i(B_j)`.
* `FairDivision.IsAlphaMMS α v allGoods A` — α-MMS: every agent receives
  ≥ `α` times their MMS value.

## Key results

Proved:
* `iInf_partition_le_mmsValue` — min-bundle of any complete allocation ≤ MMS value.
* `mmsValue_le_of_forall` — MMS value ≤ any upper bound on partition minimums.
* `mmsValue_nonneg` — MMS value is nonneg for nonneg valuations (`[Fintype G]`).
* `mmsValue_le_proportional_share_additive` — `n * mmsValue ≤ v_i(G)`.
* `isMaxminShare_iff_isAlphaMMS_one` — `IsMaxminShare` coincides with `IsAlphaMMS 1`.
* `isAlphaMMS_zero` — 0-MMS is trivially satisfied for nonneg valuations.
* `isAlphaMMS_mono_alpha` — α-MMS is monotone decreasing in α.
* `IsMaxminShare.isAlphaMMS` — full MMS implies α-MMS for `0 ≤ α ≤ 1`.
* `IsProportional.isAlphaMMS_additive` — PROP implies α-MMS for all `0 ≤ α ≤ 1`.

## Fairness hierarchy

For additive valuations with complete allocations:
```
EF → EFX → EF1 → PROP → MMS → α-MMS  (0 ≤ α ≤ 1)
```
Unlike EF, EF1, and PROP, full MMS is **not always achievable** for n ≥ 3 agents
[Procaccia-Wang 2014]. However, (3/4)-MMS is always achievable [Garg-Taki 2021].

## References

* Budish — "The Combinatorial Assignment Problem" (JPE 2011) [MMS concept]
* Procaccia, Wang — "Fair Enough: Guaranteeing Approximate Maximin Shares" (EC 2014)
* Amanatidis, Markakis, Nikzad, Saberi — "Approximation Algorithms for Computing Maximin
  Share Allocations" (ACM TALG 2017)
* Garg, Taki — "An Improved Approximation Algorithm for Maximin Shares" (EC 2021)
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### MMS value -/

/-- The **maximin share (MMS) value** of agent `i` with respect to valuation `v`
    and good set `allGoods`.

    `mmsValue v allGoods i = sup_{B : n-partition} inf_{j : N} v_i(B_j)`.

    Intuitively: the best (highest) minimum-bundle value agent `i` can guarantee by
    proposing a complete `n`-partition of `allGoods`. The outer `iSup` ranges over all
    complete allocations `{B // IsAllocation allGoods B}`; the inner `iInf` ranges over
    all agent indices `j : N` (the bundle labels).

    The corresponding **predicate** ("did agent `i` receive at least their MMS value?") is
    `IsMaxminShare` in `Fairness.lean`. See `isMaxminShare_iff_isAlphaMMS_one` for the
    connection.

    If no complete allocation exists (e.g., `N = ∅`), `iSup` over the empty subtype
    yields `sSup ∅ = 0` in ℝ. Use `[Nonempty N]` to ensure a complete allocation exists.

    [Budish 2011; AGT Ch.11] -/
noncomputable def mmsValue [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (i : N) : ℝ :=
  iSup fun B : {A : Allocation N G // IsAllocation allGoods A} =>
    iInf fun j : N => v.val i (B.val j)

/-! ### IsAlphaMMS — approximate MMS allocation -/

/-- An allocation `A` is **α-MMS** if every agent receives at least `α` times their
    MMS value.

    `IsAlphaMMS α v allGoods A ↔ ∀ i, α * mmsValue v allGoods i ≤ v.val i (A i)`.

    The scalar `α : ℝ` quantifies approximation quality:
    - `α = 1`: full MMS, equivalent to `IsMaxminShare` from `Fairness.lean`
      (see `isMaxminShare_iff_isAlphaMMS_one`).
    - `α = 3/4`: always achievable for additive valuations
      (see `exists_isAlphaMMS_threefourths`).
    - `α = 0`: trivially satisfied for nonneg valuations (see `isAlphaMMS_zero`).

    [Budish 2011; Amanatidis et al. 2017; Garg-Taki 2021] -/
def IsAlphaMMS [Fintype N] [DecidableEq G]
    (α : ℝ) (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  ∀ i : N, α * mmsValue v allGoods i ≤ v.val i (A i)

/-! ### Properties of mmsValue -/

section BasicMmsValue

variable [Fintype N] [DecidableEq G]

/-- The min-bundle value of any complete allocation is at most the MMS value.

    For any complete allocation `B`:
    `iInf_{j : N} v_i(B_j) ≤ mmsValue v allGoods i`.

    Requires `BddAbove` of the range of all per-allocation minimums, which holds
    when `[Fintype G]` (finitely many partitions).

    [Budish 2011] -/
lemma iInf_partition_le_mmsValue
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (B : Allocation N G) (hB : IsAllocation allGoods B)
    (hbdd : BddAbove (Set.range fun X : {A : Allocation N G // IsAllocation allGoods A} =>
        iInf fun j : N => v.val i (X.val j))) :
    iInf (fun j : N => v.val i (B j)) ≤ mmsValue v allGoods i :=
  le_ciSup hbdd ⟨B, hB⟩

/-- The MMS value is at most any upper bound on all per-allocation minimum bundle values.

    If `ub` is an upper bound — for every complete allocation `B`,
    `iInf_j v_i(B_j) ≤ ub` — then `mmsValue v allGoods i ≤ ub`.

    `hne` is needed because `ciSup_le` requires the index type to be nonempty. -/
lemma mmsValue_le_of_forall
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A})
    (ub : ℝ)
    (h : ∀ B : Allocation N G, IsAllocation allGoods B →
        iInf (fun j : N => v.val i (B j)) ≤ ub) :
    mmsValue v allGoods i ≤ ub := by
  haveI : Nonempty {A : Allocation N G // IsAllocation allGoods A} := hne
  exact ciSup_le fun ⟨B, hB⟩ => h B hB

/-- For nonneg valuations with at least one complete allocation, the MMS value is nonneg.

    `hne` ensures the `iSup` is nonempty. `[Fintype G]` makes the allocation subtype
    `[Finite]`, enabling `Finite.le_ciSup` without a separate `BddAbove` hypothesis. -/
lemma mmsValue_nonneg [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A})
    (hnonneg : ∀ S : Finset G, 0 ≤ v.val i S) :
    0 ≤ mmsValue v allGoods i := by
  haveI : Nonempty N := ⟨i⟩
  haveI : Fintype (Finset G) := Finset.fintype
  haveI : DecidableEq N := Classical.typeDecidableEq N
  haveI : Fintype (Allocation N G) :=
    @Pi.instFintype N (fun _ => Finset G) _ _ (fun _ => inferInstance)
  haveI : DecidablePred (fun A' : Allocation N G => IsAllocation allGoods A') :=
    Classical.decPred _
  haveI : Finite {A : Allocation N G // IsAllocation allGoods A} := inferInstance
  obtain ⟨⟨B, hB⟩⟩ := hne
  calc 0 ≤ iInf (fun j : N => v.val i (B j)) :=
        le_ciInf (fun j => hnonneg (B j))
    _ ≤ mmsValue v allGoods i :=
        Finite.le_ciSup (fun B' : {A : Allocation N G // IsAllocation allGoods A} =>
          iInf fun j : N => v.val i (B'.val j)) ⟨B, hB⟩

/-- For additive valuations, the MMS value is at most the proportional share:
    `n * mmsValue ≤ v_i(allGoods)`.

    *Proof*: For any complete `B`, `min_j v_i(B_j) ≤ avg_j v_i(B_j) = v_i(allGoods)/n`
    (minimum ≤ average). Since this bound holds for every `B`, it holds for the supremum
    `mmsValue = sup_B min_j v_i(B_j)`. Uses `mmsValue_le_of_forall`.

    `i : N` guarantees `Fintype.card N ≥ 1`, so division by `n` is safe.

    [Budish 2011] -/
lemma mmsValue_le_proportional_share_additive
    (w : AdditiveValuation N G)
    (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A}) :
    (Fintype.card N : ℝ) * mmsValue w.toValuation allGoods i ≤
      w.toValuation.val i allGoods := by
  have hn_pos : (0 : ℝ) < Fintype.card N :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hmms_bound : mmsValue w.toValuation allGoods i ≤
      w.toValuation.val i allGoods / (Fintype.card N : ℝ) := by
    apply mmsValue_le_of_forall w.toValuation allGoods i hne
    intro B hB
    rw [le_div_iff₀ hn_pos]
    calc iInf (fun j : N => w.toValuation.val i (B j)) * (Fintype.card N : ℝ)
        = (Fintype.card N : ℝ) * iInf (fun j : N => w.toValuation.val i (B j)) :=
            mul_comm _ _
      _ = ∑ _j : N, iInf (fun j' : N => w.toValuation.val i (B j')) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ j : N, w.toValuation.val i (B j) :=
            Finset.sum_le_sum (fun j _ => Finite.ciInf_le _ j)
      _ = w.toValuation.val i allGoods := by
            simp only [AdditiveValuation.toValuation]
            rw [hB.complete, Finset.sum_biUnion (fun a _ b _ hab => hB.disjoint a b hab)]
  calc (Fintype.card N : ℝ) * mmsValue w.toValuation allGoods i
      ≤ (Fintype.card N : ℝ) * (w.toValuation.val i allGoods / (Fintype.card N : ℝ)) :=
          mul_le_mul_of_nonneg_left hmms_bound (le_of_lt hn_pos)
    _ = w.toValuation.val i allGoods := by field_simp

end BasicMmsValue

/-! ### Connection to IsMaxminShare and α-MMS -/

section Bridge

variable [Fintype N] [DecidableEq G]

/-- `IsMaxminShare` from `Fairness.lean` coincides with `IsAlphaMMS 1`.

    **→ direction** (`IsMaxminShare → IsAlphaMMS 1`): for every complete `B`, there exists
    `j` with `v_i(B_j) ≤ v_i(A_i)`, so `iInf_j v_i(B_j) ≤ v_i(A_i)`. Then `ciSup_le`
    gives `mmsValue ≤ v_i(A_i)`, and `1 * mmsValue = mmsValue` by `one_mul`.

    **← direction** (`IsAlphaMMS 1 → IsMaxminShare`): for any complete `B`,
    `iInf_j v_i(B_j) ≤ mmsValue ≤ v_i(A_i)`. Since `N` is `Nonempty` and `Fintype`,
    the infimum is achieved at some `j*`, giving `v_i(B_{j*}) ≤ v_i(A_i)`.

    `[Nonempty N]` ensures `iInf` is nonempty. `[Fintype G]` makes the allocation subtype
    `[Finite]`, enabling `Finite.le_ciSup` in the ← direction.
    `hne` is required by the → direction (to call `ciSup_le`). -/
theorem isMaxminShare_iff_isAlphaMMS_one
    [Nonempty N] [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hne : Nonempty {A' : Allocation N G // IsAllocation allGoods A'}) :
    IsMaxminShare v allGoods A ↔ IsAlphaMMS 1 v allGoods A := by
  constructor
  · intro hmms
    simp only [IsAlphaMMS, one_mul]
    intro i
    haveI : Nonempty {A' : Allocation N G // IsAllocation allGoods A'} := hne
    apply ciSup_le
    intro ⟨B, hB⟩
    obtain ⟨j, hj⟩ := hmms i B hB
    exact le_trans (Finite.ciInf_le (fun j' => v.val i (B j')) j) hj
  · intro halpha i B hB
    simp only [IsAlphaMMS, one_mul] at halpha
    haveI : Fintype (Finset G) := Finset.fintype
    haveI : DecidableEq N := Classical.typeDecidableEq N
    haveI : Fintype (Allocation N G) :=
      @Pi.instFintype N (fun _ => Finset G) _ _ (fun _ => inferInstance)
    haveI : DecidablePred (fun A' : Allocation N G => IsAllocation allGoods A') :=
      Classical.decPred _
    haveI : Finite {A' : Allocation N G // IsAllocation allGoods A'} := inferInstance
    obtain ⟨j, _, hj_min⟩ := Finset.exists_min_image Finset.univ (fun j => v.val i (B j))
      ⟨Classical.choice ‹Nonempty N›, Finset.mem_univ _⟩
    refine ⟨j, ?_⟩
    by_contra h_neg
    push_neg at h_neg
    have h1 : iInf (fun j' : N => v.val i (B j')) = v.val i (B j) :=
      le_antisymm (Finite.ciInf_le _ j) (le_ciInf fun j' => hj_min j' (Finset.mem_univ _))
    have h2 : v.val i (A i) < iInf (fun j' : N => v.val i (B j')) := h1 ▸ h_neg
    have h3 : iInf (fun j' : N => v.val i (B j')) ≤ mmsValue v allGoods i :=
      Finite.le_ciSup (fun B' : {A' : Allocation N G // IsAllocation allGoods A'} =>
        iInf fun j' => v.val i (B'.val j')) ⟨B, hB⟩
    exact absurd (lt_of_lt_of_le h2 (le_trans h3 (halpha i))) (lt_irrefl _)

end Bridge

/-! ### Monotonicity and basic implications for α-MMS -/

section MonoAlpha

variable [Fintype N] [DecidableEq G]

/-- **α-MMS is monotone decreasing in α**: if `A` is α-MMS and `β ≤ α`, then `A` is β-MMS.

    *Proof*: `β * mmsValue ≤ α * mmsValue ≤ v_i(A_i)` since `β ≤ α` and `mmsValue ≥ 0`. -/
theorem isAlphaMMS_mono_alpha
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (α β : ℝ) (hβα : β ≤ α)
    (hmms_nn : ∀ i, 0 ≤ mmsValue v allGoods i)
    (hα : IsAlphaMMS α v allGoods A) :
    IsAlphaMMS β v allGoods A := by
  intro i
  calc β * mmsValue v allGoods i
      ≤ α * mmsValue v allGoods i := mul_le_mul_of_nonneg_right hβα (hmms_nn i)
    _ ≤ v.val i (A i)             := hα i

/-- Every allocation trivially satisfies **0-MMS** for nonneg valuations.

    `0 * mmsValue = 0 ≤ v_i(A_i)` by `zero_mul` and nonnegativity. -/
theorem isAlphaMMS_zero
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hnonneg : ∀ i S, 0 ≤ v.val i S) :
    IsAlphaMMS 0 v allGoods A := by
  intro i
  show 0 * mmsValue v allGoods i ≤ v.val i (A i)
  rw [zero_mul]
  exact hnonneg i (A i)

/-- **`IsMaxminShare` implies α-MMS** for `α ≤ 1` and nonneg MMS values. -/
theorem IsMaxminShare.isAlphaMMS
    [Nonempty N] [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hne : Nonempty {A' : Allocation N G // IsAllocation allGoods A'})
    (hMMS : IsMaxminShare v allGoods A)
    (α : ℝ) (hα_le : α ≤ 1)
    (hmms_nn : ∀ i, 0 ≤ mmsValue v allGoods i) :
    IsAlphaMMS α v allGoods A :=
  isAlphaMMS_mono_alpha v allGoods A 1 α hα_le hmms_nn
    ((isMaxminShare_iff_isAlphaMMS_one v allGoods A hne).mp hMMS)

end MonoAlpha

/-! ### Proportionality implies α-MMS -/

section PropImpliesMMS

variable [Fintype N] [DecidableEq G]

/-- **PROP implies α-MMS** for additive valuations and `α ≤ 1`.

    Follows by chaining:
    `IsProportional.isMaxminShare` → `isMaxminShare_iff_isAlphaMMS_one.mp`
    → `IsMaxminShare.isAlphaMMS`.

    [Budish 2011] -/
theorem IsProportional.isAlphaMMS_additive
    [Nonempty N] [Fintype G]
    (w : AdditiveValuation N G)
    {allGoods : Finset G} {A : Allocation N G}
    (hne : Nonempty {A' : Allocation N G // IsAllocation allGoods A'})
    (hProp : IsProportional (Fintype.card N) w.toValuation allGoods A)
    (α : ℝ) (hα_le : α ≤ 1)
    (hmms_nn : ∀ i, 0 ≤ mmsValue w.toValuation allGoods i) :
    IsAlphaMMS α w.toValuation allGoods A :=
  IsMaxminShare.isAlphaMMS w.toValuation allGoods A hne
    (IsProportional.isMaxminShare w hProp) α hα_le hmms_nn

end PropImpliesMMS

end Indivisible
end FairDivision
end SocialChoice
