/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.SocialChoice.FairDivision.Indivisible.Fairness
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# EconCSLib.SocialChoice.FairDivision.Indivisible.EFX

EFX (envy-free up to any good) allocations for 2 agents.

## Main results

* `IsEFX.of_noEnvy_mono` — if neither agent envies and the valuation is monotone, the
  allocation is EFX (immediate from `IsEnvyFree.isEFX_of_mono`)
* `isEFX_of_singleton_bundle` — if one agent's bundle is a singleton, the other is EFX
  w.r.t. them
* `efx_two_agents_two_goods` — EFX exists for 2 agents and exactly 2 goods
* `efx_exists_two_agents` — EFX always exists for 2 agents with additive nonnegative
  valuations

## EFX existence for 2 agents

**Theorem**: For 2 agents with additive nonneg valuations on any set of goods, a complete
EFX allocation always exists.

**Proof sketch** (maximality argument): Among all complete allocations where agent 0 is
non-envious (`v_0(A_0) ≥ v_0(A_1)`), choose A* to maximize `v_1(A_1)`.

1. Agent 0 is EFX trivially (non-envious by construction).
2. Agent 1: suppose EFX fails at some good `g ∈ A*_0`, i.e., `v_1(A*_0 \ {g}) > v_1(A*_1)`.

   **Case A** (`v_0(A*_0 \ {g}) < v_0(A*_1 ∪ {g})`): the *swap* allocation
   `(A*_1 ∪ {g},  A*_0 \ {g})` has agent 0 non-envious (they get the larger bundle).
   Agent 1 now holds `A*_0 \ {g}` with value `> v_1(A*_1)`. Contradicts maximality of A*.

   **Case B** (`v_0(A*_0 \ {g}) ≥ v_0(A*_1 ∪ {g})`, `v_1(g) > 0`): the allocation
   `(A*_0 \ {g},  A*_1 ∪ {g})` keeps agent 0 non-envious, and
   `v_1(A*_1 ∪ {g}) = v_1(A*_1) + v_1(g) > v_1(A*_1)`. Contradicts maximality of A*.

   **Case C** (Case B with `v_1(g) = 0`): `v_1(A*_0) = v_1(A*_0 \ {g}) > v_1(A*_1) > 0`,
   so some other `g' ∈ A*_0` satisfies `v_1(g') > 0`. Apply Case A or B to `g'`.
   (Terminates since `A*_0` is finite and we exhaust zero-v_1 goods first.)

The formal proof below follows this maximality argument directly. `EnvyCycle.lean`
develops a separate EF1 algorithm for many agents.

## References

* Nisan et al., *Algorithmic Game Theory*, Chapter 11
* Plaut–Roughgarden, "Almost Envy-Freeness with General Valuations" (SODA 2018)
* Chaudhury, Garg, Mehlhorn — "EFX Allocations for Three Agents" (EC 2020)
-/

open Finset

namespace SocialChoice
namespace FairDivision
namespace Indivisible

variable {N G : Type*}

/-! ### Sufficient conditions for EFX -/

/-- If neither agent envies and the valuation is monotone (subsets have less value),
    the allocation is EFX. Immediate from `IsEnvyFree.isEFX_of_mono`.

    Note: no-envy alone does NOT imply EFX without monotonicity. -/
theorem IsEFX.of_noEnvy_mono [DecidableEq G]
    (v : Valuation (Fin 2) G)
    (hmono : ∀ i S T, T ⊆ S → v.val i T ≤ v.val i S)
    (A : Allocation (Fin 2) G)
    (h : IsEnvyFree v A) : IsEFX v A :=
  h.isEFX_of_mono v A hmono

/-! ### EFX when one bundle is a singleton -/

/-- If agent `i`'s bundle is a singleton `{g}`, then agent `j` is EFX with respect to
    agent `i`: removing the sole good from `A i` leaves `∅`, which agent `j` values at
    most their own bundle.

    The hypothesis `h_empty_le : v.val j ∅ ≤ v.val j (A j)` is satisfied whenever
    valuations are additive with nonneg weights (`AdditiveValuation` with `0 ≤ w.weight j g`
    for all `g`). -/
lemma isEFX_of_singleton_bundle [DecidableEq G]
    (v : Valuation (Fin 2) G) (A : Allocation (Fin 2) G)
    (i j : Fin 2) {g : G}
    (hAi : A i = {g})
    (h_empty_le : v.val j ∅ ≤ v.val j (A j)) :
    ∀ h ∈ A i, v.val j (A i \ {h}) ≤ v.val j (A j) := by
  intro h hh
  have heq : h = g := by rwa [hAi, mem_singleton] at hh
  have hempty : A i \ {h} = ∅ := by simp [hAi, heq]
  rw [hempty]
  exact h_empty_le

/-! ### EFX for 2 agents, 2 goods -/

/-- **EFX for 2 agents and 2 goods**: the allocation giving one good to each agent is EFX.

    For any two goods `g₀` and `g₁`, the allocation `A 0 = {g₀}`, `A 1 = {g₁}` satisfies
    EFX for both agents, provided each agent values the empty bundle at most their own good.
    This holds for any additive nonneg valuation (`v.val i ∅ = 0 ≤ v.val i {g}`).

    *Proof*: Each bundle is a singleton. Removing the one element leaves `∅`, so the EFX
    condition reduces to `v.val j ∅ ≤ v.val j (A j)`, which holds by hypothesis. -/
theorem efx_two_agents_two_goods [DecidableEq G]
    (v : Valuation (Fin 2) G) {g₀ g₁ : G}
    (h₀ : v.val 0 ∅ ≤ v.val 0 {g₀})
    (h₁ : v.val 1 ∅ ≤ v.val 1 {g₁})
    (A : Allocation (Fin 2) G) (hA0 : A 0 = {g₀}) (hA1 : A 1 = {g₁}) :
    IsEFX v A := by
  intro i j hij h hh
  fin_cases i
  · -- i = 0
    fin_cases j
    · exact absurd rfl hij              -- j = 0: contradiction
    · -- j = 1: agent 0 EFX w.r.t. agent 1; A 1 = {g₁} is singleton
      apply isEFX_of_singleton_bundle v A 1 0 hA1 _ h hh
      rw [hA0]; exact h₀
  · -- i = 1
    fin_cases j
    · -- j = 0: agent 1 EFX w.r.t. agent 0; A 0 = {g₀} is singleton
      apply isEFX_of_singleton_bundle v A 0 1 hA0 _ h hh
      rw [hA1]; exact h₁
    · exact absurd rfl hij              -- j = 1: contradiction

/-! ### General EFX existence for 2 agents -/

/-- **EFX existence for 2 agents** (general m goods, additive nonneg valuations).

    For any set of goods and additive nonneg valuation, a complete EFX allocation exists.

    The proof uses the maximality argument outlined in the module header. The key
    cases are:
    - Agent 0 EFX follows trivially from the maximality construction.
    - Agent 1 EFX follows by contradiction: a swap or move argument improves agent 1's
      value while preserving agent 0's non-envy, contradicting maximality.

    The residual case (Case C: the best-good argument for zero-v₁ goods) is handled
    by the minimization over `S_star.card`, which rules out keeping the same
    agent-1 value with a strictly smaller chosen bundle. -/

private noncomputable def mkAlloc [DecidableEq G] (allGoods S : Finset G) :
    Allocation (Fin 2) G :=
  fun i => if i = 0 then S else allGoods \ S

private lemma mkAlloc_isAllocation [DecidableEq G] (allGoods S : Finset G)
    (hS : S ⊆ allGoods) : IsAllocation allGoods (mkAlloc allGoods S) := by
  constructor <;> simp_all +decide [ Finset.ext_iff ];
  · exact ⟨ Finset.disjoint_sdiff, Finset.disjoint_sdiff.symm ⟩;
  · intro g; unfold mkAlloc; by_cases hg : g ∈ S <;> aesop;

private lemma feasible_nonempty [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G) (hnn₀ : ∀ g, 0 ≤ w.weight 0 g)
    (allGoods : Finset G) :
    (allGoods.powerset.filter
      (fun S => w.toValuation.val 0 (allGoods \ S) ≤ w.toValuation.val 0 S)).Nonempty := by
  -- Since `allGoods` itself satisfies the condition, the set is nonempty.
  use allGoods
  simp
  convert Finset.sum_nonneg fun g _ => hnn₀ g using 1

private lemma optimal_exists [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G) (hnn₀ : ∀ g, 0 ≤ w.weight 0 g)
    (allGoods : Finset G) :
    ∃ S_star,
      S_star ⊆ allGoods ∧
      w.toValuation.val 0 (allGoods \ S_star) ≤ w.toValuation.val 0 S_star ∧
      (∀ S', S' ⊆ allGoods →
        w.toValuation.val 0 (allGoods \ S') ≤ w.toValuation.val 0 S' →
        w.toValuation.val 1 S_star ≤ w.toValuation.val 1 S') ∧
      (∀ S', S' ⊆ allGoods →
        w.toValuation.val 0 (allGoods \ S') ≤ w.toValuation.val 0 S' →
        w.toValuation.val 1 S' = w.toValuation.val 1 S_star →
        S_star.card ≤ S'.card) := by
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ ∈ allGoods.powerset.filter (fun S => w.toValuation.val 0 (allGoods \ S) ≤ w.toValuation.val 0 S), ∀ S' ∈ allGoods.powerset.filter (fun S => w.toValuation.val 0 (allGoods \ S) ≤ w.toValuation.val 0 S), w.toValuation.val 1 S₁ ≤ w.toValuation.val 1 S' := by
    apply_rules [ Finset.exists_min_image ];
    exact feasible_nonempty w hnn₀ allGoods;
  obtain ⟨S_star, hS_star⟩ : ∃ S_star ∈ (allGoods.powerset.filter (fun S => w.toValuation.val 0 (allGoods \ S) ≤ w.toValuation.val 0 S)).filter (fun S => w.toValuation.val 1 S = w.toValuation.val 1 S₁), ∀ S' ∈ (allGoods.powerset.filter (fun S => w.toValuation.val 0 (allGoods \ S) ≤ w.toValuation.val 0 S)).filter (fun S => w.toValuation.val 1 S = w.toValuation.val 1 S₁), S_star.card ≤ S'.card := by
    apply_rules [ Finset.exists_min_image ];
    exact ⟨ S₁, by aesop ⟩;
  grind

private lemma agent0_efx [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G) (hnn₀ : ∀ g, 0 ≤ w.weight 0 g)
    (allGoods S_star : Finset G)
    (hfeas : w.toValuation.val 0 (allGoods \ S_star) ≤ w.toValuation.val 0 S_star)
    (g : G) :
    w.toValuation.val 0 ((allGoods \ S_star) \ {g}) ≤ w.toValuation.val 0 S_star := by
  exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( by aesop ) fun _ _ _ => hnn₀ _ ) hfeas

private lemma agent1_efx [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G) (hnn₁ : ∀ g, 0 ≤ w.weight 1 g)
    (allGoods S_star : Finset G)
    (hSub : S_star ⊆ allGoods)
    (hMinV : ∀ S', S' ⊆ allGoods →
      w.toValuation.val 0 (allGoods \ S') ≤ w.toValuation.val 0 S' →
      w.toValuation.val 1 S_star ≤ w.toValuation.val 1 S')
    (hMinCard : ∀ S', S' ⊆ allGoods →
      w.toValuation.val 0 (allGoods \ S') ≤ w.toValuation.val 0 S' →
      w.toValuation.val 1 S' = w.toValuation.val 1 S_star →
      S_star.card ≤ S'.card)
    (g : G) (hg : g ∈ S_star) :
    w.toValuation.val 1 (S_star \ {g}) ≤ w.toValuation.val 1 (allGoods \ S_star) := by
  contrapose! hMinV;
  refine' ⟨ if w.toValuation.val 0 ( allGoods \ ( S_star \ { g } ) ) ≤ w.toValuation.val 0 ( S_star \ { g } ) then S_star \ { g } else ( allGoods \ S_star ) ∪ { g }, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · split_ifs <;> aesop;
  · split_ifs <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    rw [ show allGoods \ insert g ( allGoods \ S_star ) = S_star \ { g } from ?_, show insert g ( allGoods \ S_star ) = ( allGoods \ S_star ) ∪ { g } from ?_ ];
    · convert le_trans _ ( le_of_lt ‹_› ) using 1;
      · congr with x ; by_cases hx : x = g <;> aesop;
      · rw [ Finset.sdiff_singleton_eq_erase ];
    · aesop;
    · ext x; by_cases hx : x = g <;> aesop;
  · split_ifs <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase, AdditiveValuation.toValuation ];
    · specialize hMinCard ( S_star.erase g ) ; simp_all +decide;
      exact lt_of_le_of_ne (hnn₁ g) fun h => absurd (hMinCard h.symm)
        ( Nat.not_le_of_gt ( Nat.sub_lt ( Finset.card_pos.mpr ⟨ g, hg ⟩ ) zero_lt_one ) );
    · have hsum : (∑ x ∈ S_star.erase g, w.weight 1 x) =
          (∑ x ∈ S_star, w.weight 1 x) - w.weight 1 g := by
        rw [← Finset.sum_erase_add _ _ hg]
        rw [add_sub_cancel_right]
      have hlt := add_lt_add_left hMinV (w.weight 1 g)
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hlt

/-- **EFX existence for 2 agents** (general m goods, additive nonneg valuations). -/
theorem efx_exists_two_agents [Fintype G] [DecidableEq G]
    (w : AdditiveValuation (Fin 2) G)
    (hnn₀ : ∀ g, 0 ≤ w.weight 0 g)
    (hnn₁ : ∀ g, 0 ≤ w.weight 1 g)
    (allGoods : Finset G) :
    ∃ A : Allocation (Fin 2) G, IsAllocation allGoods A ∧ IsEFX w.toValuation A := by
  obtain ⟨S_star, hSub, hfeas, hMinV, hMinCard⟩ := optimal_exists w hnn₀ allGoods
  refine ⟨mkAlloc allGoods S_star, mkAlloc_isAllocation allGoods S_star hSub, ?_⟩
  intro i j hij g hg
  fin_cases i <;> fin_cases j <;> simp_all [mkAlloc]
  · exact agent0_efx w hnn₀ allGoods S_star hfeas g
  · exact agent1_efx w hnn₁ allGoods S_star hSub hMinV hMinCard g hg

end Indivisible
end FairDivision
end SocialChoice
