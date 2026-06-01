/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.Basic
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import EconCSLib.Math.Simplex
import EconCSLib.Math.FixedPoint.Brouwer_product
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousOn

/-!
# EconCSLib.GameTheory.StrategicGame.Nash

Best-response map (`nash_map`) for n-player finite strategic games,
and its continuity. Together with Brouwer's fixed-point theorem these
are the two ingredients for the Nash existence theorem (SG-L2 #199).

## Main definitions

* `evaluate_at_mixed G i σ` — expected payoff of player `i` under mixed profile `σ`;
  equals `∑_{s : Profile G} (∏_j σ_j(s_j)) · G.payoff s i`.
* `mixed_g G i m` — the multilinear payoff functional on arbitrary weight vectors
  `m : ∀ i, G.strategy i → ℝ`; used as an intermediate form inside proofs.
* `g_function G i σ a` — the augmented weight `σ_i(a) + max 0 (EU(σ[i↦a]) - EU(σ))`.
* `nash_map G σ` — the best-response map; normalizes `g_function` to a mixed profile.
  It is a continuous self-map on the product of standard simplices.
* `mixedNashEquilibrium G σ` — `σ` is a mixed Nash equilibrium of `G`.

## Main results

* `sigma_le_g_function` — `σ_i(a) ≤ g_function i σ a` (pointwise lower bound).
* `g_function_nonneg` — `0 ≤ g_function i σ a`.
* `one_le_sum_g` — `1 ≤ ∑_a g_function i σ a`.
* `nash_map_cert` — the normalized weights form a valid probability distribution.
* `nash_map_cont` — `nash_map G` is continuous.
* `exists_mixed_nash_equilibrium_finite` — every finite n-player strategic game has a
  mixed Nash equilibrium (proved via `Brouwer_Product`).

## Design

We work with the raw type `∀ i, stdSimplex ℝ (G.strategy i)` (the product of
standard simplices) rather than the defined `MixedProfile G`, so that Lean's
type-class machinery automatically finds the product topology. The payoff
convention follows EconCSLib: `G.payoff s i` is player `i`'s payoff at pure
profile `s`.

## References

* [Nash 1951] J. Nash, "Non-cooperative Games", *Ann. Math.* 54(2):286–295.
* Source: `math-xmum/Brouwer/Gametheory/Nash.lean`.
* [MFoGT §4.6.2] Maschler, Solan, Zamir, *Game Theory*, Brouwer-based Nash existence.
-/

open BigOperators Function

set_option linter.unusedSectionVars false

noncomputable section

namespace StrategicGame

variable {N : Type*}
variable (G : StrategicGame N ℝ)
variable [Fintype N] [DecidableEq N]
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
variable [∀ i, Inhabited (G.strategy i)]

/-- Type abbreviation for the product of standard simplices (one per player),
    used throughout this file. Defined as an `abbrev` so Lean unfolds it
    automatically for topology and continuity instances. -/
abbrev MixedS := ∀ i, stdSimplex ℝ (G.strategy i)

/-! ### Mixed-payoff functional -/

/-- Expected payoff of player `i` under mixed profile `σ`.
    Sums over all pure profiles, weighting by the product of each player's
    probability. -/
def evaluate_at_mixed (i : N) (σ : MixedS G) : ℝ :=
  ∑ s : G.Profile, (∏ j : N, (σ j).val (s j)) * G.payoff s i

/-- Multilinear payoff functional on raw weight vectors `m : ∀ i, G.strategy i → ℝ`.
    Same as `evaluate_at_mixed` but with arbitrary (not necessarily
    probability-normalized) weights; used inside continuity arguments. -/
def mixed_g (i : N) (m : ∀ i, G.strategy i → ℝ) : ℝ :=
  ∑ s : G.Profile, (∏ j : N, m j (s j)) * G.payoff s i

/-- `evaluate_at_mixed` is the restriction of `mixed_g` to simplex weights. -/
theorem evaluate_at_mixed_eq_mixed_g (i : N) (σ : MixedS G) :
    evaluate_at_mixed G i σ = mixed_g G i (fun j => (σ j).val) := by
  simp [evaluate_at_mixed, mixed_g]

/-! ### Best-response augmentation -/

/-- Augmented weight for pure strategy `a` of player `i` at mixed profile `σ`:
    the original probability `σ_i(a)` plus the positive part of the gain from
    deviating to pure strategy `a`. -/
def g_function (i : N) (σ : MixedS G) (a : G.strategy i) : ℝ :=
  (σ i).val a +
    max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) -
           evaluate_at_mixed G i σ)

/-- The augmented weight is at least `σ_i(a)`. -/
lemma sigma_le_g_function (i : N) (σ : MixedS G) (a : G.strategy i) :
    (σ i).val a ≤ g_function G i σ a := by
  simp [g_function]

/-- The augmented weight is nonnegative. -/
lemma g_function_nonneg (i : N) (σ : MixedS G) (a : G.strategy i) :
    0 ≤ g_function G i σ a := by
  have h1 : 0 ≤ (σ i).val a := (σ i).property.1 a
  linarith [sigma_le_g_function G i σ a]

/-- The sum of augmented weights is at least 1. -/
lemma one_le_sum_g (i : N) (σ : MixedS G) :
    1 ≤ ∑ a : G.strategy i, g_function G i σ a := by
  calc 1 = ∑ a : G.strategy i, (σ i).val a := (σ i).property.2.symm
    _ ≤ ∑ a : G.strategy i, g_function G i σ a :=
        Finset.sum_le_sum fun a _ => sigma_le_g_function G i σ a

/-! ### Nash map -/

/-- The normalized augmented weight: `g_function i σ a / ∑_b g_function i σ b`.
    Private auxiliary used to construct `nash_map`. -/
private def nash_map_aux (σ : MixedS G) (i : N) (a : G.strategy i) : ℝ :=
  g_function G i σ a / ∑ b : G.strategy i, g_function G i σ b

/-- The normalized augmented weights form a valid probability distribution
    on `G.strategy i`. -/
lemma nash_map_cert (σ : MixedS G) (i : N) :
    nash_map_aux G σ i ∈ stdSimplex ℝ (G.strategy i) := by
  have hd : 0 < ∑ b : G.strategy i, g_function G i σ b :=
    lt_of_lt_of_le one_pos (one_le_sum_g G i σ)
  constructor
  · intro a
    exact div_nonneg (g_function_nonneg G i σ a) (le_of_lt hd)
  · simp only [nash_map_aux, ← Finset.sum_div]
    exact div_self (ne_of_gt hd)

/-- The Nash best-response map: sends a mixed profile `σ` to the profile where
    each player `i` plays proportional to `g_function i σ`. A fixed point of
    this map is a mixed Nash equilibrium. -/
def nash_map (σ : MixedS G) : MixedS G :=
  fun i => ⟨nash_map_aux G σ i, nash_map_cert G σ i⟩

/-! ### Continuity -/

/-- `evaluate_at_mixed G i` is continuous in the mixed profile. -/
private lemma evaluate_at_mixed_cont (i : N) :
    Continuous (fun σ : MixedS G => evaluate_at_mixed G i σ) := by
  unfold evaluate_at_mixed
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro j _
  have h1 : Continuous (fun σ : MixedS G => σ j) := continuous_apply j
  have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy j) => x.val (s j)) :=
    (continuous_apply (s j)).comp continuous_subtype_val
  exact h2.comp h1

/-- `σ ↦ evaluate_at_mixed G i (update σ i (stdSimplex.pure a))` is continuous. -/
private lemma evaluate_at_mixed_update_cont (i : N) (a : G.strategy i) :
    Continuous (fun σ : MixedS G =>
      evaluate_at_mixed G i (update σ i (stdSimplex.pure a))) := by
  unfold evaluate_at_mixed
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro j _
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact continuous_const
  · simp only [ne_eq, h, not_false_eq_true, Function.update_of_ne]
    have h1 : Continuous (fun σ : MixedS G => σ j) := continuous_apply j
    have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy j) => x.val (s j)) :=
      (continuous_apply (s j)).comp continuous_subtype_val
    exact h2.comp h1

/-- `g_function G i (· ) a` is continuous in the mixed profile (fixed `i`, `a`). -/
private lemma g_function_cont (i : N) (a : G.strategy i) :
    Continuous (fun σ : MixedS G => g_function G i σ a) := by
  unfold g_function
  apply Continuous.add
  · have h1 : Continuous (fun σ : MixedS G => σ i) := continuous_apply i
    have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy i) => x.val a) :=
      (continuous_apply a).comp continuous_subtype_val
    exact h2.comp h1
  · apply Continuous.max continuous_const
    exact (evaluate_at_mixed_update_cont G i a).sub (evaluate_at_mixed_cont G i)

/-- `nash_map G` is a continuous self-map of the product simplex. -/
theorem nash_map_cont : Continuous (nash_map G) := by
  unfold nash_map nash_map_aux
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  apply Continuous.div
  · exact g_function_cont G i a
  · exact continuous_finset_sum _ fun b _ => g_function_cont G i b
  · intro σ
    exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_sum_g G i σ))

/-! ### Nash equilibrium predicate and existence theorem -/

/-- `evaluate_at_mixed G i` is linear in the `i`-th mixed strategy: for any
    `τ : stdSimplex ℝ (G.strategy i)`,
    `evaluate_at_mixed G i (update σ i τ) =
      ∑ a, (τ.val a) * evaluate_at_mixed G i (update σ i (stdSimplex.pure a))`. -/
lemma evaluate_at_mixed_linear (i : N) (σ : MixedS G) (τ : stdSimplex ℝ (G.strategy i)) :
    evaluate_at_mixed G i (update σ i τ) =
      ∑ a : G.strategy i, (τ.val a) * evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) := by
  simp only [evaluate_at_mixed, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext s
  -- Let P = ∏_{j≠i} σ_j(s_j) be the "other players" factor (independent of player i's strategy)
  set P := ∏ j ∈ Finset.univ.erase i, (σ j).val (s j) with hP_def
  -- The τ product factors as τ(s_i) * P
  have htau_prod : ∏ j : N, (update σ i τ j).val (s j) = τ.val (s i) * P := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [Function.update_self]
    · apply Finset.prod_congr rfl; intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  -- The pure-strategy product factors as (if s_i = a then 1 else 0) * P
  have hpure_prod : ∀ a : G.strategy i,
      ∏ j : N, (update σ i (stdSimplex.pure a) j).val (s j) =
        (if s i = a then 1 else 0) * P := by
    intro a
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [Function.update_self, stdSimplex.pure_apply]
    · apply Finset.prod_congr rfl; intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [htau_prod]
  simp_rw [hpure_prod]
  ring_nf
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  ring

/-- Nash equilibrium predicate at the mixed-profile level: `σ` is a Nash equilibrium of `G`
    if no player `i` can improve by unilaterally deviating to any mixed strategy `τ`. -/
def mixedNashEquilibrium (G : StrategicGame N ℝ) [Fintype N] [∀ i, Fintype (G.strategy i)] :
    MixedS G → Prop :=
  fun σ => ∀ i (τ : stdSimplex ℝ (G.strategy i)),
    evaluate_at_mixed G i (update σ i τ) ≤ evaluate_at_mixed G i σ

/-- Helper: weighted-average inequality on the simplex.
    If `∑_i σ_i * f_i = c`, then there exists `i` with `0 < σ_i` and `f i ≤ c`. -/
private lemma wsum_magic_ineq {X : Type*} [Fintype X]
    {p : stdSimplex ℝ X} {f : X → ℝ} {c : ℝ}
    (H : ∑ a : X, p.val a * f a = c) : ∃ a, 0 < p.val a ∧ f a ≤ c := by
  by_contra Hall
  push_neg at Hall
  -- Hall : ∀ a, 0 < p.val a → c < f a (after push_neg of ∀ a, ¬(0 < p.val a ∧ f a ≤ c))
  -- Actually push_neg gives: ∀ a, 0 < p.val a → c < f a
  have hpos : ∃ a, 0 < p.val a := by
    by_contra h_all_npos
    push_neg at h_all_npos
    have hzero : ∀ a, p.val a = 0 :=
      fun a => le_antisymm (h_all_npos a) (p.property.1 a)
    have : (∑ a : X, p.val a) = 0 := by simp [hzero]
    linarith [p.property.2]
  have hgt : c < ∑ a : X, p.val a * f a := by
    have hsum_c : ∑ a : X, p.val a * c = c := by
      rw [← Finset.sum_mul, p.property.2, one_mul]
    rw [← hsum_c]
    apply Finset.sum_lt_sum
    · intro a _
      by_cases ha : 0 < p.val a
      · exact mul_le_mul_of_nonneg_left (Hall a ha).le (p.property.1 a)
      · push_neg at ha
        have := le_antisymm ha (p.property.1 a)
        simp [this]
    · obtain ⟨a₀, ha₀⟩ := hpos
      exact ⟨a₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (Hall a₀ ha₀) ha₀⟩
  linarith [H ▸ hgt]

/-- Main theorem: every finite n-player strategic game has a mixed Nash equilibrium.

    Proof: transport `nash_map G` via player-index and strategy equivalences to a continuous
    self-map of `ProductSimplices card'` (where the players are reindexed as `Fin n` and
    `card' k = |G.strategy (eI.symm k)|`), apply `Brouwer_Product` to get a fixed point,
    transport back to `MixedS G`, and use the fixed-point equation to certify Nash equilibrium. -/
theorem exists_mixed_nash_equilibrium_finite
    (G : StrategicGame N ℝ) [Fintype N] [DecidableEq N]
    [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    [∀ i, Inhabited (G.strategy i)] [Inhabited N] :
    ∃ σ : MixedS G, mixedNashEquilibrium G σ := by
  classical
  -- Step 1: index players as Fin n
  let n : ℕ := Fintype.card N
  have n_pos : 0 < n := Fintype.card_pos
  let eI : N ≃ Fin n := Fintype.equivFin N
  letI : Inhabited (Fin n) := ⟨⟨0, n_pos⟩⟩
  -- Step 2: strategy cardinalities card' : Fin n → ℕ+
  let card' : Fin n → ℕ+ :=
    fun k => ⟨Fintype.card (G.strategy (eI.symm k)), Fintype.card_pos⟩
  -- Step 3: strategy equivalences eS k : G.strategy (eI.symm k) ≃ Fin (card' k)
  let eS : (k : Fin n) → G.strategy (eI.symm k) ≃ Fin (card' k) := fun k => Fintype.equivFin _
  -- Step 4: reindexing maps (player-level)
  let reindex : MixedS G → ((k : Fin n) → stdSimplex ℝ (G.strategy (eI.symm k))) :=
    fun σ k => σ (eI.symm k)
  let reindex_inv : ((k : Fin n) → stdSimplex ℝ (G.strategy (eI.symm k))) → MixedS G :=
    fun y i => (eI.symm_apply_apply i) ▸ y (eI i)
  have reindex_left : ∀ σ, reindex_inv (reindex σ) = σ := by
    intro σ; funext i
    exact congrFun ((Equiv.piCongrLeft (fun i => stdSimplex ℝ (G.strategy i)) eI.symm).right_inv σ) i
  -- Step 5: strategy transport maps (strategy-level)
  -- map_simplex k : stdSimplex ℝ (G.strategy (eI.symm k)) → stdSimplex ℝ (Fin (card' k))
  let map_simplex : (k : Fin n) → stdSimplex ℝ (G.strategy (eI.symm k)) →
      stdSimplex ℝ (Fin (card' k)) :=
    fun k x => ⟨fun j => x.val ((eS k).symm j), by
      refine ⟨fun j => x.property.1 _, ?_⟩
      rw [Equiv.sum_comp (eS k).symm]; exact x.property.2⟩
  -- map_simplex_inv k : stdSimplex ℝ (Fin (card' k)) → stdSimplex ℝ (G.strategy (eI.symm k))
  let map_simplex_inv : (k : Fin n) → stdSimplex ℝ (Fin (card' k)) →
      stdSimplex ℝ (G.strategy (eI.symm k)) :=
    fun k z => ⟨fun a => z.val (eS k a), by
      refine ⟨fun a => z.property.1 _, ?_⟩
      rw [Equiv.sum_comp (eS k)]; exact z.property.2⟩
  have map_simplex_left : ∀ k (x : stdSimplex ℝ (G.strategy (eI.symm k))),
      map_simplex_inv k (map_simplex k x) = x := by
    intro k x; ext a; simp [map_simplex, map_simplex_inv]
  have map_simplex_right : ∀ k (z : stdSimplex ℝ (Fin (card' k))),
      map_simplex k (map_simplex_inv k z) = z := by
    intro k z; ext j; simp [map_simplex, map_simplex_inv]
  -- Step 6: compose to get toProduct : MixedS G ↔ ProductSimplices card'
  let toProduct : MixedS G → ProductSimplices card' := fun σ k => map_simplex k (reindex σ k)
  let fromProduct : ProductSimplices card' → MixedS G :=
    fun w => reindex_inv (fun k => map_simplex_inv k (w k))
  have fromProduct_toProduct : ∀ σ, fromProduct (toProduct σ) = σ := by
    intro σ
    simp only [fromProduct, toProduct, map_simplex_left]
    exact reindex_left σ
  -- Step 7: transport nash_map G to ProductSimplices card'
  let f' : ProductSimplices card' → ProductSimplices card' := toProduct ∘ nash_map G ∘ fromProduct
  -- Step 8: continuity of toProduct
  have htoProduct_cont : Continuous toProduct := by
    apply continuous_pi; intro k
    apply Continuous.subtype_mk; apply continuous_pi; intro j
    -- (toProduct σ k).val j = (σ (eI.symm k)).val ((eS k).symm j)
    exact ((continuous_apply ((eS k).symm j)).comp continuous_subtype_val).comp
      (continuous_apply (eI.symm k))
  -- Step 9: continuity of fromProduct
  -- fromProduct = reindex_inv ∘ (fun w k => map_simplex_inv k (w k)).
  -- reindex_inv equals the Homeomorph.piCongrLeft eI.symm homeomorphism, which is continuous.
  -- The map w ↦ fun k => map_simplex_inv k (w k) is continuous by continuous_pi.
  have hfromProduct_cont : Continuous fromProduct := by
    have hreindex_inv_cont : Continuous reindex_inv := by
      have heq : reindex_inv = (Homeomorph.piCongrLeft (Y := fun i => stdSimplex ℝ (G.strategy i)) eI.symm) := by
        ext y i; simp [reindex_inv, Homeomorph.piCongrLeft]; rfl
      rw [heq]; exact (Homeomorph.piCongrLeft _).continuous
    have hmap_cont : Continuous (fun w : ProductSimplices card' => fun k => map_simplex_inv k (w k)) := by
      apply continuous_pi; intro k
      apply Continuous.subtype_mk; apply continuous_pi; intro a
      exact ((continuous_apply (eS k a)).comp continuous_subtype_val).comp (continuous_apply k)
    have : fromProduct = reindex_inv ∘ (fun w k => map_simplex_inv k (w k)) := rfl
    rw [this]; exact hreindex_inv_cont.comp hmap_cont
  have hf'_cont : Continuous f' :=
    htoProduct_cont.comp ((nash_map_cont G).comp hfromProduct_cont)
  -- Step 10: apply Brouwer_Product
  obtain ⟨w, hw⟩ := Brouwer_Product (card := card') f' hf'_cont
  -- Step 11: fromProduct w is a fixed point of nash_map G
  let σ : MixedS G := fromProduct w
  use σ
  have hfixed : nash_map G σ = σ := by
    -- f' w = w means toProduct (nash_map G (fromProduct w)) = w.
    -- Apply fromProduct: fromProduct (toProduct (nash_map G σ)) = fromProduct w = σ.
    -- By fromProduct_toProduct: fromProduct (toProduct (nash_map G σ)) = nash_map G σ.
    -- Hence nash_map G σ = σ.
    have h1 : toProduct (nash_map G σ) = w := hw
    have h2 : fromProduct (toProduct (nash_map G σ)) = nash_map G σ := fromProduct_toProduct (nash_map G σ)
    calc nash_map G σ = fromProduct (toProduct (nash_map G σ)) := h2.symm
      _ = fromProduct w := by rw [h1]
      _ = σ := rfl
  -- Step 12: the fixed point is a Nash equilibrium
  -- From hfixed: ∀ a, nash_map_aux G σ i a = (σ i).val a
  -- So g_function G i σ a / (∑_b g_function G i σ b) = (σ i).val a
  -- Summing: 1 = (∑_a g_function G i σ a) / (∑_b g_function G i σ b), so the denom = 1
  -- Then g_function G i σ a = (σ i).val a, so max 0 (EU(σ[i↦a]) - EU(σ)) = 0 for all pure a
  -- Then by linearity, no mixed deviation can improve either.
  intro i τ
  have hfixed_i : ∀ a : G.strategy i,
      g_function G i σ a / ∑ b : G.strategy i, g_function G i σ b = (σ i).val a := by
    intro a
    have := congr_fun (congr_arg (fun m => (m i).val) hfixed) a
    simp only [nash_map, nash_map_aux] at this
    exact this
  have hdenom_pos : 0 < ∑ b : G.strategy i, g_function G i σ b :=
    lt_of_lt_of_le one_pos (one_le_sum_g G i σ)
  have hdenom_ne : ∑ b : G.strategy i, g_function G i σ b ≠ 0 := ne_of_gt hdenom_pos
  have hsum_one : ∑ b : G.strategy i, g_function G i σ b = 1 := by
    -- From hfixed_i: g_function G i σ a = (σ i).val a * denom for all a
    -- Sum: denom = ∑_a g_function G i σ a = (∑_a (σ i).val a) * denom = 1 * denom = denom
    -- But we want denom = 1. Better: sum hfixed_i over all a:
    -- ∑_a (g_function G i σ a / denom) = ∑_a (σ i).val a = 1
    -- i.e., (∑_a g_function G i σ a) / denom = 1, so ∑_a g_function G i σ a = denom.
    -- That's circular. Instead: ∑_a (σ i).val a = 1, and (σ i).val a = g_f(a)/denom,
    -- so 1 = ∑_a g_f(a)/denom = (∑_a g_f(a))/denom, hence denom = ∑_a g_f(a).
    -- But denom IS ∑_a g_f(a) by definition! So this shows 1 = denom/denom = 1. Circular.
    -- The correct argument: from hfixed_i summed: ∑_a (g_f(a)/denom) = ∑_a (σ i).val a = 1.
    -- So denom ≠ 0 and ∑_a g_f(a) / denom = 1, meaning ∑_a g_f(a) = denom. And denom = ∑_a g_f(a).
    -- These are the same thing. So instead: from hfixed_i, g_f(a)/denom = (σ i).val a.
    -- Thus g_f(a) = (σ i).val a * denom for each a. Summing: denom = (∑_a (σ i).val a) * denom = 1 * denom.
    -- This just says denom = denom, still circular.
    -- The key insight: denom = ∑_a g_f(a), and from hfixed_i, g_f(a) = (σ i).val a * denom.
    -- So ∑_a g_f(a) = denom * ∑_a (σ i).val a = denom * 1 = denom. Same equation.
    -- Actually: hfixed_i gives g_f(a)/denom = (σ i).val a for each a.
    -- Multiply both sides by denom: g_f(a) = (σ i).val a * denom.
    -- So ∑_a (σ i).val a * denom = ∑_a g_f(a) = denom.
    -- Hence (∑_a (σ i).val a) * denom = denom, i.e., 1 * denom = denom. This IS trivial.
    -- The only non-trivial case would be if denom = 0, but we know denom > 0.
    -- So we need a different route: use the fact that ∑_a (σ i).val a = 1 AND
    -- (σ i).val a = g_f(a)/denom to conclude denom = 1.
    -- From hfixed_i: sum over a gives (∑_a g_f(a)) / denom = ∑_a (σ i).val a = 1.
    -- So denom / denom = 1, which gives denom = denom (already known).
    -- Wait: (∑_a g_f(a)) / denom = 1 means ∑_a g_f(a) = denom. But ∑_a g_f(a) IS denom by def.
    -- So this is indeed trivial/circular.
    -- ACTUAL PROOF: sum hfixed_i over a:
    -- ∑_a [g_f(a)/denom] = ∑_a [(σ i).val a]
    -- ⟹ (1/denom) * ∑_a g_f(a) = 1   (since ∑ (σ i).val a = 1)
    -- ⟹ (1/denom) * denom = 1
    -- ⟹ 1 = 1  -- trivial!
    -- We need: from (∑_a g_f(a)) / denom = 1 conclude denom = ∑_a g_f(a). But that's definitional.
    -- The only way to get denom = 1 is that ∑_a g_f(a) = 1 = denom.
    -- ∑_a g_f(a) = denom (by definition).
    -- From hfixed_i summed: ∑_a (g_f(a) / denom) = ∑_a (σ i).val a = 1.
    -- This is (∑_a g_f(a)) / denom = 1 (pull out denom), i.e., denom/denom = 1. True but useless.
    -- We need to show denom = 1, but from the fixed-point equation alone we cannot!?
    -- Wait: Let me re-read hfixed_i: g_f(a)/denom = (σ i).val a.
    -- Now, (σ i) is a probability distribution, so ∑_a (σ i).val a = 1.
    -- And g_f(a) = (σ i).val a * denom.
    -- Sum over a: ∑_a g_f(a) = (∑_a (σ i).val a) * denom = denom.
    -- So ∑_a g_f(a) = denom. But denom = ∑_a g_f(a) by definition. Tautology.
    -- We cannot derive denom = 1 from this alone!
    -- The real proof: we need a separate argument. From g_f(a) = (σ i).val a * denom ≥ 0
    -- and g_f(a) = (σ i).val a + max(0, EU_a - EU_σ) ≥ (σ i).val a,
    -- so max(0, EU_a - EU_σ) = (denom - 1) * (σ i).val a for each a.
    -- If denom > 1: then max(0, EU_a - EU_σ) > 0 for all a with (σ i).val a > 0.
    -- Then EU_a > EU_σ for all support strategies, meaning ∑_a (σ i).val a * EU_a > EU_σ.
    -- But ∑_a (σ i).val a * EU_a = EU_σ (expected utility = weighted sum of pure EU). Contradiction.
    -- This is the real proof, and it uses wsum_magic_ineq!
    -- Let me use wsum_magic_ineq properly.
    by_contra hne
    have hgt : 1 < ∑ b : G.strategy i, g_function G i σ b :=
      lt_of_le_of_ne (one_le_sum_g G i σ) (Ne.symm hne)
    -- From hfixed_i: (σ i).val a = g_f(a)/denom < g_f(a) since denom > 1
    -- So max(0, EU_a - EU_σ) > 0 for some a, i.e., EU_a > EU_σ for some pure strategy a
    -- with positive (σ i).val a.
    -- Key step: use σ i being a probability distribution and the above to derive contradiction.
    -- From g_f(a)/denom = (σ i).val a and denom > 1: g_f(a) = (σ i).val a * denom
    -- g_function G i σ a = (σ i).val a + max(0, EU_a - EU_σ)
    -- So max(0, EU_a - EU_σ) = (σ i).val a * (denom - 1) ≥ 0.
    -- Sum over a: ∑_a (σ i).val a * (denom - 1) = denom - 1 > 0.
    -- So not all max(0, EU_a - EU_σ) = 0.
    -- Then ∃ a with (σ i).val a > 0 and EU_a > EU_σ (from wsum_magic_ineq applied to σ i).
    -- Wait: more directly,
    -- EU_σ = ∑_a (σ i).val a * EU_a (linearity of evaluate_at_mixed in the i-th coordinate)
    -- If all EU_a ≤ EU_σ, then EU_σ = ∑ (σ i).val a * EU_a ≤ ∑ (σ i).val a * EU_σ = EU_σ. OK.
    -- Contradiction: wsum_magic_ineq gives ∃ a with (σ i).val a > 0 and EU_a ≤ EU_σ.
    -- We need the reverse: all EU_a ≤ EU_σ implies... hmm.
    -- Let me instead show: if ∑ g_f > 1, then ∑ (σ i).val a < 1. But (σ i) is a distribution!
    -- From hfixed_i: (σ i).val a = g_f(a)/denom. Sum: 1 = ∑_a (σ i).val a = (∑_a g_f(a))/denom.
    -- So ∑_a g_f(a) = denom. But denom = ∑_a g_f(a) by definition. Tautology again!
    -- So denom = ∑_a g_f(a) is always true, and ∑_a g_f(a) = denom, hence denom = denom. ALWAYS.
    -- This means our hne assumption gives 1 < denom = ∑ g_f, but also ∑ g_f = denom > 1.
    -- And from the sum of hfixed_i: ∑_a (σ i).val a = ∑_a g_f(a)/denom = denom/denom = 1. OK.
    -- So the sum argument gives NOTHING: it just confirms ∑ (σ i).val a = 1 regardless of denom.
    -- THE REAL PROOF uses: g_f(a) = (σ i).val a * denom ≥ (σ i).val a (since denom ≥ 1),
    -- with equality iff (σ i).val a = 0 or denom = 1.
    -- If denom > 1: g_f(a) > (σ i).val a for a with (σ i).val a > 0.
    -- But g_f(a) = (σ i).val a + max(0, EU_a - EU_σ).
    -- So max(0, EU_a - EU_σ) = g_f(a) - (σ i).val a = (σ i).val a * (denom - 1) > 0 for support a.
    -- Hence EU_a > EU_σ for all a in the support of σ i.
    -- But by evaluate_at_mixed_linear: EU_σ = ∑_a (σ i).val a * EU_a (where EU_a = EU(σ[i↦a]))
    -- Wait, EU_σ here is evaluate_at_mixed G i σ, not evaluate_at_mixed G i (update σ i (σ i)).
    -- Actually, update σ i (σ i) = σ (since σ i = σ i), so EU(σ[i↦σi]) = EU(σ). Circular.
    -- Use evaluate_at_mixed_linear: EU(σ[i↦τ]) = ∑_a τ(a) * EU(σ[i↦pure a]).
    -- Setting τ = σ i: EU(σ) = EU(σ[i↦σi]) = ∑_a (σ i)(a) * EU(σ[i↦pure a]).
    -- [since update σ i (σ i) = σ because (σ i) IS σ i]
    -- So EU_σ = ∑_a (σ i).val a * EU_a where EU_a = evaluate_at_mixed G i (update σ i (stdSimplex.pure a)).
    -- If all EU_a > EU_σ for support a, then EU_σ = ∑ (σ i).val a * EU_a > ∑ (σ i).val a * EU_σ = EU_σ. Contradiction!
    -- This is the correct approach. Let me implement it.
    have hupdate_self : update σ i (σ i) = σ := by
      funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    have hEU_linear : evaluate_at_mixed G i σ =
        ∑ a : G.strategy i, (σ i).val a *
          evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) := by
      nth_rw 1 [← hupdate_self]
      exact evaluate_at_mixed_linear G i σ (σ i)
    -- ∑_a (σ i).val a * EU_a = EU_σ
    -- where EU_a = evaluate_at_mixed G i (update σ i (stdSimplex.pure a))
    -- From the fixed-point: max(0, EU_a - EU_σ) = g_f(a) - (σ i).val a = (denom-1)*(σ i).val a
    have hmax_val : ∀ a : G.strategy i,
        max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) - evaluate_at_mixed G i σ) =
          (∑ b : G.strategy i, g_function G i σ b - 1) * (σ i).val a := by
      intro a
      have hg := hfixed_i a
      simp only [g_function] at hg
      -- hg : ((σ i).val a + max 0 (EU_a - EU_σ)) / denom = (σ i).val a
      -- Multiply both sides by denom to get the equation in non-division form:
      have hg2 : (σ i).val a + max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) -
          evaluate_at_mixed G i σ) = (σ i).val a * ∑ b : G.strategy i, g_function G i σ b := by
        have := div_eq_iff hdenom_ne |>.mp hg
        linarith
      linear_combination hg2 - (σ i).val a
    -- If ∑ g_f > 1, then (denom-1) > 0, so EU_a > EU_σ for all a with (σ i).val a > 0
    have hdiff_pos : 0 < ∑ b : G.strategy i, g_function G i σ b - 1 := by linarith
    -- For any a in the support: EU_a > EU_σ
    -- (max 0 (EU_a - EU_σ) > 0 implies EU_a > EU_σ)
    have hEU_gt : ∀ a : G.strategy i, 0 < (σ i).val a →
        evaluate_at_mixed G i σ <
          evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) := by
      intro a ha
      have hmv := hmax_val a
      have hval_pos : 0 < max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) -
          evaluate_at_mixed G i σ) := by
        rw [hmv]; exact mul_pos hdiff_pos ha
      -- 0 < max 0 x iff 0 < x
      have hpos := lt_of_lt_of_le hval_pos (le_max_right 0 _)
      -- hpos : max 0 (EU_a - EU_σ) ≤ EU_a - EU_σ is wrong. Let me use max_lt_iff
      -- Actually: 0 < max 0 (EU_a - EU_σ) and max 0 (EU_a - EU_σ) ≤ EU_a - EU_σ
      -- implies 0 < EU_a - EU_σ which gives EU_σ < EU_a.
      -- le_max_right 0 (EU_a - EU_σ) : EU_a - EU_σ ≤ max 0 (EU_a - EU_σ) -- WRONG direction
      -- le_max_right : a ≤ max a b means RIGHT arg. We need le_max_right 0 x : x ≤ max 0 x
      -- But we want max 0 x ≤ x when x > 0? No.
      -- Actually: max 0 x = x when x ≥ 0, and max 0 x = 0 when x ≤ 0.
      -- We have 0 < max 0 x. If x ≤ 0, then max 0 x = 0, contradicting > 0.
      -- So x > 0.
      rw [lt_max_iff] at hval_pos
      cases hval_pos with
      | inl h => exact absurd h (lt_irrefl 0)
      | inr h => linarith
    -- EU_σ = ∑_a (σ i).val a * EU_a > EU_σ. Contradiction.
    -- Find a₀ with (σ i).val a₀ > 0; then EU_a₀ > EU_σ, so the sum > EU_σ.
    obtain ⟨a₀, ha₀_pos, _⟩ := wsum_magic_ineq (p := σ i) (f := fun _ => (1:ℝ)) (c := 1)
        (by simp only [mul_one]; exact (σ i).property.2)
    -- Now EU_a₀ > EU_σ (since a₀ is in the support)
    have hEU_a₀ := hEU_gt a₀ ha₀_pos
    -- And EU_σ = ∑ a, (σ i).val a * EU_a ≥ (σ i).val a₀ * EU_a₀ > (σ i).val a₀ * EU_σ
    -- but actually EU_σ = ∑ a, (σ i).val a * EU_a, and one term (σ i).val a₀ * EU_a₀ > (σ i).val a₀ * EU_σ.
    -- Use: ∑ a, (σ i).val a * EU_a ≥ (σ i).val a₀ * EU_a₀ > (σ i).val a₀ * EU_σ = EU_σ * (σ i).val a₀.
    -- And ∑ a, (σ i).val a * EU_σ = EU_σ.
    -- Therefore EU_σ = ∑ EU_a * val a > EU_σ * val a₀ + ∑_{a ≠ a₀} EU_a * val a ≥ ... hard.
    -- Simpler: show ∑ a, (σ i).val a * EU_σ < ∑ a, (σ i).val a * EU_a by sum_lt_sum.
    have hEU_contradiction : ∑ a : G.strategy i, (σ i).val a * evaluate_at_mixed G i σ <
        ∑ a : G.strategy i, (σ i).val a *
          evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) := by
      apply Finset.sum_lt_sum
      · intro a _
        by_cases ha : (σ i).val a = 0
        · simp [ha]
        · have ha_pos : 0 < (σ i).val a :=
            lt_of_le_of_ne ((σ i).property.1 a) (Ne.symm ha)
          exact mul_le_mul_of_nonneg_left (hEU_gt a ha_pos).le ((σ i).property.1 a)
      · exact ⟨a₀, Finset.mem_univ _,
          mul_lt_mul_of_pos_left hEU_a₀ ha₀_pos⟩
    -- But ∑ a, (σ i).val a * EU_σ = EU_σ (since ∑ val = 1), and ∑ (val a * EU_a) = EU_σ.
    have hlhs : ∑ a : G.strategy i, (σ i).val a * evaluate_at_mixed G i σ =
        evaluate_at_mixed G i σ := by
      rw [← Finset.sum_mul, (σ i).property.2, one_mul]
    linarith [hEU_linear ▸ hlhs ▸ hEU_contradiction]
  have hg_eq_σ : ∀ a : G.strategy i, g_function G i σ a = (σ i).val a := by
    intro a
    have := hfixed_i a
    rw [hsum_one, div_one] at this
    exact this
  have hno_pure_improvement : ∀ a : G.strategy i,
      evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) ≤ evaluate_at_mixed G i σ := by
    intro a
    have hg := hg_eq_σ a
    simp only [g_function] at hg
    -- hg : (σ i).val a + max 0 (EU_a - EU_σ) = (σ i).val a
    -- So max 0 (EU_a - EU_σ) = 0, hence EU_a - EU_σ ≤ 0.
    have hmax0 : max 0 (evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) -
        evaluate_at_mixed G i σ) = 0 := by linarith
    linarith [max_eq_left_iff.mp hmax0]
  rw [evaluate_at_mixed_linear]
  calc ∑ a : G.strategy i, τ.val a * evaluate_at_mixed G i (update σ i (stdSimplex.pure a))
      ≤ ∑ a : G.strategy i, τ.val a * evaluate_at_mixed G i σ :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hno_pure_improvement a) (τ.property.1 a)
    _ = evaluate_at_mixed G i σ := by
        rw [← Finset.sum_mul, τ.property.2, one_mul]

end StrategicGame

end
