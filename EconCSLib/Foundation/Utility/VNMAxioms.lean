/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.Foundation.Preference

/-!
# EconCSLib.Foundation.Utility.VNMAxioms

The four axioms for expected utility theory, stated as predicates on a
preference relation over lotteries.

## Main definitions

* `VNM.Completeness` — every pair of lotteries is comparable
* `VNM.Transitivity` — preference is transitive
* `VNM.Independence` — mixing with a common lottery preserves preference
* `VNM.Continuity` — intermediate mixtures exist [MSZ Axiom 2.12]
* `strict`, `indiff` — shared derived strict preference and indifference

## Main results

* `VNM.continuity_independent` — ∃ preference violating only Continuity [MSZ Ex 2.5]
* `VNM.completeness_independent` — ∃ preference violating only Completeness
* `VNM.transitivity_independent` — ∃ preference violating only Transitivity
* `VNM.independence_independent` — ∃ preference violating only Independence

## References

* [MSZ] Chapter 2, Axioms 2.12–2.17, Exercise 2.5
-/

open Finset BigOperators

namespace VNM

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {O : Type*} [Fintype O]

/-! ### Lottery-specific axioms

`strict`, `indiff`, `Completeness`, `Transitivity` are defined in
`Foundation.Preference` for general binary relations. Here we add the two
lottery-specific axioms that reference `Lottery.mix`. -/

/-- **Independence**: mixing both sides with a common lottery preserves preference.
    `L₁ ≿ L₂ ↔ [α L₁, (1-α) N] ≿ [α L₂, (1-α) N]` for `α > 0`. -/
def Independence (pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop) : Prop :=
  ∀ (L₁ L₂ N : Lottery 𝕜 O) (α : 𝕜) (hα₀ : 0 < α) (hα₁ : α ≤ 1),
    pref L₁ L₂ ↔ pref (Lottery.mix α (le_of_lt hα₀) hα₁ L₁ N)
                       (Lottery.mix α (le_of_lt hα₀) hα₁ L₂ N)

/-- **Continuity** (Archimedean / MSZ Axiom 2.12): for `L₁ ≿ L₂ ≿ L₃`,
    there exists `θ ∈ [0,1]` such that `L₂ ∼ [θ L₁, (1-θ) L₃]`. -/
def Continuity (pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop) : Prop :=
  ∀ (L₁ L₂ L₃ : Lottery 𝕜 O),
    pref L₁ L₂ → pref L₂ L₃ →
    ∃ (θ : 𝕜) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1),
      indiff pref L₂ (Lottery.mix θ hθ₀ hθ₁ L₁ L₃)

/-! ### Consequences of the axioms -/

/-- **The Sure-Thing Principle** [MSZ Ex 2.12]: The common lottery in a mixture
    does not affect strict preference. If Independence holds, then
    `[α L₁, (1-α) L₃] ≻ [α L₂, (1-α) L₃]` iff `[α L₁, (1-α) L₄] ≻ [α L₂, (1-α) L₄]`
    for any lotteries `L₁, L₂, L₃, L₄` and `α ∈ [0,1]`. -/
theorem sure_thing_principle
    {pref : Lottery 𝕜 O → Lottery 𝕜 O → Prop}
    (hind : Independence pref)
    (L₁ L₂ L₃ L₄ : Lottery 𝕜 O)
    (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    strict pref (Lottery.mix α hα₀ hα₁ L₁ L₃) (Lottery.mix α hα₀ hα₁ L₂ L₃) ↔
    strict pref (Lottery.mix α hα₀ hα₁ L₁ L₄) (Lottery.mix α hα₀ hα₁ L₂ L₄) := by
  rcases eq_or_lt_of_le hα₀ with rfl | hα_pos
  · -- α = 0: both mixes collapse to L₃ (resp. L₄); strict X X is false
    have h₃ : Lottery.mix 0 hα₀ hα₁ L₁ L₃ = Lottery.mix 0 hα₀ hα₁ L₂ L₃ :=
      Subtype.ext (funext fun i => by simp [Lottery.mix, stdSimplex.mix])
    have h₄ : Lottery.mix 0 hα₀ hα₁ L₁ L₄ = Lottery.mix 0 hα₀ hα₁ L₂ L₄ :=
      Subtype.ext (funext fun i => by simp [Lottery.mix, stdSimplex.mix])
    simp only [strict, h₃, h₄, and_not_self_iff]
  · -- α > 0: Independence factors out the common lottery
    constructor <;> intro ⟨h₁, h₂⟩ <;> [
      exact ⟨(hind L₁ L₂ L₄ α hα_pos hα₁).mp ((hind L₁ L₂ L₃ α hα_pos hα₁).mpr h₁),
             fun h => h₂ ((hind L₂ L₁ L₃ α hα_pos hα₁).mp ((hind L₂ L₁ L₄ α hα_pos hα₁).mpr h))⟩;
      exact ⟨(hind L₁ L₂ L₃ α hα_pos hα₁).mp ((hind L₁ L₂ L₄ α hα_pos hα₁).mpr h₁),
             fun h => h₂ ((hind L₂ L₁ L₄ α hα_pos hα₁).mp ((hind L₂ L₁ L₃ α hα_pos hα₁).mpr h))⟩
    ]

end VNM

/-! ## Exercise 2.5: Independence of the vNM Axioms [MSZ Ex 2.5]

For each axiom, we construct a preference relation on `Lottery ℚ (Fin 3)` that
violates that axiom while satisfying the other three.
-/

open VNM

/-! ### Counterexample 1: ¬Completeness

Use the trivial preference `L₁ ≿ L₂ ↔ L₁ = L₂`. Only identical lotteries are
comparable, so completeness fails. The other three axioms hold trivially or by
injectivity of mixing. -/

namespace VNM.NotComplete

private def pref (L₁ L₂ : Lottery ℚ (Fin 3)) : Prop := L₁ = L₂

private theorem not_complete : ¬ Completeness pref := by
  intro h
  have := h (Lottery.pure (𝕜 := ℚ) (0 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (1 : Fin 3))
  simp only [pref] at this
  rcases this with h | h <;> {
    have := congr_arg (fun L => L.val (0 : Fin 3)) h
    simp [Lottery.pure] at this
  }

private theorem transitive : Transitivity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  exact h₁₂.trans h₂₃

private theorem independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  constructor
  · intro h; simp only [pref] at h; subst h; rfl
  · intro h
    simp only [pref] at h
    have hval : L₁.val = L₂.val := funext fun i => by
      have := congr_arg (fun L => L.val i) h
      simp only [Lottery.mix, stdSimplex.mix] at this
      -- this : α * L₁.val i + (1 - α) * N.val i = α * L₂.val i + (1 - α) * N.val i
      -- or a disjunction if simp simplified differently
      nlinarith
    exact Subtype.ext hval

private theorem continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at h₁₂ h₂₃
  subst h₁₂; subst h₂₃
  refine ⟨(1 : ℚ), by norm_num, le_refl 1, ?_⟩
  constructor <;> {
    simp only [pref]
    ext i
    simp [Lottery.mix, stdSimplex.mix]
  }

theorem completeness_independent :
    ∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_complete, transitive, independent, continuous⟩

end VNM.NotComplete

/-! ### Counterexample 2: ¬Continuity

Lexicographic preference on probability vectors: compare `L(0)` first, then `L(1)`.
This is a total order satisfying independence, but no mixture of pure outcomes
`A₀` and `A₂` is indifferent to pure `A₁`. -/

namespace VNM.NotContinuous

private def pref (L₁ L₂ : Lottery ℚ (Fin 3)) : Prop :=
  L₁.val 0 > L₂.val 0 ∨ (L₁.val 0 = L₂.val 0 ∧ L₁.val 1 ≥ L₂.val 1)

private theorem complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  rcases lt_trichotomy (L₁.val 0) (L₂.val 0) with h | h | h
  · right; left; exact h
  · rcases le_total (L₂.val 1) (L₁.val 1) with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

private theorem transitive : Transitivity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at *
  rcases h₁₂ with h | ⟨heq₁, hge₁⟩ <;> rcases h₂₃ with h' | ⟨heq₂, hge₂⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

private theorem independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  simp only [pref, Lottery.mix, stdSimplex.mix]
  constructor
  · intro h
    rcases h with h | ⟨heq, hge⟩
    · left; nlinarith
    · right; constructor <;> nlinarith
  · intro h
    rcases h with h | ⟨heq, hge⟩
    · left; nlinarith
    · right; constructor <;> nlinarith

private theorem not_continuous : ¬ Continuity pref := by
  intro h
  -- Use pure outcomes: A₀ ≿ A₁ ≿ A₂ in lex order
  have h12 : pref (Lottery.pure (𝕜 := ℚ) (0 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)) := by
    simp only [pref, Lottery.pure]; left; decide
  have h23 : pref (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)) (Lottery.pure (𝕜 := ℚ) (2 : Fin 3)) := by
    simp only [pref, Lottery.pure]; right; constructor <;> decide
  obtain ⟨θ, hθ₀, hθ₁, hfwd, hbwd⟩ := h _ _ _ h12 h23
  -- mix θ (pure 0) (pure 2) has val 0 = θ, val 1 = 0
  -- pure 1 has val 0 = 0, val 1 = 1
  -- hbwd : pref (mix θ _ _ (pure 0) (pure 2)) (pure 1)
  --       = (θ > 0 ∨ (θ = 0 ∧ 0 ≥ 1))
  -- mix θ (pure 0) (pure 2) has val 0 = θ, val 1 = 0
  -- pure 1 has val 0 = 0, val 1 = 1
  have mix0 : (Lottery.mix θ hθ₀ hθ₁ (Lottery.pure (𝕜 := ℚ) (0 : Fin 3))
    (Lottery.pure (2 : Fin 3))).val (0 : Fin 3) = θ := by
    simp [Lottery.mix, stdSimplex.mix, Lottery.pure]
  have mix1 : (Lottery.mix θ hθ₀ hθ₁ (Lottery.pure (𝕜 := ℚ) (0 : Fin 3))
    (Lottery.pure (2 : Fin 3))).val (1 : Fin 3) = 0 := by
    simp [Lottery.mix, stdSimplex.mix, Lottery.pure]
  have p1_0 : (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)).val (0 : Fin 3) = 0 := by
    simp [Lottery.pure]
  have p1_1 : (Lottery.pure (𝕜 := ℚ) (1 : Fin 3)).val (1 : Fin 3) = 1 := by
    simp [Lottery.pure]
  simp only [pref, mix0, mix1, p1_0, p1_1] at hfwd hbwd
  -- hbwd : θ > 0 ∨ (θ = 0 ∧ 0 ≥ 1)
  -- hfwd : 0 > θ ∨ (0 = θ ∧ 1 ≥ 0)
  rcases hbwd with h | ⟨h₁, h₂⟩
  · rcases hfwd with h' | ⟨h', _⟩ <;> linarith
  · linarith

theorem continuity_independent :
    ∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧
      Transitivity pref ∧ Independence pref :=
  ⟨pref, not_continuous, complete, transitive, independent⟩

end VNM.NotContinuous

/-! ### Counterexample 3: ¬Transitivity

Define `L₁ ≿ L₂` iff `L₁(0) ≥ L₂(0)` OR `L₁(1) ≥ L₂(1)`. This is complete
(for any pair, at least one coordinate comparison holds) and satisfies independence
(linear mixing preserves each coordinate comparison). But it is NOT transitive:
the "or" allows preference chains that don't compose. -/

namespace VNM.NotTransitive

private def pref (L₁ L₂ : Lottery ℚ (Fin 3)) : Prop :=
  L₁.val 0 ≥ L₂.val 0 ∨ L₁.val 1 ≥ L₂.val 1

private theorem complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  -- Either L₁(0) ≥ L₂(0) or L₂(0) ≥ L₁(0); the first gives left-left, the second gives right-left
  rcases le_total (L₂.val 0) (L₁.val 0) with h | h
  · left; left; exact h
  · right; left; exact h

private theorem not_transitive : ¬ Transitivity pref := by
  intro h
  -- Construct three lotteries witnessing intransitivity:
  -- L₁ = (0.4, 0.1, 0.5), L₂ = (0.3, 0.3, 0.4), L₃ = (0.5, 0.2, 0.3)
  -- pref L₁ L₂ via component 0: 0.4 ≥ 0.3
  -- pref L₂ L₃ via component 1: 0.3 ≥ 0.2
  -- ¬pref L₁ L₃: 0.4 < 0.5 and 0.1 < 0.2
  let L₁ : Lottery ℚ (Fin 3) := ⟨![2/5, 1/10, 1/2], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₂ : Lottery ℚ (Fin 3) := ⟨![3/10, 3/10, 2/5], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₃ : Lottery ℚ (Fin 3) := ⟨![1/2, 1/5, 3/10], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  have h12 : pref L₁ L₂ := by left; show (2 : ℚ)/5 ≥ 3/10; norm_num
  have h23 : pref L₂ L₃ := by right; show (3 : ℚ)/10 ≥ 1/5; norm_num
  have h13 := h L₁ L₂ L₃ h12 h23
  rcases h13 with h0 | h1
  · exact absurd h0 (by show ¬((2 : ℚ)/5 ≥ 1/2); norm_num)
  · exact absurd h1 (by show ¬((1 : ℚ)/10 ≥ 1/5); norm_num)

private theorem independent : Independence pref := by
  intro L₁ L₂ N α hα₀ hα₁
  simp only [pref, Lottery.mix, stdSimplex.mix]
  constructor
  · intro h; rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  · intro h; rcases h with h | h
    · left; nlinarith
    · right; nlinarith

private theorem continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  -- Try θ=0 (mix = L₃): works if pref L₃ L₂
  by_cases h₃₂ : pref L₃ L₂
  · refine ⟨0, le_refl 0, by norm_num, ?_⟩
    exact ⟨by simp only [pref, Lottery.mix, stdSimplex.mix] at h₂₃ ⊢; rcases h₂₃ with h | h <;> [left; right] <;> nlinarith,
           by simp only [pref, Lottery.mix, stdSimplex.mix] at h₃₂ ⊢; rcases h₃₂ with h | h <;> [left; right] <;> nlinarith⟩
  -- Try θ=1 (mix = L₁): works if pref L₂ L₁
  · by_cases h₂₁ : pref L₂ L₁
    · refine ⟨1, by norm_num, le_refl 1, ?_⟩
      exact ⟨by simp only [pref, Lottery.mix, stdSimplex.mix] at h₂₁ ⊢; rcases h₂₁ with h | h <;> [left; right] <;> nlinarith,
             by simp only [pref, Lottery.mix, stdSimplex.mix] at h₁₂ ⊢; rcases h₁₂ with h | h <;> [left; right] <;> nlinarith⟩
    · -- Neither endpoint works ⟹ L₁ strictly dominates L₂ strictly dominates L₃ on both coords
      simp only [pref] at h₃₂ h₂₁
      push_neg at h₃₂ h₂₁
      obtain ⟨h₃₂_0, h₃₂_1⟩ := h₃₂
      obtain ⟨h₂₁_0, h₂₁_1⟩ := h₂₁
      -- Match component 0: θ = (L₂(0) - L₃(0)) / (L₁(0) - L₃(0))
      have hden_pos : L₁.val 0 - L₃.val 0 > 0 := by linarith
      have hnum_pos : L₂.val 0 - L₃.val 0 > 0 := by linarith
      have hnum_lt : L₂.val 0 - L₃.val 0 < L₁.val 0 - L₃.val 0 := by linarith
      set θ := (L₂.val 0 - L₃.val 0) / (L₁.val 0 - L₃.val 0)
      refine ⟨θ, le_of_lt (div_pos hnum_pos hden_pos),
              le_of_lt (by rwa [div_lt_one hden_pos]), ?_⟩
      -- At this θ, mix.val 0 = L₂.val 0 (by construction)
      have hmix0 : θ * L₁.val 0 + (1 - θ) * L₃.val 0 = L₂.val 0 := by
        have hne : L₁.val 0 - L₃.val 0 ≠ 0 := ne_of_gt hden_pos
        simp only [θ]; field_simp; ring
      simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
      exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩

theorem transitivity_independent :
    ∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_transitive, complete, independent, continuous⟩

end VNM.NotTransitive

/-! ### Counterexample 4: ¬Independence

Use a threshold preference: `L₁ ≿ L₂` iff `L₁(0) ≥ 1/2` or `L₂(0) < 1/2`.
This partitions lotteries into "high" (L(0) ≥ 1/2) and "low" (L(0) < 1/2);
high is preferred to low, and within each class everything is indifferent.
Mixing can move a lottery across the threshold, violating independence.
Continuity holds because θ=0 or θ=1 always gives indifference. -/

namespace VNM.NotIndependent

private def pref (L₁ L₂ : Lottery ℚ (Fin 3)) : Prop :=
  L₁.val 0 ≥ 1/2 ∨ L₂.val 0 < 1/2

private theorem complete : Completeness pref := by
  intro L₁ L₂
  simp only [pref]
  rcases le_or_gt (1/2 : ℚ) (L₁.val 0) with h | h
  · left; left; exact h
  · right; right; exact h

private theorem transitive : Transitivity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  simp only [pref] at *
  rcases h₁₂ with h | h
  · left; exact h
  · -- L₂.val 0 < 1/2, so from h₂₃: L₂.val 0 ≥ 1/2 (contradiction) or L₃.val 0 < 1/2
    rcases h₂₃ with h' | h'
    · linarith
    · right; exact h'

private theorem not_independent : ¬ Independence pref := by
  intro h
  -- L₁ = (2/5, 3/5, 0): L₁(0) = 2/5 < 1/2 (low)
  -- L₂ = (3/5, 2/5, 0): L₂(0) = 3/5 ≥ 1/2 (high)
  -- ¬pref L₁ L₂: 2/5 < 1/2 and 3/5 ≥ 1/2
  -- N = (4/5, 1/5, 0): N(0) = 4/5
  -- mix 1/2 L₁ N: val 0 = 3/5 ≥ 1/2 → pref (mix L₁ N) anything
  -- So pref (mix L₁ N) (mix L₂ N) but ¬pref L₁ L₂. Independence fails.
  let L₁ : Lottery ℚ (Fin 3) := ⟨![2/5, 3/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let L₂ : Lottery ℚ (Fin 3) := ⟨![3/5, 2/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  let N : Lottery ℚ (Fin 3) := ⟨![4/5, 1/5, 0], by
    refine ⟨fun i => by fin_cases i <;> simp (config := { decide := true }) [*] <;> (try norm_num), ?_⟩
    simp [Fin.sum_univ_three]; ring⟩
  have h_not : ¬ pref L₁ L₂ := by
    simp only [pref]; push_neg; constructor <;> native_decide
  have h_mix : pref (Lottery.mix (1/2) (by norm_num) (by norm_num) L₁ N)
                     (Lottery.mix (1/2) (by norm_num) (by norm_num) L₂ N) := by
    simp only [pref, Lottery.mix, stdSimplex.mix]; left; native_decide
  exact h_not ((h L₁ L₂ N (1/2) (by norm_num) (by norm_num)).mpr h_mix)

private theorem continuous : Continuity pref := by
  intro L₁ L₂ L₃ h₁₂ h₂₃
  rcases le_or_gt (1/2 : ℚ) (L₂.val 0) with h₂_high | h₂_low
  · -- L₂ is "high" (L₂(0) ≥ 1/2). Use θ=1: mix = L₁.
    -- From pref L₁ L₂ with L₂ high: L₁ must also be high.
    have h₁_high : L₁.val 0 ≥ 1/2 := by
      simp only [pref] at h₁₂; rcases h₁₂ with h | h <;> linarith
    refine ⟨1, by norm_num, le_refl 1, ?_⟩
    simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
    exact ⟨Or.inl (by nlinarith), Or.inl (by nlinarith)⟩
  · -- L₂ is "low" (L₂(0) < 1/2). Use θ=0: mix = L₃.
    -- From pref L₂ L₃ with L₂ low: L₃ must also be low.
    have h₃_low : L₃.val 0 < 1/2 := by
      simp only [pref] at h₂₃; rcases h₂₃ with h | h <;> linarith
    refine ⟨0, le_refl 0, by norm_num, ?_⟩
    simp only [indiff, pref, Lottery.mix, stdSimplex.mix]
    exact ⟨Or.inr (by nlinarith), Or.inr (by nlinarith)⟩

theorem independence_independent :
    ∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧
      Transitivity pref ∧ Continuity pref :=
  ⟨pref, not_independent, complete, transitive, continuous⟩

end VNM.NotIndependent

/-! ### Main theorem -/

/-- **Exercise 2.5 [MSZ]**: The four vNM axioms are independent. For each axiom,
    there exists a preference relation on lotteries that violates that axiom while
    satisfying the other three. -/
theorem VNM.axioms_independent :
    -- ¬Complete
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref) ∧
    -- ¬Transitive
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧ Independence pref ∧ Continuity pref) ∧
    -- ¬Independent
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧ Transitivity pref ∧ Continuity pref) ∧
    -- ¬Continuous
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧ Transitivity pref ∧ Independence pref) :=
  ⟨NotComplete.completeness_independent,
   NotTransitive.transitivity_independent,
   NotIndependent.independence_independent,
   NotContinuous.continuity_independent⟩
