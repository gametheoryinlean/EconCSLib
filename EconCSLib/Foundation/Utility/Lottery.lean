/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Simplex
import Mathlib.Tactic.Positivity

/-!
# EconCSLib.Foundation.Utility.Lottery

Lotteries (probability distributions over finite outcome sets) and their
algebraic properties. A lottery is an element of `stdSimplex 𝕜 O` — a
non-negative function summing to 1.

This module provides game-theory-specific vocabulary on top of Mathlib's
`stdSimplex`, including convex combinations (compound lotteries) and
expected value.

## Main definitions

* `Lottery` — type alias for `stdSimplex 𝕜 O`
* `Lottery.pure` — degenerate lottery (certain outcome)
* `Lottery.mix` — convex combination of two lotteries (compound lottery simplification)
* `Lottery.expectedValue` — expected value: `∑ o, p(o) · f(o)`

## Main results

* `mix_mem` — convex combination of lotteries is a lottery
* `expectedValue_mix` — linearity: `E[mix] = α·E[L₁] + (1-α)·E[L₂]` [MSZ Axiom 2.16]
* `expectedValue_pure` — expected value of a pure lottery is the outcome value

## References

* [MSZ] Chapter 2, Definitions 2.9–2.11, Axioms 2.12–2.17
-/

open Finset BigOperators

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

set_option linter.unusedSectionVars false

/-! ### Lottery type -/

/-- A lottery over outcomes `O`: a probability distribution.
    Just `stdSimplex 𝕜 O` with a game-theoretic name. -/
abbrev Lottery (𝕜 : Type*) (O : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype O] :=
  stdSimplex 𝕜 O

/-! ### Constructors

Lottery is a thin domain-flavored shell over `stdSimplex`. The constructors
below are definitional aliases of the Core operations:

* `Lottery.pure := stdSimplex.pure`
* `Lottery.mix  := stdSimplex.mix`

so existing call sites and KB references continue resolving unchanged. -/

/-- A pure (degenerate) lottery: outcome `o₀` with probability 1.
    Alias of `stdSimplex.pure`. -/
abbrev Lottery.pure {O : Type*} [Fintype O] [DecidableEq O] (o₀ : O) :
    Lottery 𝕜 O :=
  stdSimplex.pure o₀

/-- Convex combination of two lotteries: the compound lottery `[α(L₁), (1-α)(L₂)]`
    after simplification. [MSZ Axiom 2.16]

    Alias of `stdSimplex.mix`: `mix α L₁ L₂ = α · L₁ + (1-α) · L₂` pointwise. -/
abbrev Lottery.mix {O : Type*} [Fintype O]
    (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (L₁ L₂ : Lottery 𝕜 O) : Lottery 𝕜 O :=
  stdSimplex.mix α hα₀ hα₁ L₁ L₂

/-! ### Expected value -/

/-- Expected value of `f` under lottery `L`:
    `E_L[f] = ∑ o, L(o) · f(o)`.

    Alias of `wsum` from `Math.Simplex`. -/
abbrev Lottery.expectedValue {O : Type*} [Fintype O]
    (L : Lottery 𝕜 O) (f : O → 𝕜) : 𝕜 :=
  wsum L f

/-! ### Properties

All four properties below are thin wrappers around the simplex lemmas
(`wsum_pure_apply`, `wsum_mix`, `wsum_le_wsum`, `wsum_const`). -/

section Properties
variable {O : Type*} [Fintype O]

/-- Expected value of a pure lottery equals the outcome value. -/
theorem Lottery.expectedValue_pure [DecidableEq O] (o₀ : O) (f : O → 𝕜) :
    Lottery.expectedValue (Lottery.pure (𝕜 := 𝕜) o₀) f = f o₀ :=
  wsum_pure_apply o₀ f

/-- **Linearity of expected value** under convex combination.
    `E[mix α L₁ L₂] = α · E[L₁] + (1-α) · E[L₂]`

    This is the key property corresponding to [MSZ Axiom 2.16]
    (simplification of compound lotteries). -/
theorem Lottery.expectedValue_mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (L₁ L₂ : Lottery 𝕜 O) (f : O → 𝕜) :
    Lottery.expectedValue (Lottery.mix α hα₀ hα₁ L₁ L₂) f =
    α * Lottery.expectedValue L₁ f + (1 - α) * Lottery.expectedValue L₂ f :=
  wsum_mix α hα₀ hα₁ L₁ L₂ f

/-- Expected value is monotone: if `f ≤ g` pointwise, then `E[f] ≤ E[g]`. -/
theorem Lottery.expectedValue_mono {L : Lottery 𝕜 O} {f g : O → 𝕜}
    (h : ∀ o, f o ≤ g o) :
    Lottery.expectedValue L f ≤ Lottery.expectedValue L g :=
  wsum_le_wsum L h

/-- Expected value of a constant is the constant. -/
theorem Lottery.expectedValue_const (L : Lottery 𝕜 O) (c : 𝕜) :
    Lottery.expectedValue L (fun _ => c) = c :=
  wsum_const L c

end Properties

/-! ### Linear utility -/

/-- A utility function `u` is linear (in the vNM sense) if it respects
    compound lottery simplification:
    `u([α(L₁), (1-α)(L₂)]) = α · u(L₁) + (1-α) · u(L₂)`.

    Equivalently, `u(L) = E_L[u ∘ outcome]` for some function on outcomes.
    [MSZ Definition 2.10] -/
def IsLinearUtility {O : Type*} [Fintype O]
    (u : Lottery 𝕜 O → 𝕜) : Prop :=
  ∀ (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (L₁ L₂ : Lottery 𝕜 O),
    u (Lottery.mix α hα₀ hα₁ L₁ L₂) = α * u L₁ + (1 - α) * u L₂

/-- Expected value (with respect to a fixed payoff function) is a linear utility. -/
theorem expectedValue_isLinearUtility {O : Type*} [Fintype O] (f : O → 𝕜) :
    IsLinearUtility (𝕜 := 𝕜) (fun L => Lottery.expectedValue L f) := by
  intro α hα₀ hα₁ L₁ L₂
  exact Lottery.expectedValue_mix α hα₀ hα₁ L₁ L₂ f
