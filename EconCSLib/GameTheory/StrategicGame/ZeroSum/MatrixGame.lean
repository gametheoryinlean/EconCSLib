/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Simplex
import EconCSLib.GameTheory.StrategicGame.ZeroSum.Basic
import EconCSLib.Math.Minimax.Loomis

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.MatrixGame

Von Neumann's Minimax Theorem for finite two-player zero-sum games.

## Main definitions

* `ZerosumGame` — a matrix game `g : I → J → ℝ`
* `maximin` — player I's maximin value: `max_x min_j E(x, j)`
* `minimax` — player II's minimax value: `min_y max_i E(i, y)`
* `HasMixedValue` — the game has a value in mixed strategies

## Main results

* `maximin_le_minimax` — maximin ≤ minimax (always)
* `minimax_theorem` — maximin = minimax for finite games [von Neumann 1928]
* `minimax_optimal_strategies` — existence of optimal mixed strategies

## Proof method

This module exposes the real-valued Loomis route. The reusable ordered-field
minimax theorem is available in `EconCSLib.Math.Minimax.Minimax`.

## Attribution

Ported from `GameTheory/Zerosum.lean` in
[math-xmum/gametheory](https://github.com/math-xmum/gametheory)
by Ma Jia-Jun, HXZ, yuxuan, and Lazyfill.

## References

* [MSZ] Theorem 5.11 (von Neumann's Minimax Theorem)
* [LRS] Laraki, Renault, Sorin, Theorem 2.3.1
-/

open Finset BigOperators Matrix

/-! ### Matrix game -/

/-- A finite two-player zero-sum matrix game.
    Player I chooses row `i : I`, Player II chooses column `j : J`.
    Payoff to Player I is `g i j` (in the scalar field `𝕜`); payoff to
    Player II is `-g i j`.

    The scalar field `𝕜` defaults to `ℚ` so that unannotated `MatrixGame I J`
    means a rational matrix game — keeping the data structure Bourbaki-minimal
    and forcing the choice of `ℝ` (or any other ordered field) to be explicit
    at the use site. -/
structure MatrixGame (I J : Type*) (𝕜 : Type := ℚ) where
  /-- The payoff matrix. -/
  g : I → J → 𝕜

namespace MatrixGame

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-! ### Expected payoff under mixed strategies

These bilinear-payoff and guarantee definitions are purely arithmetic +
order; they go through over any linearly ordered field. Order-completeness
(needed for `maximin` / `minimax` below) is **not** required here. -/

section LayerTwo
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable (A : MatrixGame I J 𝕜)

/-- Expected payoff when Player I uses mixed strategy `x` against pure column `j`. -/
noncomputable def payoffAgainstColumn (x : stdSimplex 𝕜 I) (j : J) : 𝕜 :=
  x ⬝ᵥ fun i => A.g i j

/-- Expected payoff when pure row `i` faces Player II's mixed strategy `y`. -/
noncomputable def payoffAgainstRow (i : I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  y ⬝ᵥ A.g i

/-- Expected payoff when Player I uses mixed strategy `x` and Player II uses `y`. -/
noncomputable def expectedPayoff (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  x ⬝ᵥ fun i => A.payoffAgainstRow i y

/-- Expected payoff when Player I uses mixed strategy `x` and Player II uses `y`. -/
noncomputable def E (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  A.expectedPayoff x y

/-- Expected payoff when Player I uses `x` against pure column `j`. -/
noncomputable def Ej (x : stdSimplex 𝕜 I) (j : J) : 𝕜 :=
  A.payoffAgainstColumn x j

/-- Expected payoff when pure row `i` faces Player II's mixed strategy `y`. -/
noncomputable def Ei (i : I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  A.payoffAgainstRow i y

/-! ### Pure-row / pure-column guarantees -/

/-- Player I's guaranteed payoff using mixed strategy `x`:
    the minimum expected payoff over all of Player II's pure responses.

    A finite `Finset.inf'` over `J`, so only `[LinearOrder 𝕜]` is needed —
    no order completeness. -/
noncomputable def guarantee_I (x : stdSimplex 𝕜 I) : 𝕜 :=
  Finset.inf' univ Finset.univ_nonempty (fun j => A.Ej x j)

/-- Player II's guaranteed loss using mixed strategy `y`:
    the maximum expected payoff (for Player I) over all of Player I's pure responses. -/
noncomputable def guarantee_II (y : stdSimplex 𝕜 J) : 𝕜 :=
  Finset.sup' univ Finset.univ_nonempty (fun i => A.Ei i y)

/-! ### Value predicates (field-generic)

`IsMaximin`, `IsMinimax`, `IsValue` express the value of a matrix game
without committing to any specific witness construction. They are
inequality predicates only, so they live at the Layer-2 hypothesis level
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]` — usable over `ℚ`,
`ℝ`, any ordered field, even when `sSup`-based `maximin` / `minimax`
below are unavailable. -/

/-- `v` is a **maximin value** of `A`: some row strategy guarantees at
least `v` (existence), and no strictly larger value is achievable
(maximality). -/
def IsMaximin (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  (∃ x : stdSimplex 𝕜 I, ∀ j, v ≤ A.Ej x j) ∧
  (∀ w, (∃ x : stdSimplex 𝕜 I, ∀ j, w ≤ A.Ej x j) → w ≤ v)

/-- `v` is a **minimax value** of `A`: some column strategy caps player I's
payoff at `v` (existence), and no strictly smaller cap is achievable
(minimality). -/
def IsMinimax (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  (∃ y : stdSimplex 𝕜 J, ∀ i, A.Ei i y ≤ v) ∧
  (∀ w, (∃ y : stdSimplex 𝕜 J, ∀ i, A.Ei i y ≤ w) → v ≤ w)

/-- `v` is **the value** of `A` (saddle-point form): there exist a row
mixed strategy `x` and column mixed strategy `y` such that `x` guarantees
at least `v` against every column and `y` caps player I's payoff at `v`
against every row. Field-generic; `MatrixGame.value` below is the
ℝ-valued specialisation (via `iSup`) when `𝕜` admits order completeness. -/
def IsValue (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  ∃ x : stdSimplex 𝕜 I, ∃ y : stdSimplex 𝕜 J,
    (∀ j, v ≤ A.Ej x j) ∧ (∀ i, A.Ei i y ≤ v)

end LayerTwo

/-! ### Maximin and minimax values via `iSup` / `iInf`

`maximin` and `minimax` use `iSup` / `iInf` over the (uncountable)
mixed-strategy simplex, so they need order completeness in addition to
the Layer-2 hypotheses. We require
`[ConditionallyCompleteLinearOrder 𝕜]` — satisfied by ℝ via
`Real.instConditionallyCompleteLinearOrder`, but not by ℚ.

For an ordered field without order completeness (e.g. ℚ), use the
field-generic `IsMaximin` / `IsMinimax` / `IsValue` predicates above
instead — they characterise the same notion without invoking `sSup`. -/

section LayerThreeSup
variable {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable (A : MatrixGame I J 𝕜)

/-- The maximin value: the best guarantee Player I can achieve.
    `maximin = sup_x inf_j E(x, j)` -/
noncomputable def maximin : 𝕜 :=
  iSup (fun x => A.guarantee_I x)

/-- The minimax value: the best guarantee Player II can achieve.
    `minimax = inf_y sup_i E(i, y)` -/
noncomputable def minimax : 𝕜 :=
  iInf (fun y => A.guarantee_II y)

end LayerThreeSup

/-! ### Loomis-route theorems (ℝ-only)

These theorems carry the actual content of the von Neumann minimax
theorem and are proved by aliasing the simplified-Loomis development in
[`MinimaxLoomis`](MinimaxLoomis.lean). The Loomis proof uses ℝ-specific
compactness / continuity, so the theorems are pinned to ℝ even though
their statements (via `maximin` / `minimax` above) make sense over any
order-complete linearly ordered field. -/

section LayerThree
variable (A : MatrixGame I J ℝ)

/-- Maximin ≤ minimax (always holds, for any matrix game).
    This is the finite weak-duality inequality. -/
theorem maximin_le_minimax : A.maximin ≤ A.minimax :=
  MinimaxLoomis.lam0_le_mu0 A.g

/-- **Von Neumann's Minimax Theorem**: For any finite matrix game,
    maximin = minimax. [MSZ 5.11, von Neumann 1928]

    Proof: the general (positive-`B`) Loomis theorem specialised to `B = 𝟙`,
    exported as [`Loomis.minmax_from_general`] (compactness + continuity
    + strong induction on `|I| + |J|`).

    The field-generic minimax (any linearly ordered field, not just ℝ) is
    proved separately by von Neumann symmetrisation in
    [`Minimax.minimax`] — no compactness, no order completeness. -/
theorem minimax_theorem : A.maximin = A.minimax :=
  Loomis.minmax_from_general A.g

/-- Existence of optimal mixed strategies: there exist mixed strategies
    `xx` for Player I and `yy` for Player II and a value `v` such that:
    - Player I guarantees at least `v`: `∀ j, E(xx, j) ≥ v`
    - Player II limits payoff to at most `v`: `∀ i, E(i, yy) ≤ v`

    [MSZ Theorem 5.11, LRS Theorem 2.3.1] -/
theorem minimax_optimal_strategies :
    ∃ (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J) (v : ℝ),
      (∀ j : J, A.Ej xx j ≥ v) ∧
      (∀ i : I, A.Ei i yy ≤ v) := by
  obtain ⟨xx, Hxx⟩ := MinimaxLoomis.exists_xx_lam0 A.g
  obtain ⟨yy, Hyy⟩ := MinimaxLoomis.exists_yy_mu0 A.g
  refine ⟨xx, yy, MinimaxLoomis.lam0 A.g, ?_, ?_⟩
  · -- ∀ j, Ej xx j ≥ lam0 A.g
    intro j
    -- A.Ej xx j = wsum xx (fun i => A.g i j) by unfolding payoffAgainstColumn.
    have : A.Ej xx j = wsum xx (fun i => A.g i j) := rfl
    rw [this]; exact Hxx j
  · -- ∀ i, Ei i yy ≤ lam0 A.g  (using lam0 = mu0)
    intro i
    have : A.Ei i yy = wsum yy (fun j => A.g i j) := rfl
    rw [this, Loomis.minmax_from_general A.g]
    exact Hyy i

end LayerThree

end MatrixGame
