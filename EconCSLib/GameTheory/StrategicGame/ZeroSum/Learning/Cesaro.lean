/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.FictitiousPlay

/-!
# EconCSLib.GameTheory.StrategicGame.ZeroSum.Learning.Cesaro

The realised cumulative payoff along a matrix-game play sequence. The
knowledge blueprint records the Cesàro convergence target and its proof route.
-/

open Finset BigOperators Filter

set_option linter.unusedSectionVars false

namespace MatrixGame

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]

/-- **Realised cumulative payoff** along a play sequence on `A`. -/
noncomputable def realisedCumPayoff (A : MatrixGame I J ℝ) (iSeq : ℕ → I)
    (jSeq : ℕ → J) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range n, A.g (iSeq p) (jSeq p)

end MatrixGame
