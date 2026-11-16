/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning.Stochastic

/-!
# Stochastic logical-winning import boundary

The stochastic winning facade combines complete-play winning conditions with
the discrete measure-valued infinite history law. The non-atomic analytic
kernel arena remains a separate opt-in path.
-/

#check Arena.WinningConditionFrom.AEWinningUnder
#check Arena.WinningConditionFrom.IsAlmostSurelyWinningUnder
#check Arena.StochasticHistoryPolicy.IsAlmostSurelyWinning
#check Arena.pathLaw_ae_isCompletePlayPathFrom

namespace ArbitraryMeasureBoundary

open MeasureTheory

variable {A : Arena} {start : A.State}
  {current : A.HistoryFrom start} {N : Type*}
  [MeasurableSpace (A.HistoryFrom start)]

/-- The arbitrary-measure predicate is intentionally vacuous under the zero
measure; this is why the probability-certified predicate has a separate
name and typeclass premise. -/
example (W : A.WinningConditionFrom current N) (i : N) :
    W.AEWinningUnder
      (0 : Measure (ℕ → A.HistoryFrom start)) i := by
  simp [Arena.WinningConditionFrom.AEWinningUnder]

end ArbitraryMeasureBoundary

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
