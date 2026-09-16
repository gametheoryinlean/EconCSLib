/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning
import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite
import EconCSLib.GameTheory.ExtensiveGame.Winning.Chance

/-!
# Stochastic logical winning

Opt-in facade combining logical winning conditions with the canonical
measure-valued discrete infinite-history executor. It exposes
`AEWinningUnder` for arbitrary measures and reserves
`IsAlmostSurelyWinningUnder` for laws carrying an `IsProbabilityMeasure`
certificate. It preserves the distinct probability-free pathwise and
profile-based winning semantics from `Interface.Winning`.

This facade does not import the non-atomic measurable-kernel arena. An
analytic almost-sure winning layer requires a measurable objective on the
analytic state/event path space.
-/
