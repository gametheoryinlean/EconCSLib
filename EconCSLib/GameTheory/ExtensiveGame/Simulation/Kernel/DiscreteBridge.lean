/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge

/-!
# Kernel.DiscreteBridge — supplied discrete-to-analytic path-law bridge

The finite discrete executor computes `FiniteLaw` prefixes. A complete path
measure is supplied separately. This module records equality with an analytic
kernel presentation only from an explicit realization certificate; it no
longer constructs a second Ionescu--Tulcea path measure on behalf of callers.
-/

open MeasureTheory ProbabilityTheory

namespace Arena

variable {A : Arena} {start : A.State}

local instance historyMeasurableSpace :
    MeasurableSpace (A.HistoryFrom start) :=
  ⊤

/-- A supplied discrete complete-history path measure agrees with the analytic
history-kernel presentation exactly when the caller provides that full
path-measure realization certificate. -/
theorem pathLaw_eq_historyKernelArena_toMeasurable_pathMeasure
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    [MeasurableKernelArena.ActionPolicy.PathExecution
      policy.toKernelPolicy.toMeasurable
      (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet]
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (realizes :
      (supplied : Measure (ℕ → A.HistoryFrom start)) =
        policy.toKernelPolicy.toMeasurable.pathMeasure
          (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
          current) :
    Arena.pathLaw policy current supplied =
      policy.toKernelPolicy.toMeasurable.pathMeasure
        (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
        current :=
  realizes

end Arena
