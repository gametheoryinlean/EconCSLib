/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

/-!
# Supplied infinite execution for observed behavioral games

This adapter indexes a caller-supplied complete-history path law by an observed
behavioral profile. The bounded behavioral executor remains `FiniteLaw`-valued,
and finite-marginal agreement is an explicit certificate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

namespace ExtensiveGame.ObservedChanceGame.BehavioralProfile

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- Project a caller-supplied complete path probability measure for an observed
behavioral profile. -/
def pathLaw
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (supplied : ProbabilityMeasure
      (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init)) :
    Measure
      (ℕ →
        G.observed.base.toArena.HistoryFrom G.observed.base.init) :=
  Arena.pathLaw (toHistoryPolicy G profile) current supplied

/-- The supplied behavioral path law starts at the indexed complete history
when its finite-marginal certificate says so. -/
theorem pathLaw_initial
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (supplied : ProbabilityMeasure
      (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure
          (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init)).map
            (fun path => path time) =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (toHistoryPolicy G profile) current time)) :
    (pathLaw G profile current supplied).map (fun path => path 0) =
      Measure.dirac current :=
  Arena.pathLaw_initial
    (toHistoryPolicy G profile) current supplied finiteMarginal

/-- At every event time, a supplied behavioral path law agrees with the
bounded behavioral finite-law executor when the caller supplies the exact
marginal certificate. -/
theorem pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (supplied : ProbabilityMeasure
      (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure
          (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init)).map
            (fun path => path time) =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (toHistoryPolicy G profile) current time))
    (time : ℕ) :
    (pathLaw G profile current supplied).map (fun path => path time) =
      finiteLawMeasure(
        G.observed.base.toArena.stochasticHistoryLawFrom
          (toHistoryPolicy G profile) current time) :=
  Arena.pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    (toHistoryPolicy G profile) current supplied finiteMarginal time

/-- Behavioral almost-sure termination under a caller-supplied complete path
law. -/
abbrev AETerminates
    [MeasurableSpace
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (supplied : ProbabilityMeasure
      (ℕ → G.observed.base.toArena.HistoryFrom G.observed.base.init)) : Prop :=
  Arena.AETerminates (toHistoryPolicy G profile) current supplied

end ExtensiveGame.ObservedChanceGame.BehavioralProfile
