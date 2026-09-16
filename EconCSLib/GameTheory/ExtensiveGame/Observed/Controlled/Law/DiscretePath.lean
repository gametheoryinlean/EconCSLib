/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law

/-!
# Supplied discrete complete-path probability semantics

Finite behavioral execution remains executable through `FiniteLaw`. A complete
infinite-path probability measure and its bounded measure-valued marginals are
caller-supplied data. Exact marginal and legality equations are required
explicitly; this adapter performs no hidden Ionescu--Tulcea construction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

namespace ExtensiveGame.DiscreteControlledObservedChanceGame

variable {N : Type*}
  (G : DiscreteControlledObservedChanceGame N)

/-- Project a caller-supplied complete behavioral path probability measure. -/
def behavioralPathLaw
    [MeasurableSpace G.observed.base.History]
    (_profile : G.BehavioralProfile)
    (_current : G.observed.base.History)
    (supplied : ProbabilityMeasure
      (ℕ → G.observed.base.History)) :
    Measure (ℕ → G.observed.base.History) :=
  supplied

/-- Package supplied complete-path and bounded-marginal data as the common
lawful probability interface.

The two marginal certificates record, respectively, agreement with executable
`FiniteLaw` prefixes and agreement with the supplied complete path law. -/
def behavioralCompletePathLawSemantics
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace G.observed.base.History]
    (pathLaws :
      G.BehavioralProfile → G.observed.base.History →
        ProbabilityMeasure (ℕ → G.observed.base.History))
    (boundedLaws :
      G.BehavioralProfile → G.observed.base.History → ℕ →
        Measure G.observed.base.History)
    (bounded_eq_finite :
      ∀ profile current time,
        boundedLaws profile current time =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (BehavioralProfile.toHistoryPolicy G profile)
              current time))
    (path_finiteMarginal :
      ∀ profile current time,
        ((pathLaws profile current :
            ProbabilityMeasure (ℕ → G.observed.base.History)) :
          Measure (ℕ → G.observed.base.History)).map
            (fun path => path time) =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (BehavioralProfile.toHistoryPolicy G profile)
              current time))
    (lawful :
      ∀ (profile : G.BehavioralProfile)
        (current : G.observed.base.History),
        ∀ᵐ path ∂((pathLaws profile current :
            ProbabilityMeasure (ℕ → G.observed.base.History)) :
              Measure (ℕ → G.observed.base.History)),
          G.observed.base.toArena.IsCompletePlayPathFrom current path) :
    G.observed.CompletePathLawSemantics where
  Strategy := G.BehavioralStrategy
  pathLaw := fun profile current =>
    G.behavioralPathLaw profile current (pathLaws profile current)
  pathLaw_isProbability := by
    intro profile current
    change IsProbabilityMeasure
      (pathLaws profile current :
        Measure (ℕ → G.observed.base.History))
    infer_instance
  pathLaw_ae_legal := lawful
  boundedCompleteHistoryLaw := boundedLaws
  boundedCompleteHistoryLaw_eq_map := by
    intro profile current time
    rw [bounded_eq_finite, ← path_finiteMarginal]
    rfl

/-- The supplied discrete semantic carrier realizes its supplied complete path
law definitionally. -/
theorem behavioralCompletePathLawSemantics_realizesExecution
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [MeasurableSpace G.observed.base.History]
    (pathLaws :
      G.BehavioralProfile → G.observed.base.History →
        ProbabilityMeasure (ℕ → G.observed.base.History))
    (boundedLaws :
      G.BehavioralProfile → G.observed.base.History → ℕ →
        Measure G.observed.base.History)
    (bounded_eq_finite :
      ∀ profile current time,
        boundedLaws profile current time =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (BehavioralProfile.toHistoryPolicy G profile)
              current time))
    (path_finiteMarginal :
      ∀ profile current time,
        ((pathLaws profile current :
            ProbabilityMeasure (ℕ → G.observed.base.History)) :
          Measure (ℕ → G.observed.base.History)).map
            (fun path => path time) =
          finiteLawMeasure(
            G.observed.base.toArena.stochasticHistoryLawFrom
              (BehavioralProfile.toHistoryPolicy G profile)
              current time))
    (lawful :
      ∀ (profile : G.BehavioralProfile)
        (current : G.observed.base.History),
        ∀ᵐ path ∂((pathLaws profile current :
            ProbabilityMeasure (ℕ → G.observed.base.History)) :
              Measure (ℕ → G.observed.base.History)),
          G.observed.base.toArena.IsCompletePlayPathFrom current path) :
    (G.behavioralCompletePathLawSemantics
      pathLaws boundedLaws bounded_eq_finite
      path_finiteMarginal lawful).RealizesExecution
        (fun profile current =>
          G.behavioralPathLaw profile current
            (pathLaws profile current)) := by
  intro _profile _current
  rfl

end ExtensiveGame.DiscreteControlledObservedChanceGame
