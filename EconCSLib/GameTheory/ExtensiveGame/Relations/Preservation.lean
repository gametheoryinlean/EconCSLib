/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism

/-!
# Formal preservation-certificate vocabulary

This module is the Lean counterpart of `docs/design/efg-preservation-matrix.md`.
It gives one canonical pre-stability namespace for the relation strengths
used by EFG compilers and semantic bridges. Most entries are aliases of the
authoritative relation structures; the aliases do not add stronger
preservation claims.

Strict compiler packages carry a payoff-free observed-game isomorphism and an
external root-correspondence proof. Weak compiler packages instead carry a
progressing weak simulation, which is the appropriate contract for
stuttering, macro/micro serialization, and endpoint-forgetting.

`PathLawCoupling` is deliberately law-level: it stores a joint measure, both
marginals, and almost-sure support on a relation. It does not imply a strict
state or strategy isomorphism.
-/

open MeasureTheory

namespace ExtensiveGame.Preservation

universe uN uA uS uO uI uP uStrategy uα uβ

/-- Directional payoff-free structural homomorphism. -/
abbrev StructuralHom {N : Type uN} :=
  ControlledObservedGame.Hom (N := N)

/-- Strict payoff-free observed-game isomorphism. -/
abbrev StrictIso {N : Type uN} :=
  ControlledObservedGame.Iso (N := N)

/-- Strict observed-game isomorphism with an orthogonal payoff square. -/
abbrev PayoffCompatibleIso {N : Type uN} {U : Type*} :=
  ObservedGame.PayoffCompatibleIso (N := N) (U := U)

/-- Directional payoff-free information refinement. -/
abbrev InformationRefinement {N : Type uN} :=
  ControlledObservedGame.InformationRefinement (N := N)

/-- One-step relational simulation of arenas. -/
abbrev Simulation := Arena.Simulation

/-- Two-way one-step relational simulation of arenas. -/
abbrev Bisimulation := Arena.Bisimulation

/-- Stuttering/macro-step relational simulation of arenas. -/
abbrev WeakSimulation := Arena.WeakSimulation

/-- Two-way stuttering/macro-step relational simulation of arenas. -/
abbrev WeakBisimulation := Arena.WeakBisimulation

/-- One-way complete-path-law realization with playerwise strategy maps. -/
abbrev CompletePathLawRealization
    {N : Type uN}
    (G : ControlledObservedGame N)
    [MeasurableSpace G.base.History]
    (S T : G.CompletePathLawSemantics) :=
  S.CompletePathLawRealization T

/-- Functional complete-path-law realization across different payoff-free EFG
representations. -/
abbrev CrossGameCompletePathLawRealization
    {N : Type uN}
    (G H : ControlledObservedGame N)
    [MeasurableSpace G.base.History]
    [MeasurableSpace H.base.History]
    (S : G.CompletePathLawSemantics)
    (T : H.CompletePathLawSemantics) :=
  ControlledObservedGame.CrossGameCompletePathLawRealization S T

/-- One-way bounded complete-history-law realization with playerwise
strategy maps and exact occurrence-sensitive finite-law equality. -/
abbrev CompleteHistoryLawRealization
    {N : Type uN}
    (G : DiscreteControlledObservedChanceGame N)
    (S T : G.BoundedHistoryLawFamily) :=
  S.CompleteHistoryLawRealization T

/-- A coupling of two path laws supported almost surely on a relation.

The marginal equalities are stored explicitly; support alone never licenses
an equality-of-laws claim. -/
structure PathLawCoupling
    {α : Type uα} {β : Type uβ}
    [MeasurableSpace α] [MeasurableSpace β]
    (source : Measure α) (target : Measure β)
    (Rel : α → β → Prop) where
  /-- Joint law on paired source/target paths. -/
  joint : Measure (α × β)
  /-- The source marginal is a probability measure. -/
  source_isProbability : IsProbabilityMeasure source
  /-- The target marginal is a probability measure. -/
  target_isProbability : IsProbabilityMeasure target
  /-- The joint coupling itself is a probability measure. -/
  joint_isProbability : IsProbabilityMeasure joint
  /-- The joint law has the source law as first marginal. -/
  fst_marginal :
    joint.map Prod.fst = source
  /-- The joint law has the target law as second marginal. -/
  snd_marginal :
    joint.map Prod.snd = target
  /-- The coupling relation holds outside a joint null set. -/
  supported :
    ∀ᵐ pair ∂joint, Rel pair.1 pair.2

/-- Compiler package for a genuinely strict payoff-free representation
change, including exact correspondence of its separately chosen roots. -/
structure StrictCompilerPreservation
    {N : Type uN}
    (G H :
      ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) where
  /-- Strict structural representation equivalence. -/
  structural : G.Iso H
  /-- Exact correspondence of externally chosen roots. -/
  roots :
    structural.PreservesRootPresentations
      sourceRoots targetRoots

/-- Compiler package for a serialization or abstraction whose visible source
step may require a nonempty finite target trace. -/
structure WeakCompilerPreservation
    (source target : Arena)
    (sourceInit : source.State)
    (targetInit : target.State) where
  /-- Weak step-matching relation. -/
  simulation : source.WeakSimulation target
  /-- Initial states are related. -/
  initial : simulation.Rel sourceInit targetInit
  /-- Each visible source step makes target progress. -/
  progressing : simulation.Progressing

end ExtensiveGame.Preservation
