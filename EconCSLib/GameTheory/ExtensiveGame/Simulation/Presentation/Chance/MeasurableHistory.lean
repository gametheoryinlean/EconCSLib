/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge

/-!
# Presentation.Chance.MeasurableHistory — measurable complete-history models

The representation-neutral `ObservedGame` interface deliberately puts no
measurable spaces on histories or dependent legal actions.  This module
records exactly the measurable data needed to regard its complete-history
unfolding as a `MeasurableKernelArena`.

A `MeasurableHistoryModel` supplies measurable spaces on

```lean
HistoryFrom init
Σ history : HistoryFrom init, Action history.1
```

together with measurability of projection, deterministic history append, and
the terminal set.  Its transition kernel is required pointwise to be the
Dirac history-append law.  Measurable singletons are recorded
because the joint event-policy compiler uses them to express legality.

The structure is an explicit certificate, not an automatic measurable-space
inference principle.  In particular, it can carry standard-Borel structures
on uncountable history and action spaces when the model author proves the
dependent append map measurable.

`MeasurableHistoryModel.discrete` recovers the established top-measurable
`KernelArena.toMeasurable` lift exactly.  It is useful for compatibility, but
on an uncountable carrier its top measurable space is not advertised as a
standard-Borel presentation.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- Complete histories of an observed game. -/
abbrev CompleteHistory (G : ObservedGame N U) :=
  G.base.toArena.HistoryFrom G.base.init

/-- The total dependent carrier of complete histories and legal actions. -/
abbrev HistoryActionBundle (G : ObservedGame N U) :=
  Σ history : CompleteHistory G,
    G.base.Action history.1

/-- Append one legal action to a complete history. -/
def appendHistory
    (G : ObservedGame N U)
    (historyAction : HistoryActionBundle G) :
    CompleteHistory G :=
  ⟨G.base.next historyAction.1.1 historyAction.2,
    historyAction.1.2.snoc historyAction.2⟩

/-- Explicit measurable semantics for the deterministic complete-history
unfolding of an observed game.

The pointwise transition equation prevents the certificate from silently
changing the game's dynamics while allowing the measurable structures to be
chosen independently of the discrete top-space embedding. -/
structure MeasurableHistoryModel
    (G : ObservedGame N U) where
  /-- Measurable space on complete histories. -/
  historyMeasurable : MeasurableSpace (CompleteHistory G)
  /-- Measurable space on the dependent history/action bundle. -/
  historyActionMeasurable :
    MeasurableSpace (HistoryActionBundle G)
  /-- Forgetting a legal action is measurable. -/
  stateProjection_measurable :
    @Measurable
      (HistoryActionBundle G) (CompleteHistory G)
      historyActionMeasurable historyMeasurable
      Sigma.fst
  /-- Deterministic history append is measurable. -/
  appendHistory_measurable :
    @Measurable
      (HistoryActionBundle G) (CompleteHistory G)
      historyActionMeasurable historyMeasurable
      (appendHistory G)
  /-- Measurable deterministic transition kernel. -/
  transition :
    @Kernel
      (HistoryActionBundle G) (CompleteHistory G)
      historyActionMeasurable historyMeasurable
  /-- The transition is normalized. -/
  transition_isMarkov :
    @IsMarkovKernel
      (HistoryActionBundle G) (CompleteHistory G)
      historyActionMeasurable historyMeasurable transition
  /-- The transition is exactly deterministic history append. -/
  transition_apply :
    ∀ historyAction,
      transition historyAction =
        @Measure.dirac
          (CompleteHistory G) historyMeasurable
          (appendHistory G historyAction)
  /-- The set of complete histories with no legal action is measurable. -/
  terminalSet_measurable :
    @MeasurableSet
      (CompleteHistory G) historyMeasurable
      {history | G.base.isTerminal history.1}
  /-- Complete-history singletons are measurable. -/
  singleton_measurable :
    ∀ history : CompleteHistory G,
      @MeasurableSet
        (CompleteHistory G) historyMeasurable
        ({history} : Set (CompleteHistory G))

namespace MeasurableHistoryModel

variable {G : ObservedGame N U}

/-- The measurable kernel arena represented by an explicit complete-history
model. -/
def toArena
    (model : MeasurableHistoryModel G) :
    MeasurableKernelArena where
  State := CompleteHistory G
  Action := fun history => G.base.Action history.1
  stateMeasurable := model.historyMeasurable
  actionBundleMeasurable := model.historyActionMeasurable
  stateProjection_measurable := model.stateProjection_measurable
  transition := model.transition
  transition_isMarkov := model.transition_isMarkov

/-- The represented arena has measurable state singletons. -/
instance instMeasurableSingletonClass
    (model : MeasurableHistoryModel G) :
    MeasurableSingletonClass model.toArena.State where
  measurableSet_singleton :=
    model.singleton_measurable

/-- The represented arena's terminal set is measurable. -/
theorem toArena_terminalSet_measurable
    (model : MeasurableHistoryModel G) :
    MeasurableSet model.toArena.terminalSet :=
  model.terminalSet_measurable

/-- The represented successor measure is exactly the Dirac measure of one
deterministic history append. -/
@[simp]
theorem toArena_nextMeasure
    (model : MeasurableHistoryModel G)
    (history : model.toArena.State)
    (action : model.toArena.Action history) :
    model.toArena.nextMeasure history action =
      @Measure.dirac
        (CompleteHistory G) model.historyMeasurable
        (appendHistory G ⟨history, action⟩) :=
  model.transition_apply ⟨history, action⟩

/-- The established discrete top-space lift, packaged as an explicit
measurable history model.

No countability premise is needed for this compatibility model.  It does not
solve the uncountable realization problem: products of uncountable discrete
measurable spaces need not themselves be discrete. -/
noncomputable def discrete
    (G : ObservedGame N U) :
    MeasurableHistoryModel G := by
  let arena :=
    (G.base.toArena.historyKernelArena
      G.base.init).toMeasurable
  exact
    { historyMeasurable := arena.stateMeasurable
      historyActionMeasurable := arena.actionBundleMeasurable
      stateProjection_measurable :=
        arena.stateProjection_measurable
      appendHistory_measurable := by
        change
          @Measurable
            (HistoryActionBundle G) (CompleteHistory G)
            ⊤ ⊤ (appendHistory G)
        intro measurableSet _hmeasurableSet
        exact MeasurableSpace.measurableSet_top
      transition := arena.transition
      transition_isMarkov := arena.transition_isMarkov
      transition_apply := by
        intro historyAction
        dsimp only [arena, KernelArena.toMeasurable]
        change
          (((G.base.toArena.historyKernelArena G.base.init).next
            historyAction.1 historyAction.2).atoms.foldr
              (fun atom rest =>
                (atom.2 : ENNReal) •
                  @Measure.dirac (CompleteHistory G) ⊤ atom.1 + rest)
              0) = _
        rw [Arena.historyKernelArena_next, FiniteLaw.pure_atoms]
        simp only [List.foldr_cons, List.foldr_nil]
        change
          (((1 : ℚ≥0) : NNReal) : ENNReal) •
              @Measure.dirac (CompleteHistory G) ⊤
                (appendHistory G historyAction) + 0 =
            @Measure.dirac (CompleteHistory G) ⊤
              (appendHistory G historyAction)
        simp
      terminalSet_measurable := by
        change
          @MeasurableSet
            (CompleteHistory G) ⊤
            {history | G.base.isTerminal history.1}
        exact MeasurableSpace.measurableSet_top
      singleton_measurable := by
        intro history
        change
          @MeasurableSet
            (CompleteHistory G) ⊤
            ({history} : Set (CompleteHistory G))
        exact MeasurableSpace.measurableSet_top }

/-- The arena underlying the compatibility model is definitionally the
existing discrete-to-analytic complete-history lift. -/
theorem discrete_toArena
    (G : ObservedGame N U) :
    (discrete G).toArena =
      (G.base.toArena.historyKernelArena
        G.base.init).toMeasurable := by
  rfl

end MeasurableHistoryModel

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- Compatibility spelling for complete histories of an observed chance
game. -/
abbrev CompleteHistory (G : ObservedChanceGame N U) :=
  ObservedGame.CompleteHistory G.observed

/-- Compatibility spelling for the dependent history/action bundle. -/
abbrev HistoryActionBundle (G : ObservedChanceGame N U) :=
  ObservedGame.HistoryActionBundle G.observed

/-- Compatibility spelling for deterministic history append. -/
abbrev appendHistory (G : ObservedChanceGame N U) :=
  ObservedGame.appendHistory G.observed

/-- Compatibility spelling for the structural measurable-history model.

The model depends only on `G.observed`; the chance finite law is deliberately absent
from its definition. -/
abbrev MeasurableHistoryModel (G : ObservedChanceGame N U) :=
  ObservedGame.MeasurableHistoryModel G.observed

namespace MeasurableHistoryModel

/-- Compatibility constructor for the established discrete measurable
history model. -/
noncomputable abbrev discrete
    (G : ObservedChanceGame N U) :
    MeasurableHistoryModel G :=
  ObservedGame.MeasurableHistoryModel.discrete G.observed

/-- The compatibility constructor represents exactly the established
discrete complete-history arena. -/
theorem discrete_toArena
    (G : ObservedChanceGame N U) :
    (discrete G).toArena =
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable :=
  ObservedGame.MeasurableHistoryModel.discrete_toArena G.observed

end MeasurableHistoryModel

end ExtensiveGame.ObservedChanceGame
