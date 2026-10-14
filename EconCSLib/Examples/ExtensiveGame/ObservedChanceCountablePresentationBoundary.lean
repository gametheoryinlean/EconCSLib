/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.ObservedChanceKernelBridgeBoundary
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable

/-!
# Effective countable observed-chance presentation regression

This regression supplies actual history/action encodings and exercises the
executable terminal/player tag selector on the absent-minded three-rung game.
The analytic presentation is an explicit parameter: countability alone is not
an algorithm for producing measurable kernels. Its existing certification
theorems still preserve recurring information and the exact stopped-history
law, without a second presentation constructor.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceCountablePresentationBoundary

open Examples.AbsentMinded
open Examples.ObservedChanceKernelBridgeBoundary
open ExtensiveGame
open MeasurableKernelArena

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

/-- The unique complete history ending at the terminal rung. -/
def lastHistory :
    base.toArena.HistoryFrom base.init :=
  ⟨Rung.s2, secondDecision.2.snoc ()⟩

/-- Every complete history of the three-rung game is one of its three
prefixes. -/
theorem history_classify
    (history : base.toArena.HistoryFrom base.init) :
    history = firstDecision ∨
      history = secondDecision ∨
      history = lastHistory := by
  rcases history with ⟨state, path⟩
  refine Arena.History.rec
    (motive := fun state path =>
      (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
          firstDecision ∨
        (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
            secondDecision ∨
        (⟨state, path⟩ : base.toArena.HistoryFrom base.init) =
          lastHistory)
    ?_ ?_ path
  · exact Or.inl rfl
  · intro state path action ih
    rcases ih with hfirst | hsecond | hlast
    · cases hfirst
      cases action
      exact Or.inr (Or.inl rfl)
    · cases hsecond
      cases action
      exact Or.inr (Or.inr rfl)
    · cases hlast
      exact PEmpty.elim action

/-- An executable enumeration of the three complete histories. -/
def historyCover :
    Fin 3 → base.toArena.HistoryFrom base.init
  | 0 => firstDecision
  | 1 => secondDecision
  | 2 => lastHistory

theorem historyCover_surjective :
    Function.Surjective historyCover := by
  intro history
  rcases history_classify history with hfirst | hsecond | hlast
  · exact ⟨0, hfirst.symm⟩
  · exact ⟨1, hsecond.symm⟩
  · exact ⟨2, hlast.symm⟩

/-- A concrete encoder and partial decoder, not an encoding selected from a
countability proof. -/
instance baseHistoryEncoding :
    Encodable (base.toArena.HistoryFrom base.init) where
  encode history := match history.1 with
    | .s0 => 0
    | .s1 => 1
    | .s2 => 2
  decode
    | 0 => some firstDecision
    | 1 => some secondDecision
    | 2 => some lastHistory
    | _ => none
  encodek history := by
    rcases history_classify history with hfirst | hsecond | hlast
    · subst history; rfl
    · subst history; rfl
    · subst history; rfl

instance gameHistoryEncoding :
    Encodable
      (game.observed.base.toArena.HistoryFrom
        game.observed.base.init) := by
  change Encodable (base.toArena.HistoryFrom base.init)
  infer_instance

instance gameLocalActionEncoding
    (history :
      game.observed.base.toArena.HistoryFrom
        game.observed.base.init) :
    Encodable (game.observed.base.Action history.1) := by
  change Encodable (rungAction history.1)
  cases history.1 <;> simp only [rungAction] <;> infer_instance

private def informationTag :
    ObservedChanceGame.CountableInformation game → Nat
  | .terminal => 0
  | .player _ => 1
  | .chance _ _ => 2

/-- Native execution sees the two recurring decisions and then termination. -/
example :
    (informationTag (ObservedChanceGame.CountablePresentation.informationAtHistory
        game firstDecision),
      informationTag (ObservedChanceGame.CountablePresentation.informationAtHistory
        game secondDecision),
      informationTag (ObservedChanceGame.CountablePresentation.informationAtHistory
        game lastHistory)) = (1, 1, 0) := by
  native_decide

/-- The explicit decoder fails outside its finite domain. -/
example :
    (Encodable.decode
      (α := game.observed.base.toArena.HistoryFrom game.observed.base.init)
      3).isNone = true := by
  native_decide

variable (presentation : game.AnalyticPresentation)

/-- The two recurring player histories use exactly the same canonical
abstract action law because their original information states agree. -/
theorem recurring_player_abstract_law_eq :
    (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 firstPrefix) =
      (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 secondPrefix) := by
  exact
    presentation.abstractKernel_eq_of_player_infoAt_eq
      profile 0 firstPrefix secondPrefix 0
      rfl firstPrefix_nonterminal
      rfl secondPrefix_nonterminal
      infoState_recurs

/-- The supplied certified presentation compiles exactly to the concrete
history action kernel at every finite event prefix. -/
theorem compiled_kernel_exact
    (time : ℕ)
    (events : game.AnalyticHistoryArena.EventPrefix time) :
      (presentation.toPolicy profile).toEventHistoryActionPolicy.kernel
        time events =
      (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
        game profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) :=
  presentation.compiled_kernel profile time events

/-- The supplied presentation recovers the exact two-step stopped
complete-history law. -/
theorem two_step_state_law_exact :
    Measure.map
        (fun path : ℕ → game.AnalyticHistoryArena.State => path 2)
        (EventHistoryActionPolicy.statePathMeasure
          (presentation.toPolicy profile).toEventHistoryActionPolicy
            (game.observed.base.toArena.historyKernelArena
              game.observed.base.init).toMeasurable_measurableSet_terminalSet
            firstDecision) =
      finiteLawMeasureTop(
        game.observed.base.toArena.stochasticHistoryLawFrom
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            game profile)
          firstDecision 2) :=
  presentation.compiled_finite_state_law
    profile 2 firstDecision

end Examples.ObservedChanceCountablePresentationBoundary
