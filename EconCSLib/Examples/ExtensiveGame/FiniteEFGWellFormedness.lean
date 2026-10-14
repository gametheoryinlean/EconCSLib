/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed

/-!
# Finite-EFG well-formedness regressions

These examples distinguish raw information catalogs from represented strategy
coordinates.

The presentations use one-state terminal base games. A ghost Boolean
information carrier fails the optional `AllDecisionInfoRepresented`
certificate but still satisfies the structural finite-EFG certificate and has
an inhabited pure-profile type. A separate regression shows that an irrelevant
terminal player label fails mover normalization but still creates no strategy
coordinate.
-/

namespace FiniteEFGWellFormedness

def terminalArena : Arena where
  State := Unit
  Action := fun _ => Empty
  next := fun _ action => action.elim

def terminalBase : ExtensiveGame Unit Unit where
  toArena := terminalArena
  init := ()
  mover := fun _ => none
  payoff := fun _ _ => ()

/-- The canonical complete-information presentation uses only genuine player
decision histories as strategy coordinates. -/
def canonicalTerminalGame : ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation terminalBase

theorem canonicalTerminalGame_allDecisionInfoRepresented :
    canonicalTerminalGame.AllDecisionInfoRepresented :=
  ExtensiveGame.ObservedGame.completeInformation_allDecisionInfoRepresented
    terminalBase

theorem canonicalTerminalGame_decisionMoverCoherent :
    canonicalTerminalGame.DecisionMoverCoherent := by
  intro _history _i hmover
  simp [canonicalTerminalGame, terminalBase] at hmover

/-- Regression for the former all-history carrier bug: a terminal canonical
presentation now has an inhabited pure-profile type. -/
theorem canonicalTerminalGame_pureProfile_nonempty :
    Nonempty canonicalTerminalGame.PureProfile :=
  ExtensiveGame.ObservedGame.completeInformation_nonempty_pureProfile
    terminalBase

/-- The unconstrained base carrier also permits a semantically ignored player
label at a terminal state. -/
def playerLabeledTerminalBase : ExtensiveGame Unit Unit where
  toArena := terminalArena
  init := ()
  mover := fun _ => some ()
  payoff := fun _ _ => ()

def playerLabeledCanonicalTerminalGame :
    ExtensiveGame.ObservedGame Unit Unit :=
  ExtensiveGame.ObservedGame.completeInformation
    playerLabeledTerminalBase

/-- Mover coherence detects the player label on an empty terminal action
fiber. -/
theorem playerLabeledCanonicalTerminalGame_not_decisionMoverCoherent :
    ¬ playerLabeledCanonicalTerminalGame.DecisionMoverCoherent := by
  intro hcoherent
  have hnonempty :=
    hcoherent
      (Arena.HistoryFrom.nil terminalArena ())
      () rfl
  rcases hnonempty with ⟨action⟩
  exact action.elim

/-- Terminal mover labels do not create decision histories. Mover coherence is
still a useful normalization certificate, but no longer a precondition for
the complete-information strategy carrier to be inhabited. -/
theorem playerLabeledCanonicalTerminalGame_pureProfile_nonempty :
    Nonempty playerLabeledCanonicalTerminalGame.PureProfile := by
  refine ⟨fun _player information => ?_⟩
  have hfalse : False := by
    rcases information.property with ⟨witness⟩
    rcases witness.decision with ⟨action⟩
    exact action.elim
  exact hfalse.elim

/-- A presentation with decision-information values that are never realized.
-/
def ghostGame : ExtensiveGame.ObservedGame Unit Unit where
  base := terminalBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Bool
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => false
  infoAt_observe := by simp
  InfoAction := fun _ _ => Empty
  actionEquiv := fun _ _ _ _ => Equiv.refl Empty

/-- The stronger raw-catalog certificate detects ghost decision information. -/
theorem ghostGame_not_allDecisionInfoRepresented :
    ¬ ghostGame.AllDecisionInfoRepresented := by
  intro hrepresented
  rcases hrepresented () false with ⟨witness⟩
  have hmover := witness.mover
  simp [ghostGame, terminalBase] at hmover

/-- Ghost raw information does not obstruct structural finiteness because no
value is represented at a genuine decision. -/
def ghostGame_finiteEFG :
    ghostGame.FiniteEFGHypotheses where
  lengthBound := 0
  hasLengthBound :=
    Arena.HasLengthBoundAt.of_terminal
      (current :=
        Arena.HistoryFrom.nil
          ghostGame.base.toArena ghostGame.base.init)
      (by
        change IsEmpty Empty
        infer_instance)
  finiteAction := by
    intro _history
    change Fintype Empty
    exact inferInstance
  finiteDecisionPresentation := by
    intro i
    letI : IsEmpty (ghostGame.RepresentedInfo i) :=
      ⟨fun information => by
        rcases information.2 with ⟨witness⟩
        have hmover := witness.mover
        simp [ghostGame, terminalBase] at hmover⟩
    exact
      ⟨⟨0, Equiv.equivOfIsEmpty _ _⟩,
        fun information => isEmptyElim information⟩

/-- Ghost raw information creates neither a strategic obligation nor an empty
pure-profile carrier. -/
theorem ghostGame_pureProfile_nonempty :
    Nonempty ghostGame.PureProfile :=
  ExtensiveGame.ObservedGame.nonempty_pureProfile

/-- A presentation with no declared decision information, matching the fact
that the base has no player decision histories. -/
def cleanGame : ExtensiveGame.ObservedGame Unit Unit where
  base := terminalBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by simp
  InfoState := fun _ => Empty
  infoObserve := fun _ information => information.elim
  infoAt := fun _ _ hmover _hdecision => by
    simp [terminalBase] at hmover
  infoAt_observe := by
    intro _ _ hmover _hdecision
    simp [terminalBase] at hmover
  InfoAction := fun _ information => information.elim
  actionEquiv := fun _ _ hmover _hdecision => by
    simp [terminalBase] at hmover

theorem cleanGame_allDecisionInfoRepresented :
    cleanGame.AllDecisionInfoRepresented := by
  intro _ information
  exact information.elim

theorem cleanGame_decisionMoverCoherent :
    cleanGame.DecisionMoverCoherent := by
  intro _history _i hmover
  simp [cleanGame, terminalBase] at hmover

/-- The clean terminal presentation has a zero-step finite-EFG certificate.
-/
def cleanGame_finiteEFG :
    cleanGame.FiniteEFGHypotheses where
  lengthBound := 0
  hasLengthBound :=
    Arena.HasLengthBoundAt.of_terminal
      (current :=
        Arena.HistoryFrom.nil
          cleanGame.base.toArena cleanGame.base.init)
      (by
        change IsEmpty Empty
        infer_instance)
  finiteAction := by
    intro history
    change Fintype Empty
    exact inferInstance
  finiteDecisionPresentation := by
    intro _i
    letI : IsEmpty (cleanGame.RepresentedInfo _i) :=
      ⟨fun information => information.1.elim⟩
    exact
      ⟨⟨0, Equiv.equivOfIsEmpty _ _⟩,
        fun information => isEmptyElim information⟩

/-- Represented decision coordinates make the pure-profile carrier inhabited,
independently of the finite certificate. -/
theorem cleanGame_pureProfile_nonempty :
    Nonempty cleanGame.PureProfile :=
  ExtensiveGame.ObservedGame.nonempty_pureProfile

end FiniteEFGWellFormedness
