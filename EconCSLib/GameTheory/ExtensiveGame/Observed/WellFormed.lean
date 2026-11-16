/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite

/-!
# Structural well-formedness and finite-EFG certificates

The general `ObservedGame` carrier intentionally permits unreachable
information states, infinite branching, player labels at terminal endpoints,
and infinite play. This module packages the stronger assumptions required by
finite textbook EFG algorithms without adding a second semantic game record.

`FiniteEFGHypotheses` is structural and representation-aware. It uses a
uniform bound in the complete-history unfolding rather than finite compact
state, and it requires finiteness only of represented decision information.
Finiteness of players and executable decidability assumptions remain
theorem-local because many structural results do not enumerate players or
compute transitions.

## Main definitions

* `ObservedGame.AllDecisionInfoRepresented`.
* `ObservedGame.DecisionMoverCoherent`.
* `ObservedGame.FiniteEFGHypotheses`.

## Main results

* represented raw information has a nonempty abstract action type;
* represented-coordinate pure contingent plans are always inhabited;
* every play under `FiniteEFGHypotheses` terminates and the unfolding is
  structurally well-founded.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} {G : ObservedGame N U}

/-- Every declared decision information state is represented by an actual
player-controlled complete history. -/
abbrev AllDecisionInfoRepresented
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.AllDecisionInfoRepresented

/-- Every player-labeled complete history is a genuine decision history with
at least one legal action.

This condition is deliberately not a field of `ExtensiveGame`: terminal
execution ignores mover labels. It is needed when all declared decision
information states are used to form total contingent plans. -/
abbrev DecisionMoverCoherent
    (G : ObservedGame N U) : Prop :=
  G.toControlledObservedGame.DecisionMoverCoherent

/-- The canonical decision-history complete-information presentation has no
ghost decision-information states. -/
theorem completeInformation_allDecisionInfoRepresented
    (base : ExtensiveGame N U) :
    AllDecisionInfoRepresented
      (completeInformation base) := by
  intro i information
  refine ⟨
    { history := information.1
      mover := information.2.1
      decision := information.2.2
      infoAt_eq := ?_ }⟩
  cases information
  rfl

namespace AllDecisionInfoRepresented

/-- A represented raw information state has at least one abstract legal
action. -/
theorem nonempty_infoAction
    (hrepresented : G.AllDecisionInfoRepresented)
    (i : N) (information : G.InfoState i) :
    Nonempty (G.InfoAction i information) :=
  ControlledObservedGame.AllDecisionInfoRepresented.nonempty_infoAction
    hrepresented i information

end AllDecisionInfoRepresented

/-- Every player's represented-coordinate pure contingent-plan type is
inhabited without extra well-formedness assumptions. -/
theorem nonempty_pureStrategy
    (i : N) :
    Nonempty (G.PureStrategy i) :=
  ControlledObservedGame.nonempty_pureStrategy i

/-- The represented-coordinate pure-profile type is inhabited without extra
well-formedness assumptions or a finite player type. -/
theorem nonempty_pureProfile
    : Nonempty G.PureProfile :=
  ControlledObservedGame.nonempty_pureProfile

/-- A canonical complete-information presentation has an inhabited pure-profile
carrier. Terminal mover labels do not create strategy coordinates. -/
theorem completeInformation_nonempty_pureProfile
    (base : ExtensiveGame N U) :
    Nonempty
      (completeInformation base).PureProfile :=
  nonempty_pureProfile

/-- Reusable structural hypotheses for a finite textbook EFG presentation.

The selected `lengthBound` bounds the legal complete-history unfolding, not
the compact state space. `finiteAction` stores explicit, executable concrete
action enumerations, while `finiteDecisionPresentation` fixes an executable
order on represented decision information and equality on each abstract
action fiber. Player finiteness, recall, chance laws, and preference orders
are intentionally separate. -/
abbrev FiniteEFGHypotheses
    (G : ObservedGame N U) :=
  G.toControlledObservedGame.FiniteEFGHypotheses

namespace FiniteEFGHypotheses

/-- A finite-EFG certificate supplies structural well-foundedness of the
complete-history unfolding. -/
theorem isWellFoundedFrom
    (h : G.FiniteEFGHypotheses) :
    G.base.toArena.IsWellFoundedFrom G.base.init :=
  ControlledObservedGame.FiniteEFGHypotheses.isWellFoundedFrom h

/-- Every complete legal play of a finite-EFG certificate eventually
terminates. -/
theorem eventuallyTerminates
    (h : G.FiniteEFGHypotheses)
    (play :
      G.base.toArena.CompletePlayFrom G.base.init) :
    play.EventuallyTerminates :=
  ControlledObservedGame.FiniteEFGHypotheses.eventuallyTerminates h play

end FiniteEFGHypotheses

end ExtensiveGame.ObservedGame
