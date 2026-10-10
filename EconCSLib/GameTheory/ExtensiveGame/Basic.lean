/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Basic

Payoff-aware compatibility for the minimal Arena-based EFG core.

## Design

The payoff-free `Arena` and `ControlledGame` carriers live in
`ExtensiveGame.Structural.Basic`. This module preserves the historical `Basic`
import path and adds only the endpoint-state-payoff `ExtensiveGame`
compatibility carrier.

## Main definitions

* `ExtensiveGame` — controlled game + state payoff

## References

* [MSZ] Maschler, Solan, Zamir, *Game Theory*, Chapter 3
-/

/-! ### Extensive-form game -/

/-- A state-payoff extensive game: a payoff-free controlled game together
with a convenient endpoint-state payoff.

    * `mover s` = who controls state `s` (`none` = non-player-controlled)
    * `payoff s i` = payoff for player `i` at state `s` (meaningful at terminal states)

    General terminal-history, complete-path, and winning-condition semantics
    are separate objective layers; this field is not their authoritative
    definition.

    No `isTerminal` field — terminal states are detected by `IsEmpty (Action s)`.
    No proof terms to carry around. -/
structure ExtensiveGame (N : Type*) (U : Type*) extends ControlledGame N where
  /-- Payoff at each state for each player.
      Meaningful at terminal states; may be arbitrary elsewhere. -/
  payoff : State → N → U

namespace ExtensiveGame

variable {N : Type*} {U : Type*}

/-- Add a state-based payoff interpretation to a payoff-free controlled game.

Forgetting the result with `ExtensiveGame.toControlledGame` recovers `base`
definitionally. -/
abbrev ofControlledGame (base : ControlledGame N)
    (payoff : base.State → N → U) :
    ExtensiveGame N U where
  toControlledGame := base
  payoff := payoff

@[simp]
theorem ofControlledGame_toControlledGame
    (base : ControlledGame N)
    (payoff : base.State → N → U) :
    (ofControlledGame base payoff).toControlledGame = base :=
  rfl

@[simp]
theorem ofControlledGame_payoff
    (base : ControlledGame N)
    (payoff : base.State → N → U)
    (state : base.State) (i : N) :
    (ofControlledGame base payoff).payoff state i = payoff state i :=
  rfl

/-- Add an initial state, mover assignment, and payoff function to an ordinary
arena.

All game-semantic data are explicit arguments; in particular this constructor
does not infer chance nodes or terminal payoffs from the arena. It composes
with observed-game presentation constructors without duplicating the arena's
state, action, or transition fields. -/
abbrev ofArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) :
    ExtensiveGame N U :=
  ofControlledGame (ControlledGame.ofArena arena init mover) payoff

@[simp]
theorem ofArena_toArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) :
    (ofArena arena init mover payoff).toArena = arena :=
  rfl

@[simp]
theorem ofArena_init (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) :
    (ofArena arena init mover payoff).init = init :=
  rfl

@[simp]
theorem ofArena_mover (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) (state : arena.State) :
    (ofArena arena init mover payoff).mover state = mover state :=
  rfl

@[simp]
theorem ofArena_payoff (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N)
    (payoff : arena.State → N → U) (state : arena.State) (i : N) :
    (ofArena arena init mover payoff).payoff state i = payoff state i :=
  rfl

/-- The arena of a game. -/
abbrev arena (G : ExtensiveGame N U) : Arena := G.toArena

/-- Forget only the state-payoff interpretation.

This is a lossless projection for dynamics, the initial root, and mover data.
It is the canonical migration path from payoff-aware APIs to structural or
logical-game APIs. -/
abbrev controlledGame (G : ExtensiveGame N U) : ControlledGame N :=
  G.toControlledGame

/-- Available actions at a state. -/
abbrev actions (G : ExtensiveGame N U) (s : G.State) := G.Action s

/-- A state is terminal. -/
abbrev isTerminal (G : ExtensiveGame N U) (s : G.State) := G.toArena.IsTerminal s

/-- A state is controlled by player `i`. -/
def isPlayerState (G : ExtensiveGame N U) (s : G.State) (i : N) : Prop :=
  G.toControlledGame.isPlayerState s i

/-- A nonterminal state carrying the non-player-control label.

This predicate supplies no probability law. -/
def isNonPlayerState (G : ExtensiveGame N U) (s : G.State) : Prop :=
  G.toControlledGame.isNonPlayerState s

/-- Compatibility name for `isNonPlayerState`.

No chance law is implied by this predicate alone. -/
abbrev isChanceState (G : ExtensiveGame N U) (s : G.State) : Prop :=
  G.isNonPlayerState s

/-- No chance nodes: every nonterminal state has a strategic mover. -/
def NoChance (G : ExtensiveGame N U) : Prop :=
  G.toControlledGame.NoChance

end ExtensiveGame
