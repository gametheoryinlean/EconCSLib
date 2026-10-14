/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.IsEmpty.Basic

/-!
# Payoff-free structural carriers for extensive games

This module contains only the representation-neutral dynamics used by the
minimal EFG core.

## Main definitions

* `Arena` — states, dependent legal actions, and transitions.
* `Arena.IsTerminal` — terminality as absence of legal actions.
* `ControlledGame` — an Arena with a root and player-control labels.
* `Arena.ofFin` — a small constructor for explicitly finite arenas.

No payoff, objective, probability law, finiteness assumption, decidability
assumption, or information structure is stored in these carriers. In
particular, `mover s = none` is only a non-player-control label. A chance law,
when desired, belongs to a separate stochastic semantics layer.

This state-space representation permits merging paths, cycles, and infinite
state or action types. History unfolding is provided separately.
-/

/-- A game arena: the pure dynamics of an extensive-form game.

States, actions, and transitions are stored without players, payoffs, or
probability. A state is terminal iff `Action s` is empty. -/
structure Arena where
  /-- The state space. -/
  State : Type*
  /-- Available actions at each state. Empty means terminal. -/
  Action : State → Type*
  /-- Transition function from a state and one legal action. -/
  next : (s : State) → Action s → State

namespace Arena

variable (A : Arena)

/-- A state is terminal if there are no available actions. -/
def IsTerminal (s : A.State) : Prop := IsEmpty (A.Action s)

/-- A state is a decision point if it has at least one available action. -/
def IsDecision (s : A.State) : Prop := Nonempty (A.Action s)

/-- Terminal and decision states are complementary. -/
theorem isTerminal_iff_not_isDecision (s : A.State) :
    A.IsTerminal s ↔ ¬ A.IsDecision s := by
  simp [IsTerminal, IsDecision, isEmpty_iff, not_nonempty_iff]

/-- Classical compatibility bridge for legacy APIs stated with a merely
nonterminal premise.

Core decision-information data should request `IsDecision` directly. This
lemma is reserved for interfaces, such as terminal-aware history policies,
whose established callback contract supplies `¬ IsTerminal`. -/
theorem isDecision_of_not_isTerminal (s : A.State)
    (hnonterminal : ¬ A.IsTerminal s) : A.IsDecision s := by
  classical
  by_contra hnotDecision
  exact hnonterminal ((A.isTerminal_iff_not_isDecision s).2 hnotDecision)

end Arena

/-- A payoff-free controlled extensive-game skeleton.

`ControlledGame` adds only a distinguished initial state and a mover label to
the pure `Arena` dynamics. It deliberately stores no objective, payoff,
probability law, finiteness, decidability, or information data.

At a nonterminal state, `mover s = none` means only that the state is not
controlled by a strategic player. It does not itself supply a chance
distribution. The mover label at a terminal state is semantically ignored. -/
structure ControlledGame (N : Type*) extends Arena where
  /-- The initial state (root of the controlled game). -/
  init : State
  /-- Who controls each state. `none` means non-player-controlled. -/
  mover : State → Option N

namespace ControlledGame

variable {N : Type*}

/-- Add an initial state and mover assignment to an ordinary arena. -/
abbrev ofArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    ControlledGame N where
  toArena := arena
  init := init
  mover := mover

@[simp]
theorem ofArena_toArena (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).toArena = arena :=
  rfl

@[simp]
theorem ofArena_init (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) :
    (ofArena arena init mover).init = init :=
  rfl

@[simp]
theorem ofArena_mover (arena : Arena) (init : arena.State)
    (mover : arena.State → Option N) (state : arena.State) :
    (ofArena arena init mover).mover state = mover state :=
  rfl

/-- The arena of a payoff-free controlled game. -/
abbrev arena (G : ControlledGame N) : Arena := G.toArena

/-- Available actions at a state. -/
abbrev actions (G : ControlledGame N) (s : G.State) := G.Action s

/-- A state is terminal. -/
abbrev isTerminal (G : ControlledGame N) (s : G.State) :=
  G.toArena.IsTerminal s

/-- A state is controlled by player `i`. -/
def isPlayerState (G : ControlledGame N) (s : G.State) (i : N) : Prop :=
  G.mover s = some i

/-- A nonterminal state carrying the non-player-control label.

This predicate deliberately supplies no probability law. -/
def isNonPlayerState (G : ControlledGame N) (s : G.State) : Prop :=
  G.mover s = none ∧ ¬ G.toArena.IsTerminal s

/-- Compatibility name for a non-player-controlled nonterminal state.

This structural predicate does not assert that a chance law exists. Stochastic
layers may interpret such a state as chance only after supplying the relevant
law. -/
abbrev isChanceState (G : ControlledGame N) (s : G.State) : Prop :=
  G.isNonPlayerState s

/-- Every nonterminal state has a strategic mover. -/
def NoChance (G : ControlledGame N) : Prop :=
  ∀ s : G.State, ¬ G.isTerminal s → ∃ i : N, G.mover s = some i

end ControlledGame

/-- Build an arena from a `Fin`-indexed state space with finite action types.
Terminal states have `nActions s = 0`. -/
def Arena.ofFin (n : ℕ) (nActions : Fin n → ℕ)
    (next : (s : Fin n) → Fin (nActions s) → Fin n) : Arena where
  State := Fin n
  Action := fun s => Fin (nActions s)
  next := next
