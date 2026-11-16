/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

/-!
# Discrete.ObservedChance — direct finite execution of observed chance games

This module assembles an exact finite event-history policy directly from an
observed chance game's original laws.  Player histories read the acting
player's information-indexed behavioral `FiniteLaw`; chance histories read the
game's declared chance `FiniteLaw`.  No measure, measurable kernel, or
realization presentation is an input to the algorithm.

Terminal detection is supplied explicitly.  The bounded executor therefore
contains no classical terminal decision hidden in its implementation.

## Main definitions

* `ObservedChanceGame.finiteHistoryArena` — the deterministic complete-history
  execution arena;
* `BehavioralProfile.toFiniteEventPolicy` — direct finite event-history
  policy;
* `BehavioralProfile.finiteActionLaw?` — terminal-aware action-law query;
* `BehavioralProfile.finitePrefixLawFrom` — bounded exact event-prefix
  execution.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- The discrete complete-history arena used to execute an observed chance
game. Its transition is deterministic history append; all probability comes
from the player and chance action laws. -/
def finiteHistoryArena (G : ObservedChanceGame N U) : KernelArena where
  State := G.observed.base.toArena.HistoryFrom G.observed.base.init
  Action := fun history => G.observed.base.Action history.1
  next := fun history action =>
    FiniteLaw.pure
      ⟨G.observed.base.next history.1 action,
        history.2.snoc action⟩

@[simp]
theorem finiteHistoryArena_next
    (G : ObservedChanceGame N U)
    (history : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (action : G.observed.base.Action history.1) :
    (finiteHistoryArena G).next history action =
      FiniteLaw.pure
        ⟨G.observed.base.next history.1 action,
          history.2.snoc action⟩ :=
  rfl

/-- An explicit decision procedure for terminal base states. -/
abbrev TerminalDecision (G : ObservedChanceGame N U) :=
  (state : G.observed.base.State) →
    Decidable (G.observed.base.isTerminal state)

/-- Lift a base-state terminal decision to complete-history states. -/
def historyTerminalDecision {G : ObservedChanceGame N U}
    (terminalDecision : TerminalDecision G) :
    (history : (finiteHistoryArena G).State) →
      Decidable (IsEmpty ((finiteHistoryArena G).Action history)) :=
  fun history => terminalDecision history.1

namespace BehavioralProfile

variable {G : ObservedChanceGame N U}

/-- Direct executable compilation of a behavioral profile from the game's
original player and chance finite laws. -/
def toFiniteEventPolicy
    (profile : G.observed.BehavioralProfile) :
    (finiteHistoryArena G).EventHistoryPolicy :=
  fun _time history hnonterminal =>
    toHistoryPolicy G profile history.latestState hnonterminal

@[simp]
theorem toFiniteEventPolicy_apply
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty ((finiteHistoryArena G).Action history.latestState)) :
    toFiniteEventPolicy profile time history hnonterminal =
      toHistoryPolicy G profile history.latestState hnonterminal :=
  rfl

/-- At a player-controlled prefix, direct finite compilation reads exactly
that player's information-indexed action law. -/
theorem toFiniteEventPolicy_of_mover
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty ((finiteHistoryArena G).Action history.latestState))
    (i : N)
    (hmover : G.observed.base.mover history.latestState.1 = some i) :
    toFiniteEventPolicy profile time history hnonterminal =
      profile.actionLawAt G.observed history.latestState i hmover
        hnonterminal := by
  exact toHistoryPolicy_of_mover
    G profile history.latestState hnonterminal i hmover

/-- At a chance prefix, direct finite compilation reads exactly the game's
declared chance action law. -/
theorem toFiniteEventPolicy_of_chance
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty ((finiteHistoryArena G).Action history.latestState))
    (hmover : G.observed.base.mover history.latestState.1 = none) :
    toFiniteEventPolicy profile time history hnonterminal =
      G.chanceKernel history.latestState ⟨hmover, hnonterminal⟩ := by
  exact toHistoryPolicy_of_chance
    G profile history.latestState hnonterminal hmover

/-- Query the bundled selected-action law, returning `none` exactly at a
terminal prefix. The terminal decision procedure is an ordinary explicit
input to the algorithm. -/
def finiteActionLaw?
    (terminalDecision : TerminalDecision G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time) :
    Option (FiniteLaw (finiteHistoryArena G).ActionBundle) := by
  letI := historyTerminalDecision terminalDecision
  exact (toFiniteEventPolicy profile).actionLaw? time history

@[simp]
theorem finiteActionLaw?_eq_none_iff
    (terminalDecision : TerminalDecision G)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time) :
    finiteActionLaw? terminalDecision profile time history = none ↔
      G.observed.base.isTerminal history.latestState.1 := by
  letI := historyTerminalDecision terminalDecision
  exact
    (toFiniteEventPolicy profile).actionLaw?_eq_none_iff
      time history

/-- Execute the directly compiled policy for a bounded number of transitions,
retaining every state and selected-action occurrence. -/
def finitePrefixLawFrom
    (terminalDecision : TerminalDecision G)
    (profile : G.observed.BehavioralProfile)
    (start : ℕ)
    (initialPrefix : (finiteHistoryArena G).EventPrefix start)
    (steps : ℕ) :
    FiniteLaw ((finiteHistoryArena G).EventPrefix (start + steps)) := by
  letI := historyTerminalDecision terminalDecision
  exact
    (toFiniteEventPolicy profile).prefixLawFrom
      start initialPrefix steps

end BehavioralProfile

end ExtensiveGame.ObservedChanceGame
