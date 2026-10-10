/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay

/-!
# Terminal and complete-path objectives

This module separates EFG dynamics from outcome interpretation.

* A terminal outcome is indexed by a complete terminal history, so it can
  distinguish two routes that merge into one endpoint state.
* A path outcome is an arbitrary function of a complete legal play.
* A terminal outcome induces an `Option`-valued path outcome without assigning
  an invented value to nonterminating plays.
* A terminal outcome is evaluated only from an explicit terminal coordinate;
  no witness is extracted from an existential proposition.
* A computable terminal-coordinate finder induces an `Option`-valued or total
  path outcome.

Utilities and preferences are intentionally not stored here. They are attached
later through `GameForm`, `LawGameForm`, or `ContinuationGameForm`.

## Main definitions

* `Arena.TerminalHistoryFrom`.
* `Arena.TerminalOutcome`.
* `Arena.PathOutcomeFromHistory` and `Arena.PathOutcome`.
* `Arena.TerminalOutcome.toPartialPathOutcome`.
* `Arena.TerminalOutcome.toPathOutcome`.
* `ExtensiveGame.terminalPayoffOutcome`.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- A complete terminal history from `start`. -/
abbrev TerminalHistoryFrom (A : Arena) (start : A.State) :=
  {history : A.HistoryFrom start // A.IsTerminal history.1}

/-- A history-sensitive terminal outcome. -/
abbrev TerminalOutcome (A : Arena) (start : A.State)
    (Outcome : Type*) :=
  A.TerminalHistoryFrom start → Outcome

/-- An outcome depending on a complete play from an arbitrary absolute
history. -/
abbrev PathOutcomeFromHistory (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) (Outcome : Type*) :=
  A.CompletePlayFromHistory current → Outcome

/-- An outcome depending on a complete play from an Arena root. -/
abbrev PathOutcome (A : Arena) (start : A.State)
    (Outcome : Type*) :=
  A.CompletePlayFrom start → Outcome

namespace PathOutcomeFromHistory

variable {Outcome : Type*}

/-- Rebase an objective already defined on an absolute tail at `current` onto a
future play rooted at the current endpoint.

`splice` attaches the already accumulated absolute history to every future
coordinate. It does not replay root coordinates preceding `current`; use
`PathOutcome.afterHistory` to restrict an arbitrary root objective. -/
def rebaseTailAt
    (current : A.HistoryFrom start)
    (outcome : A.PathOutcomeFromHistory current Outcome) :
    A.PathOutcome current.1 Outcome :=
  fun future =>
    outcome (CompletePlayFromHistory.splice current future)

@[simp]
theorem rebaseTailAt_apply
    (current : A.HistoryFrom start)
    (outcome : A.PathOutcomeFromHistory current Outcome)
    (future : A.CompletePlayFrom current.1) :
    rebaseTailAt current outcome future =
      outcome
        (CompletePlayFromHistory.splice current future) :=
  rfl

end PathOutcomeFromHistory

namespace PathOutcome

variable {Outcome : Type*}

/-- Restrict an arbitrary root complete-play objective after one accumulated
absolute history.

`resume` replays every prefix coordinate before following the future, so
objectives depending on the root clock or earlier visits retain their original
meaning. -/
def afterHistory
    (outcome : A.PathOutcome start Outcome)
    (current : A.HistoryFrom start) :
    A.PathOutcome current.1 Outcome :=
  fun future =>
    outcome (CompletePlayFromHistory.resume current future)

@[simp]
theorem afterHistory_apply
    (outcome : A.PathOutcome start Outcome)
    (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) :
    outcome.afterHistory current future =
      outcome (CompletePlayFromHistory.resume current future) :=
  rfl

end PathOutcome

namespace CompletePlayFromHistory

variable {current : A.HistoryFrom start}

/-- The terminal coordinate carried by an explicit computational witness. -/
def terminalIndex
    (play : A.CompletePlayFromHistory current)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1}) : ℕ :=
  hit.1

/-- The supplied terminal coordinate is terminal. -/
theorem terminalIndex_spec
    (play : A.CompletePlayFromHistory current)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    A.IsTerminal
      (play.historyAt (play.terminalIndex hit)).1 :=
  hit.2

/-- The complete terminal history selected by an explicit terminal
coordinate. Any two such coordinates carry the same history because complete
plays stutter after termination. -/
def terminalHistory
    (play : A.CompletePlayFromHistory current)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    A.TerminalHistoryFrom start :=
  ⟨play.historyAt (play.terminalIndex hit),
    play.terminalIndex_spec hit⟩

@[simp]
theorem terminalHistory_val
    (play : A.CompletePlayFromHistory current)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    (play.terminalHistory hit).1 =
      play.historyAt (play.terminalIndex hit) :=
  rfl

end CompletePlayFromHistory

namespace TerminalOutcome

variable {Outcome : Type*}

/-- Evaluate a terminal outcome at an explicitly supplied terminal
coordinate. -/
def evaluate
    (outcome : A.TerminalOutcome start Outcome)
    (play : A.CompletePlayFrom start)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    Outcome :=
  outcome (play.terminalHistory hit)

/-- Use a computable terminal-coordinate finder to regard a terminal outcome
as an `Option`-valued path outcome.

The finder controls partiality: `none` means that it did not supply a terminal
coordinate. No decision procedure for existential termination and no
artificial terminal utility is hidden in this definition. -/
def toPartialPathOutcome
    (outcome : A.TerminalOutcome start Outcome)
    (findTerminal :
      ∀ play : A.CompletePlayFrom start,
        Option {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    A.PathOutcome start (Option Outcome) :=
  fun play =>
    (findTerminal play).map (outcome.evaluate play)

/-- A terminal coordinate returned by the finder is evaluated in the partial
path semantics. -/
theorem toPartialPathOutcome_eq_some
    (outcome : A.TerminalOutcome start Outcome)
    (findTerminal :
      ∀ play : A.CompletePlayFrom start,
        Option {n : ℕ // A.IsTerminal (play.historyAt n).1})
    (play : A.CompletePlayFrom start)
    (hit : {n : ℕ // A.IsTerminal (play.historyAt n).1})
    (hfind : findTerminal play = some hit) :
    outcome.toPartialPathOutcome findTerminal play =
      some (outcome.evaluate play hit) := by
  simp [toPartialPathOutcome, hfind]

/-- A failed terminal-coordinate search produces no terminal outcome. -/
theorem toPartialPathOutcome_eq_none
    (outcome : A.TerminalOutcome start Outcome)
    (findTerminal :
      ∀ play : A.CompletePlayFrom start,
        Option {n : ℕ // A.IsTerminal (play.historyAt n).1})
    (play : A.CompletePlayFrom start)
    (hfind : findTerminal play = none) :
    outcome.toPartialPathOutcome findTerminal play = none := by
  simp [toPartialPathOutcome, hfind]

/-- A terminal-coordinate producer makes a terminal outcome into a total path
outcome. Unlike an existential all-play termination proof, the producer
contains the runtime coordinate used for evaluation. -/
def toPathOutcome
    (outcome : A.TerminalOutcome start Outcome)
    (terminalHit :
      ∀ play : A.CompletePlayFrom start,
        {n : ℕ // A.IsTerminal (play.historyAt n).1}) :
    A.PathOutcome start Outcome :=
  fun play =>
    outcome.evaluate play (terminalHit play)

end TerminalOutcome

end Arena

namespace ControlledGame

variable {N : Type*}

/-- Terminal complete histories of a payoff-free controlled game. -/
abbrev TerminalHistory (G : ControlledGame N) :=
  G.toArena.TerminalHistoryFrom G.init

/-- A history-sensitive terminal outcome on a payoff-free controlled game. -/
abbrev TerminalOutcome (G : ControlledGame N) (Outcome : Type*) :=
  G.toArena.TerminalOutcome G.init Outcome

/-- A complete-path outcome on a payoff-free controlled game. -/
abbrev PathOutcome (G : ControlledGame N) (Outcome : Type*) :=
  G.toArena.PathOutcome G.init Outcome

end ControlledGame

namespace ExtensiveGame

variable {N U : Type*}

/-- The existing endpoint-state payoff interpreted as a history-indexed
terminal outcome. -/
def terminalPayoffOutcome (G : ExtensiveGame N U) :
    G.toArena.TerminalOutcome G.init (N → U) :=
  fun history => G.payoff history.1.1

@[simp]
theorem terminalPayoffOutcome_apply
    (G : ExtensiveGame N U)
    (history : G.toArena.TerminalHistoryFrom G.init) :
    G.terminalPayoffOutcome history =
      G.payoff history.1.1 :=
  rfl

end ExtensiveGame
