/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay

/-!
# Structural length and well-foundedness certificates

This module separates two strategy-independent termination hypotheses.

* `Arena.HasLengthBoundAt current bound` gives one uniform natural-number
  bound for every legal continuation of `current`.
* `Arena.IsWellFoundedAt current` is an `Acc` certificate for one-step
  extension of complete absolute histories and need not supply a uniform
  natural-number height.

Both notions quantify over all legal player and nature actions. They are
strictly stronger than almost-sure termination of one generated probability
law.

## Main results

* `HasLengthBoundAt.isWellFoundedAt` - a uniform bound supplies an `Acc`
  certificate.
* `HasLengthBoundAt.terminal_historyAt` - every complete play is terminal at
  the declared bound.
* `IsWellFoundedAt.eventuallyTerminates` - every complete legal play from an
  accessible history eventually terminates.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- Every continuation exactly `bound` actions from `current` is terminal.

When a branch terminates earlier there is no suffix of the requested positive
length, so the condition correctly allows varying branch lengths. -/
def HasLengthBoundAt (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) (bound : ℕ) : Prop :=
  ∀ {finish : A.State}
    (suffix : A.History current.1 finish),
    suffix.length = bound →
      A.IsTerminal finish

/-- Uniform structural length from an Arena root. -/
def HasLengthBoundFrom (A : Arena)
    (start : A.State) (bound : ℕ) : Prop :=
  A.HasLengthBoundAt (HistoryFrom.nil A start) bound

/-- One-step extension below `current` is accessible. -/
def IsWellFoundedAt (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) : Prop :=
  Acc (A.IsChildFrom (start := start)) current

/-- Structural well-foundedness from an Arena root. -/
def IsWellFoundedFrom (A : Arena) (start : A.State) : Prop :=
  A.IsWellFoundedAt (HistoryFrom.nil A start)

namespace HasLengthBoundAt

variable {current : A.HistoryFrom start} {bound : ℕ}

/-- A terminal current history has the zero-step structural length bound. -/
theorem of_terminal
    (hterminal : A.IsTerminal current.1) :
    A.HasLengthBoundAt current 0 := by
  intro finish suffix hlength
  cases suffix with
  | nil =>
      exact hterminal
  | snoc suffix action =>
      simp at hlength

/-- A zero-step bound says the current history is already terminal. -/
theorem terminal
    (hbound : A.HasLengthBoundAt current 0) :
    A.IsTerminal current.1 :=
  hbound (History.nil : A.History current.1 current.1) rfl

/-- Removing one initial action from a uniform successor bound leaves a
uniform bound at the child history. -/
theorem afterAction
    (hbound : A.HasLengthBoundAt current (bound + 1))
    (action : A.Action current.1) :
    A.HasLengthBoundAt
      ⟨A.next current.1 action, current.2.snoc action⟩
      bound := by
  intro finish suffix hlength
  apply hbound
    ((History.nil.snoc action).append suffix)
  simp [hlength, Nat.add_comm]

/-- A successor bound descends along any one-step child relation. -/
theorem of_child
    (hbound : A.HasLengthBoundAt current (bound + 1))
    {child : A.HistoryFrom start}
    (hchild : A.IsChildFrom child current) :
    A.HasLengthBoundAt child bound := by
  rcases hchild with ⟨action, rfl⟩
  exact hbound.afterAction action

/-- A uniform natural-number length bound supplies a constructive
well-foundedness certificate. -/
theorem isWellFoundedAt
    (hbound : A.HasLengthBoundAt current bound) :
    A.IsWellFoundedAt current := by
  induction bound generalizing current with
  | zero =>
      exact Acc.intro current fun child hchild =>
        (hchild.false_of_terminal hbound.terminal).elim
  | succ bound ih =>
      apply Acc.intro current
      intro child hchild
      exact ih (hbound.of_child hchild)

/-- Every legal complete play is terminal at a declared uniform bound. -/
theorem terminal_historyAt
    (hbound : A.HasLengthBoundAt current bound)
    (play : A.CompletePlayFromHistory current) :
    A.IsTerminal (play.historyAt bound).1 := by
  induction bound generalizing current with
  | zero =>
      rw [play.historyAt_zero]
      exact hbound.terminal
  | succ bound ih =>
      by_cases hterminal : A.IsTerminal current.1
      · have hterminalZero :
            A.IsTerminal (play.historyAt 0).1 := by
          rw [play.historyAt_zero]
          exact hterminal
        have hsame :=
          play.at_add_eq_of_terminal 0 hterminalZero (bound + 1)
        simp only [Nat.zero_add] at hsame
        rw [hsame, play.historyAt_zero]
        exact hterminal
      · have hnonterminalZero :
            ¬ A.IsTerminal (play.historyAt 0).1 := by
          rw [play.historyAt_zero]
          exact hterminal
        have hchild :=
          play.isChild_at_succ_of_not_terminal
            0 hnonterminalZero
        have hchildCurrent :
            A.IsChildFrom (play.historyAt 1) current := by
          simpa [play.historyAt_zero] using hchild
        have htail :=
          ih (hbound.of_child hchildCurrent) (play.drop 1)
        simpa [Nat.add_comm] using htail

/-- A uniform bound makes every complete legal play eventually terminate. -/
theorem eventuallyTerminates
    (hbound : A.HasLengthBoundAt current bound)
    (play : A.CompletePlayFromHistory current) :
    play.EventuallyTerminates :=
  ⟨bound, hbound.terminal_historyAt play⟩

end HasLengthBoundAt

namespace IsWellFoundedAt

variable {current : A.HistoryFrom start}

/-- A terminal history is structurally well-founded. -/
theorem of_terminal
    (hterminal : A.IsTerminal current.1) :
    A.IsWellFoundedAt current :=
  Acc.intro current fun _child hchild =>
    (hchild.false_of_terminal hterminal).elim

/-- Accessibility descends to every one-step child. -/
theorem child
    (hwellFounded : A.IsWellFoundedAt current)
    {nextHistory : A.HistoryFrom start}
    (hchild : A.IsChildFrom nextHistory current) :
    A.IsWellFoundedAt nextHistory := by
  cases hwellFounded with
  | intro _ descendants =>
      exact descendants nextHistory hchild

/-- Every complete legal play from an accessible history eventually reaches a
terminal coordinate. -/
theorem eventuallyTerminates
    (hwellFounded : A.IsWellFoundedAt current) :
    ∀ play : A.CompletePlayFromHistory current,
      play.EventuallyTerminates := by
  induction hwellFounded with
  | intro current descendants ih =>
      intro play
      by_cases hterminal : A.IsTerminal current.1
      · exact ⟨0, by
          rw [play.historyAt_zero]
          exact hterminal⟩
      · have hnonterminalZero :
            ¬ A.IsTerminal (play.historyAt 0).1 := by
          rw [play.historyAt_zero]
          exact hterminal
        have hchild :=
          play.isChild_at_succ_of_not_terminal
            0 hnonterminalZero
        have hchildCurrent :
            A.IsChildFrom (play.historyAt 1) current := by
          simpa [play.historyAt_zero] using hchild
        rcases ih (play.historyAt 1) hchildCurrent
            (play.drop 1) with
          ⟨n, hterminalTail⟩
        exact ⟨n + 1, by
          simpa [Nat.add_comm] using hterminalTail⟩

end IsWellFoundedAt

/-- Root well-foundedness descends to every complete absolute history.

Every such history is, by construction, a finite chain of one-step children
from the empty root history. -/
theorem IsWellFoundedFrom.atHistory
    (hwellFounded : A.IsWellFoundedFrom start)
    (history : A.HistoryFrom start) :
    A.IsWellFoundedAt history := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil =>
      exact hwellFounded
  | @snoc state path action ih =>
      exact ih.child
        (IsChildFrom.snoc ⟨state, path⟩ action)

/-- The child relation on complete histories is globally well founded once
it is well founded at the root, because every complete history begins at that
root. -/
theorem IsWellFoundedFrom.wellFounded_isChildFrom
    (hwellFounded : A.IsWellFoundedFrom start) :
    WellFounded (A.IsChildFrom (start := start)) :=
  ⟨hwellFounded.atHistory⟩

/-- A root length bound supplies root well-foundedness. -/
theorem HasLengthBoundFrom.isWellFoundedFrom
    {bound : ℕ}
    (hbound : A.HasLengthBoundFrom start bound) :
    A.IsWellFoundedFrom start :=
  HasLengthBoundAt.isWellFoundedAt hbound

/-- Every play of a root-well-founded Arena eventually terminates. -/
theorem IsWellFoundedFrom.eventuallyTerminates
    (hwellFounded : A.IsWellFoundedFrom start)
    (play : A.CompletePlayFrom start) :
    play.EventuallyTerminates :=
  IsWellFoundedAt.eventuallyTerminates hwellFounded play

end Arena
