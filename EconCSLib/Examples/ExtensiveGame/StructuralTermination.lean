/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Objective

/-!
# Structural termination regressions

These examples separate finite state, uniform finite length, and structural
well-foundedness.

* `InfiniteLoop` has one state but a genuinely infinite complete play, so
  finite state does not imply any structural termination certificate.
* `UnboundedWellFounded` is structurally well-founded but has no uniform
  natural-number length bound: the first action chooses an arbitrary finite
  countdown.
-/

namespace Examples.StructuralTermination

namespace InfiniteLoop

/-- A one-state Arena with one self-loop action. -/
def arena : Arena where
  State := Unit
  Action _ := Unit
  next _ _ := ()

/-- The unique history after `n` loop actions. -/
def history : (n : ℕ) → arena.History () ()
  | 0 => .nil
  | n + 1 => (history n).snoc ()

/-- The unique genuinely infinite complete play. -/
def play : arena.CompletePlayFrom () where
  historyAt n := ⟨(), history n⟩
  historyAt_zero := rfl
  step _ := Or.inr ⟨(), rfl⟩

/-- No coordinate of the self-loop play is terminal. -/
theorem play_neverTerminates : play.NeverTerminates := by
  intro _n hterminal
  exact hterminal.false ()

/-- A finite-state Arena may fail structural well-foundedness. -/
theorem not_isWellFoundedFrom :
    ¬ arena.IsWellFoundedFrom () := by
  intro hwellFounded
  exact
    play.not_eventuallyTerminates_of_neverTerminates
      play_neverTerminates
      (hwellFounded.eventuallyTerminates play)

/-- Consequently the self-loop has no uniform structural length bound. -/
theorem not_hasLengthBoundFrom (bound : ℕ) :
    ¬ arena.HasLengthBoundFrom () bound := by
  intro hbound
  exact not_isWellFoundedFrom hbound.isWellFoundedFrom

/-- A two-step accumulated history in the loop Arena. -/
def current : arena.HistoryFrom () :=
  ⟨(), history 2⟩

/-- Resuming after an accumulated history replays the original root clock,
rather than treating `current` as time zero. -/
theorem resume_preserves_root_and_current :
    (Arena.CompletePlayFromHistory.resume current play).historyAt 0 =
        Arena.HistoryFrom.nil arena () ∧
      (Arena.CompletePlayFromHistory.resume current play).historyAt 2 =
        current := by
  constructor
  · exact Arena.CompletePlayFromHistory.resume_at_zero current play
  · simpa [current, history] using
      Arena.CompletePlayFromHistory.resume_at_length current play

/-- A root-clock objective recording the absolute history length at time zero.
-/
def rootClock :
    arena.PathOutcome () ℕ :=
  fun complete => complete.historyAt 0 |>.2.length

/-- Restricting a root-clock objective after a history still evaluates time
zero at the original root. -/
theorem afterHistory_replays_prefix :
    rootClock.afterHistory current play = 0 := by
  change
    ((Arena.CompletePlayFromHistory.resume
      current play).historyAt 0).2.length = 0
  rw [Arena.CompletePlayFromHistory.resume_at_zero]
  rfl

/-- An absolute-tail objective records the already accumulated history at its
own time zero. This is intentionally different from `rootClock.afterHistory`.
-/
def absoluteTailClock :
    arena.PathOutcomeFromHistory current ℕ :=
  fun complete => complete.historyAt 0 |>.2.length

theorem rebaseTailAt_starts_at_current :
    absoluteTailClock.rebaseTailAt current play = 2 := by
  change
    ((Arena.CompletePlayFromHistory.splice
      current play).historyAt 0).2.length = 2
  rw [Arena.CompletePlayFromHistory.splice_at, play.historyAt_zero]
  change
    (current.append
      (Arena.HistoryFrom.nil arena current.1)).2.length = 2
  rw [Arena.HistoryFrom.append_nil]
  rfl

end InfiniteLoop

namespace UnboundedWellFounded

/-- The root chooses an arbitrary countdown; state zero is terminal. -/
inductive State
  | root
  | countdown (remaining : ℕ)

/-- Root actions choose a countdown and positive countdown states have one
forced decrement action. -/
def Action : State → Type
  | .root => ℕ
  | .countdown 0 => PEmpty
  | .countdown (Nat.succ _) => PUnit

/-- Countdown transition. -/
def next : (state : State) → Action state → State
  | .root, chosen => .countdown chosen
  | .countdown (Nat.succ remaining), _ =>
      .countdown remaining

/-- The unbounded but well-founded countdown Arena. -/
def arena : Arena where
  State := State
  Action := Action
  next := next

/-- Countdown zero is terminal. -/
theorem terminal_zero :
    arena.IsTerminal (.countdown 0) :=
  ⟨fun action => nomatch action⟩

/-- Root and positive countdown states are nonterminal. -/
theorem not_terminal_root :
    ¬ arena.IsTerminal .root :=
  fun hterminal => by
    change IsEmpty ℕ at hterminal
    exact hterminal.false 0

theorem not_terminal_one :
    ¬ arena.IsTerminal (.countdown 1) :=
  fun hterminal => by
    change IsEmpty PUnit at hterminal
    exact hterminal.false PUnit.unit

/-- Every absolute history ending at countdown `remaining` is accessible. -/
theorem countdown_isWellFoundedAt
    (remaining : ℕ)
    (path : arena.History .root (.countdown remaining)) :
    arena.IsWellFoundedAt ⟨.countdown remaining, path⟩ := by
  induction remaining with
  | zero =>
      apply Arena.IsWellFoundedAt.of_terminal
      exact terminal_zero
  | succ remaining ih =>
      unfold Arena.IsWellFoundedAt
      constructor
      intro child hchild
      rcases hchild with ⟨action, rfl⟩
      exact ih (path.snoc action)

/-- The root is accessible although its subtrees have unbounded finite
heights. -/
theorem isWellFoundedFrom :
    arena.IsWellFoundedFrom .root := by
  apply Acc.intro (Arena.HistoryFrom.nil arena .root)
  intro child hchild
  rcases hchild with ⟨chosen, rfl⟩
  exact countdown_isWellFoundedAt chosen
    (Arena.History.nil.snoc chosen)

/-- A forced history from countdown `n + 1` down to countdown one. -/
def descendToOne :
    (n : ℕ) →
      arena.History (.countdown (n + 1)) (.countdown 1)
  | 0 => .nil
  | n + 1 =>
      (Arena.History.nil.snoc PUnit.unit).append
        (descendToOne n)

@[simp]
theorem descendToOne_length (n : ℕ) :
    (descendToOne n).length = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [descendToOne, Arena.History.length_append]
      change 1 + (descendToOne n).length = n + 1
      rw [ih]
      exact Nat.add_comm 1 n

/-- For every requested length, a nonterminal history of exactly that length
exists. -/
def longHistory : (bound : ℕ) →
    Σ finish : arena.State,
      arena.History .root finish
  | 0 => ⟨.root, .nil⟩
  | bound + 1 =>
      ⟨.countdown 1,
        (Arena.History.nil.snoc (bound + 1)).append
          (descendToOne bound)⟩

@[simp]
theorem longHistory_length (bound : ℕ) :
    (longHistory bound).2.length = bound := by
  cases bound with
  | zero =>
      rfl
  | succ bound =>
      rw [longHistory, Arena.History.length_append]
      change 1 + (descendToOne bound).length = bound + 1
      rw [descendToOne_length]
      exact Nat.add_comm 1 bound

/-- The chosen long history always ends at a nonterminal state. -/
theorem longHistory_not_terminal (bound : ℕ) :
    ¬ arena.IsTerminal (longHistory bound).1 := by
  cases bound with
  | zero =>
      exact not_terminal_root
  | succ _ =>
      exact not_terminal_one

/-- Structural well-foundedness need not supply one uniform natural-number
bound when branching is infinite. -/
theorem no_uniform_length_bound (bound : ℕ) :
    ¬ arena.HasLengthBoundFrom .root bound := by
  intro hbound
  apply longHistory_not_terminal bound
  exact hbound (longHistory bound).2 (longHistory_length bound)

end UnboundedWellFounded

end Examples.StructuralTermination
