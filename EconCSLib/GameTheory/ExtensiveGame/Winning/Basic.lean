/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Winning conditions on complete extensive-game plays

This module treats a winning condition as objective data: one set of complete
legal plays for each player. It does not build finiteness, determinacy,
measurability, or equilibrium assumptions into that data.

The primary definitions accept an arbitrary current absolute history. Root
specializations are abbreviations. Terminal win/lose rules embed without
assigning a winner to a nonterminating play, while path outcomes embed by
ordinary inverse image.

For observed games, compatibility with one player's pure strategy constrains
only that player's decision coordinates. The API distinguishes pathwise
robustness from winning against information-consistent opponent profiles.
Pure and quasistrategy play-compatibility predicates are defined in the
payoff-free `Controlled.Infrastructure` leaves; this module adds their
winning-condition interpretations.

## Main definitions

* `Arena.WinningConditionFrom` and `Arena.WinningCondition`.
* `WinningConditionFrom.IsExclusive` and `.IsTotal`.
* `WinningConditionFrom.ofTerminal` and `.ofPathOutcome`.
* `WinningConditionFrom.DecidesAt` and `.PrefixDecision`.
* `ControlledObservedGame.IsCompatibleWithPlayerStrategyFrom`.
* `ControlledObservedGame.HasPathwiseWinningStrategy`.
* `ControlledObservedGame.HasWinningQuasiStrategy`.

The payoff-aware `ObservedGame` surface is isolated in `Winning.BasicCompat`.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- A family of winning sets on complete plays from an arbitrary absolute
history. -/
abbrev WinningConditionFrom (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) (N : Type*) :=
  N → Set (A.CompletePlayFromHistory current)

/-- A family of winning sets on complete plays from an Arena root. -/
abbrev WinningCondition (A : Arena) (start : A.State) (N : Type*) :=
  A.WinningConditionFrom (HistoryFrom.nil A start) N

/-- The cylinder of complete plays that visit one complete absolute history.

If `history` is not a continuation of `current`, the cylinder is empty. The
definition deliberately remains meaningful without a decidable prefix
relation or finite state space. -/
def CompletePlayCylinderFrom (A : Arena) {start : A.State}
    (current history : A.HistoryFrom start) :
    Set (A.CompletePlayFromHistory current) :=
  {play | ∃ n, play.historyAt n = history}

namespace WinningConditionFrom

variable {current : A.HistoryFrom start} {N Outcome : Type*}

/-- No complete play is winning for two distinct players. -/
def IsExclusive
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ (play : A.CompletePlayFromHistory current) {i j : N},
    play ∈ W i → play ∈ W j → i = j

/-- Every complete play is winning for at least one player. -/
def IsTotal
    (W : A.WinningConditionFrom current N) : Prop :=
  ∀ play : A.CompletePlayFromHistory current,
    ∃ i, play ∈ W i

/-- The winning sets form a partition of complete plays. -/
def IsPartition
    (W : A.WinningConditionFrom current N) : Prop :=
  W.IsExclusive ∧ W.IsTotal

/-- Two players have exactly complementary winning sets.

The explicit exclusive-or formulation is constructive: it provides a winner
on every play rather than identifying winning with the negation of losing via
an implicit excluded-middle step. -/
def AreComplementary
    (W : A.WinningConditionFrom current N) (first second : N) : Prop :=
  ∀ play,
    (play ∈ W first ∧ play ∉ W second) ∨
      (play ∉ W first ∧ play ∈ W second)

/-- A two-player zero-sum winning condition, represented with players
`0, 1 : Fin 2`. Exactly one player wins every complete play. -/
def IsTwoPlayerZeroSum
    (W : A.WinningConditionFrom current (Fin 2)) : Prop :=
  W.AreComplementary 0 1

/-- A two-player zero-sum winning condition is total. -/
theorem IsTwoPlayerZeroSum.isTotal
    {W : A.WinningConditionFrom current (Fin 2)}
    (hzeroSum : W.IsTwoPlayerZeroSum) :
    W.IsTotal := by
  intro play
  rcases hzeroSum play with hzero | hone
  · exact ⟨0, hzero.1⟩
  · exact ⟨1, hone.2⟩

/-- A two-player zero-sum winning condition is exclusive. -/
theorem IsTwoPlayerZeroSum.isExclusive
    {W : A.WinningConditionFrom current (Fin 2)}
    (hzeroSum : W.IsTwoPlayerZeroSum) :
    W.IsExclusive := by
  intro play i j hi hj
  have hnotBoth :
      ¬ (play ∈ W (0 : Fin 2) ∧
          play ∈ W (1 : Fin 2)) := by
    intro hboth
    rcases hzeroSum play with hzero | hone
    · exact hzero.2 hboth.2
    · exact hone.1 hboth.1
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hnotBoth ⟨hi, hj⟩).elim
  · exact (hnotBoth ⟨hj, hi⟩).elim
  · rfl

/-- A two-player zero-sum winning condition partitions complete plays. -/
theorem IsTwoPlayerZeroSum.isPartition
    {W : A.WinningConditionFrom current (Fin 2)}
    (hzeroSum : W.IsTwoPlayerZeroSum) :
    W.IsPartition :=
  ⟨hzeroSum.isExclusive, hzeroSum.isTotal⟩

/-- Pull winning subsets of an outcome space back along a complete-path
outcome map. -/
def ofPathOutcome
    (outcome : A.PathOutcomeFromHistory current Outcome)
    (wins : N → Set Outcome) :
    A.WinningConditionFrom current N :=
  fun i => outcome ⁻¹' wins i

@[simp]
theorem mem_ofPathOutcome_iff
    (outcome : A.PathOutcomeFromHistory current Outcome)
    (wins : N → Set Outcome) (i : N)
    (play : A.CompletePlayFromHistory current) :
    play ∈ ofPathOutcome outcome wins i ↔
      outcome play ∈ wins i :=
  Iff.rfl

/-- Lift history-sensitive terminal winning sets to complete plays.

A play wins only when it actually reaches a terminal history in the supplied
terminal winning set. In particular, a nonterminating play is not silently
assigned a terminal winner. -/
def ofTerminal
    (wins : N → Set (A.TerminalHistoryFrom start)) :
    A.WinningConditionFrom current N :=
  fun i =>
    {play | ∃ (n : ℕ)
        (hterminal : A.IsTerminal (play.historyAt n).1),
      (⟨play.historyAt n, hterminal⟩ :
        A.TerminalHistoryFrom start) ∈ wins i}

@[simp]
theorem mem_ofTerminal_iff
    (wins : N → Set (A.TerminalHistoryFrom start))
    (i : N) (play : A.CompletePlayFromHistory current) :
    play ∈ ofTerminal wins i ↔
      ∃ (n : ℕ)
        (hterminal : A.IsTerminal (play.historyAt n).1),
        (⟨play.historyAt n, hterminal⟩ :
          A.TerminalHistoryFrom start) ∈ wins i :=
  Iff.rfl

/-- Exclusive terminal winning sets induce exclusive complete-play winning
sets. -/
theorem isExclusive_ofTerminal
    (wins : N → Set (A.TerminalHistoryFrom start))
    (hexclusive :
      ∀ (history : A.TerminalHistoryFrom start) {i j : N},
        history ∈ wins i → history ∈ wins j → i = j) :
    (ofTerminal (current := current) wins).IsExclusive := by
  intro play i j hi hj
  rcases hi with ⟨first, hfirst, hwinsFirst⟩
  rcases hj with ⟨second, hsecond, hwinsSecond⟩
  have heq :
      play.historyAt first = play.historyAt second :=
    play.historyAt_eq_of_terminal hfirst hsecond
  have hterminalEq :
      (⟨play.historyAt first, hfirst⟩ :
          A.TerminalHistoryFrom start) =
        ⟨play.historyAt second, hsecond⟩ :=
    Subtype.ext heq
  rw [hterminalEq] at hwinsFirst
  exact hexclusive
    ⟨play.historyAt second, hsecond⟩ hwinsFirst hwinsSecond

/-- Total terminal winning sets induce a total complete-play winning
condition whenever every complete play terminates. -/
theorem isTotal_ofTerminal
    (wins : N → Set (A.TerminalHistoryFrom start))
    (htotal :
      ∀ history : A.TerminalHistoryFrom start,
        ∃ i, history ∈ wins i)
    (hterminates :
      ∀ play : A.CompletePlayFromHistory current,
        play.EventuallyTerminates) :
    (ofTerminal (current := current) wins).IsTotal := by
  intro play
  rcases hterminates play with ⟨n, hterminal⟩
  rcases htotal ⟨play.historyAt n, hterminal⟩ with
    ⟨i, hwins⟩
  exact ⟨i, n, hterminal, hwins⟩

/-- Rebase a winning condition already defined on absolute tails at `current`
onto future root-relative plays.

The result retains the accumulated prefix in every future complete-history
clock. It does not replay root coordinates before `current`; use
`WinningCondition.afterHistory` for an arbitrary root winning condition. -/
def rebaseTailAt
    (current : A.HistoryFrom start)
    (W : A.WinningConditionFrom current N) :
    A.WinningCondition current.1 N :=
  fun i =>
    {future |
      CompletePlayFromHistory.splice current future ∈ W i}

@[simp]
theorem mem_rebaseTailAt_iff
    (current : A.HistoryFrom start)
    (W : A.WinningConditionFrom current N)
    (i : N) (future : A.CompletePlayFrom current.1) :
    future ∈ rebaseTailAt current W i ↔
      CompletePlayFromHistory.splice current future ∈ W i :=
  Iff.rfl

/-- A finite history decides player `i`'s objective when its entire complete
play cylinder lies inside `i`'s winning set. -/
def DecidesAt
    (W : A.WinningConditionFrom current N) (i : N)
    (history : A.HistoryFrom start) : Prop :=
  A.CompletePlayCylinderFrom current history ⊆ W i

/-- An explicit prefix-decision certificate for a winning condition.

`complete` says every complete play reaches a certified prefix. `persistent`
records that a certificate remains valid under arbitrary legal extension;
neither property is silently imposed on general winning conditions. -/
structure PrefixDecision
    (W : A.WinningConditionFrom current N) where
  /-- Certified finite winning histories for each player. -/
  winningHistories : N → Set (A.HistoryFrom start)
  /-- Every certified history decides the corresponding winning set. -/
  sound :
    ∀ (i : N) (history : A.HistoryFrom start),
      history ∈ winningHistories i →
        W.DecidesAt i history
  /-- Certification persists under every legal finite extension. -/
  persistent :
    ∀ (i : N) {ancestor descendant : A.HistoryFrom start},
      ancestor ∈ winningHistories i →
        A.IsExtensionFrom descendant ancestor →
        descendant ∈ winningHistories i
  /-- Every complete play reaches some certified winning history. -/
  complete :
    ∀ play : A.CompletePlayFromHistory current,
      ∃ (n : ℕ) (i : N),
        play.historyAt n ∈ winningHistories i

end WinningConditionFrom

namespace WinningCondition

variable {N : Type*}

/-- Restrict an arbitrary root winning condition after one accumulated
absolute history.

The resumed play includes every coordinate from the original root, so this
operation preserves root-clock and earlier-visit objectives. -/
def afterHistory
    (W : A.WinningCondition start N)
    (current : A.HistoryFrom start) :
    A.WinningCondition current.1 N :=
  fun i =>
    {future |
      CompletePlayFromHistory.resume current future ∈ W i}

@[simp]
theorem mem_afterHistory_iff
    (W : A.WinningCondition start N)
    (current : A.HistoryFrom start)
    (i : N) (future : A.CompletePlayFrom current.1) :
    future ∈ W.afterHistory current i ↔
      CompletePlayFromHistory.resume current future ∈ W i :=
  Iff.rfl

end WinningCondition

end Arena

namespace ControlledGame

variable {N : Type*}

/-- Player-indexed winning sets on the complete plays of a payoff-free
controlled game. -/
abbrev WinningCondition (G : ControlledGame N) :=
  G.toArena.WinningCondition G.init N

end ControlledGame

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- A pathwise robust winning strategy on the payoff-free observed carrier.

This is the canonical logical-game interface: it requires neither a utility
type nor a fabricated endpoint payoff. -/
def HasPathwiseWinningStrategy
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition)
    (i : N) (strategy : G.PureStrategy i) : Prop :=
  ∀ play : G.base.CompletePlay,
    G.IsCompatibleWithPlayerStrategy i strategy play →
      play ∈ W i

/-- Robust pathwise winning for a payoff-free quasistrategy. -/
def HasWinningQuasiStrategy
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition)
    (i : N) (strategy : G.QuasiStrategy i) : Prop :=
  ∀ play : G.base.CompletePlay,
    G.IsCompatibleWithQuasiStrategy i strategy play →
      play ∈ W i

end ExtensiveGame.ControlledObservedGame
