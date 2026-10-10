/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.History

/-!
# Complete legal plays

This module defines measure-free complete plays for the Arena model. A play is
rooted at one complete absolute history, takes exactly one legal action at each
nonterminal coordinate, and stutters forever after reaching a terminal
history. Thus finite and genuinely infinite play share one path type without
introducing a policy, probability law, countability, or measurability.

The path stores complete dependent histories rather than endpoint states.
Distinct action occurrences therefore remain distinct even when their endpoint
states merge.

## Main definitions

* `Arena.HistoryFrom.append` - attach a relative suffix to an absolute history.
* `Arena.IsChildFrom` - one-step extension between complete histories.
* `Arena.CompletePlayFromHistory` - a legal terminal-absorbing complete play
  starting at an arbitrary absolute history.
* `Arena.CompletePlayFrom` - the root-started specialization.
* `Arena.CompletePlayFromHistory.EventuallyTerminates` - eventual terminal
  absorption.
-/

namespace Arena

namespace HistoryFrom

variable {A : Arena} {start : A.State}

/-- Attach a history rooted at the endpoint of `baseHistory` to the complete
absolute history `baseHistory`. -/
def append (baseHistory : A.HistoryFrom start)
    (suffix : A.HistoryFrom baseHistory.1) :
    A.HistoryFrom start :=
  ⟨suffix.1, baseHistory.2.append suffix.2⟩

@[simp]
theorem append_fst (baseHistory : A.HistoryFrom start)
    (suffix : A.HistoryFrom baseHistory.1) :
    (baseHistory.append suffix).1 = suffix.1 :=
  rfl

@[simp]
theorem append_nil (baseHistory : A.HistoryFrom start) :
    baseHistory.append (HistoryFrom.nil A baseHistory.1) = baseHistory :=
  rfl

@[simp]
theorem append_snoc (baseHistory : A.HistoryFrom start)
    (suffix : A.HistoryFrom baseHistory.1)
    (action : A.Action suffix.1) :
    baseHistory.append
        ⟨A.next suffix.1 action, suffix.2.snoc action⟩ =
      ⟨A.next suffix.1 action,
        (baseHistory.2.append suffix.2).snoc action⟩ :=
  rfl

@[simp]
theorem append_length (baseHistory : A.HistoryFrom start)
    (suffix : A.HistoryFrom baseHistory.1) :
    (baseHistory.append suffix).2.length =
      baseHistory.2.length + suffix.2.length :=
  History.length_append baseHistory.2 suffix.2

end HistoryFrom

variable {A : Arena} {start : A.State}

/-- `child` extends `parent` by exactly one legal action occurrence.

The argument order is chosen for `Acc`: descendants appear in the first
argument and their parent in the second. -/
def IsChildFrom (A : Arena) {start : A.State}
    (child parent : A.HistoryFrom start) : Prop :=
  ∃ action : A.Action parent.1,
    child =
      ⟨A.next parent.1 action, parent.2.snoc action⟩

/-- `descendant` extends `ancestor` by a possibly empty legal suffix.

This occurrence-sensitive prefix relation compares complete histories, not
only their endpoint states. -/
def IsExtensionFrom (A : Arena) {start : A.State}
    (descendant ancestor : A.HistoryFrom start) : Prop :=
  ∃ suffix : A.HistoryFrom ancestor.1,
    descendant = ancestor.append suffix

namespace IsChildFrom

/-- Appending one action produces a child history. -/
theorem snoc (parent : A.HistoryFrom start)
    (action : A.Action parent.1) :
    A.IsChildFrom
      ⟨A.next parent.1 action, parent.2.snoc action⟩
      parent :=
  ⟨action, rfl⟩

/-- A child history has one more action occurrence than its parent. -/
theorem length_eq {child parent : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent) :
    child.2.length = parent.2.length + 1 := by
  rcases hchild with ⟨action, rfl⟩
  rfl

/-- A terminal history has no child. -/
theorem false_of_terminal {child parent : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent)
    (hterminal : A.IsTerminal parent.1) : False := by
  rcases hchild with ⟨action, _⟩
  exact hterminal.false action

/-- One-step extension is preserved when a relative history is attached to a
fixed absolute prefix. -/
theorem append {baseHistory : A.HistoryFrom start}
    {child parent : A.HistoryFrom baseHistory.1}
    (hchild : A.IsChildFrom child parent) :
    A.IsChildFrom
      (baseHistory.append child) (baseHistory.append parent) := by
  rcases hchild with ⟨action, rfl⟩
  exact ⟨action, rfl⟩

end IsChildFrom

namespace IsExtensionFrom

/-- Every complete history extends itself by the empty suffix. -/
theorem refl (history : A.HistoryFrom start) :
    A.IsExtensionFrom history history :=
  ⟨HistoryFrom.nil A history.1,
    (HistoryFrom.append_nil history).symm⟩

/-- A one-step child extends its parent. -/
theorem of_child {child parent : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent) :
    A.IsExtensionFrom child parent := by
  rcases hchild with ⟨action, rfl⟩
  exact
    ⟨⟨A.next parent.1 action,
        (History.nil : A.History parent.1 parent.1).snoc action⟩,
      rfl⟩

/-- Complete-history extension is transitive. -/
theorem trans {first second third : A.HistoryFrom start}
    (hsecond : A.IsExtensionFrom second first)
    (hthird : A.IsExtensionFrom third second) :
    A.IsExtensionFrom third first := by
  rcases hsecond with ⟨middleSuffix, rfl⟩
  rcases hthird with ⟨lastSuffix, rfl⟩
  refine ⟨middleSuffix.append lastSuffix, ?_⟩
  apply Sigma.ext
  · rfl
  · exact heq_of_eq
      (History.append_assoc first.2 middleSuffix.2 lastSuffix.2)

end IsExtensionFrom

/-- A complete legal play starting at an arbitrary complete absolute history.

At a nonterminal coordinate the next coordinate is one legal child history.
At a terminal coordinate the play stutters. The disjunction is constructive
and does not require decidable terminality. -/
structure CompletePlayFromHistory (A : Arena) {start : A.State}
    (current : A.HistoryFrom start) where
  /-- The complete absolute history at every event coordinate. -/
  historyAt : ℕ → A.HistoryFrom start
  /-- Coordinate zero is the supplied absolute history. -/
  historyAt_zero : historyAt 0 = current
  /-- Each coordinate either terminal-stutters or takes one legal action. -/
  step :
    ∀ n,
      (A.IsTerminal (historyAt n).1 ∧
          historyAt (n + 1) = historyAt n) ∨
        A.IsChildFrom (historyAt (n + 1)) (historyAt n)

/-- Complete plays from an Arena root. -/
abbrev CompletePlayFrom (A : Arena) (start : A.State) :=
  A.CompletePlayFromHistory (HistoryFrom.nil A start)

/-- The unbundled legality predicate for a terminal-absorbing history path.

This is the support-level interface used by probability laws on the ambient
function space. Bundled `CompletePlayFromHistory` values and almost-sure path
legality can therefore share one transition semantics without putting a
measurable-space structure on the bundled subtype. -/
def IsCompletePlayPathFrom (A : Arena) {start : A.State}
    (current : A.HistoryFrom start)
    (path : ℕ → A.HistoryFrom start) : Prop :=
  path 0 = current ∧
    ∀ n,
      (A.IsTerminal (path n).1 ∧ path (n + 1) = path n) ∨
        A.IsChildFrom (path (n + 1)) (path n)

namespace CompletePlayFromHistory

variable {current : A.HistoryFrom start}

@[ext]
theorem ext (first second : A.CompletePlayFromHistory current)
    (hat : first.historyAt = second.historyAt) :
    first = second := by
  cases first
  cases second
  cases hat
  rfl

/-- Heterogeneous extensionality for complete plays with propositionally
equal starting histories. -/
theorem hext {firstCurrent secondCurrent : A.HistoryFrom start}
    (first : A.CompletePlayFromHistory firstCurrent)
    (second : A.CompletePlayFromHistory secondCurrent)
    (hat : first.historyAt = second.historyAt) :
    HEq first second := by
  cases first with
  | mk firstHistory firstZero firstStep =>
      cases second with
      | mk secondHistory secondZero secondStep =>
          dsimp only at hat
          cases hat
          have hcurrent : firstCurrent = secondCurrent :=
            firstZero.symm.trans secondZero
          cases hcurrent
          rfl

/-- The underlying function of every bundled complete play satisfies the
unbundled legality predicate. -/
theorem isCompletePlayPathFrom
    (play : A.CompletePlayFromHistory current) :
    A.IsCompletePlayPathFrom current play.historyAt :=
  ⟨play.historyAt_zero, play.step⟩

/-- Bundle a function-space path after proving the common legality
predicate. -/
def ofPath (path : ℕ → A.HistoryFrom start)
    (hpath : A.IsCompletePlayPathFrom current path) :
    A.CompletePlayFromHistory current where
  historyAt := path
  historyAt_zero := hpath.1
  step := hpath.2

@[simp]
theorem ofPath_historyAt (path : ℕ → A.HistoryFrom start)
    (hpath : A.IsCompletePlayPathFrom current path) :
    (ofPath path hpath).historyAt = path :=
  rfl

/-- A play stutters at the next coordinate after reaching a terminal
history. -/
theorem at_succ_eq_of_terminal
    (play : A.CompletePlayFromHistory current) (n : ℕ)
    (hterminal : A.IsTerminal (play.historyAt n).1) :
    play.historyAt (n + 1) = play.historyAt n := by
  rcases play.step n with hstutter | hchild
  · exact hstutter.2
  · exact (hchild.false_of_terminal hterminal).elim

/-- Before termination, the next coordinate is a one-action child. -/
theorem isChild_at_succ_of_not_terminal
    (play : A.CompletePlayFromHistory current) (n : ℕ)
    (hnonterminal : ¬ A.IsTerminal (play.historyAt n).1) :
    A.IsChildFrom
      (play.historyAt (n + 1)) (play.historyAt n) := by
  rcases play.step n with hstutter | hchild
  · exact (hnonterminal hstutter.1).elim
  · exact hchild

/-- Before termination, complete-history length increases by exactly one. -/
theorem length_at_succ_of_not_terminal
    (play : A.CompletePlayFromHistory current) (n : ℕ)
    (hnonterminal : ¬ A.IsTerminal (play.historyAt n).1) :
    (play.historyAt (n + 1)).2.length =
      (play.historyAt n).2.length + 1 :=
  (play.isChild_at_succ_of_not_terminal n hnonterminal).length_eq

/-- Once a play reaches a terminal history, every later coordinate is the same
complete history. -/
theorem at_add_eq_of_terminal
    (play : A.CompletePlayFromHistory current) (n : ℕ)
    (hterminal : A.IsTerminal (play.historyAt n).1) :
    ∀ k, play.historyAt (n + k) = play.historyAt n
  | 0 => by simp
  | k + 1 => by
      have ih := play.at_add_eq_of_terminal n hterminal k
      have hterminal' :
          A.IsTerminal (play.historyAt (n + k)).1 := by
        rw [ih]
        exact hterminal
      rw [← Nat.add_assoc,
        play.at_succ_eq_of_terminal (n + k) hterminal']
      exact ih

/-- Any two terminal coordinates of one complete play carry the same complete
history. -/
theorem historyAt_eq_of_terminal
    (play : A.CompletePlayFromHistory current)
    {first second : ℕ}
    (hfirst : A.IsTerminal (play.historyAt first).1)
    (hsecond : A.IsTerminal (play.historyAt second).1) :
    play.historyAt first = play.historyAt second := by
  rcases Nat.le_total first second with hle | hle
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (play.at_add_eq_of_terminal first hfirst offset).symm
  · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact play.at_add_eq_of_terminal second hsecond offset

/-- Every coordinate of a complete play extends its initial absolute
history. -/
theorem isExtensionFrom_historyAt
    (play : A.CompletePlayFromHistory current) :
    ∀ n, A.IsExtensionFrom (play.historyAt n) current
  | 0 => by
      rw [play.historyAt_zero]
      exact IsExtensionFrom.refl current
  | n + 1 => by
      have hprefix := play.isExtensionFrom_historyAt n
      rcases play.step n with hstutter | hchild
      · rw [hstutter.2]
        exact hprefix
      · exact hprefix.trans (IsExtensionFrom.of_child hchild)

/-- A complete play has eventually terminated when one coordinate is
terminal. -/
def EventuallyTerminates
    (play : A.CompletePlayFromHistory current) : Prop :=
  ∃ n, A.IsTerminal (play.historyAt n).1

/-- A genuinely infinite play never reaches a terminal history. -/
def NeverTerminates
    (play : A.CompletePlayFromHistory current) : Prop :=
  ∀ n, ¬ A.IsTerminal (play.historyAt n).1

/-- A never-terminating play is not eventually terminating. -/
theorem not_eventuallyTerminates_of_neverTerminates
    {play : A.CompletePlayFromHistory current}
    (hinfinite : play.NeverTerminates) :
    ¬ play.EventuallyTerminates := by
  rintro ⟨n, hterminal⟩
  exact hinfinite n hterminal

/-- Dropping an initial segment produces a complete play rooted at the
retained absolute history. -/
def drop (play : A.CompletePlayFromHistory current) (offset : ℕ) :
    A.CompletePlayFromHistory (play.historyAt offset) where
  historyAt n := play.historyAt (offset + n)
  historyAt_zero := by simp
  step n := by
    simpa [Nat.add_assoc] using play.step (offset + n)

@[simp]
theorem drop_at (play : A.CompletePlayFromHistory current)
    (offset n : ℕ) :
    (play.drop offset).historyAt n =
      play.historyAt (offset + n) :=
  rfl

/-- A terminal current history has the unique constant complete play. -/
def stutter (current : A.HistoryFrom start)
    (hterminal : A.IsTerminal current.1) :
    A.CompletePlayFromHistory current where
  historyAt _ := current
  historyAt_zero := rfl
  step _ := Or.inl ⟨hterminal, rfl⟩

@[simp]
theorem stutter_at (current : A.HistoryFrom start)
    (hterminal : A.IsTerminal current.1) (n : ℕ) :
    (stutter current hterminal).historyAt n = current :=
  rfl

/-- Attach a root-relative future play to an absolute base history. -/
def splice (baseHistory : A.HistoryFrom start)
    (future : A.CompletePlayFrom baseHistory.1) :
    A.CompletePlayFromHistory baseHistory where
  historyAt n := baseHistory.append (future.historyAt n)
  historyAt_zero := by
    rw [future.historyAt_zero]
    exact HistoryFrom.append_nil baseHistory
  step n := by
    rcases future.step n with hstutter | hchild
    · exact Or.inl
        ⟨hstutter.1,
          congrArg (HistoryFrom.append baseHistory) hstutter.2⟩
    · exact Or.inr hchild.append

@[simp]
theorem splice_at (baseHistory : A.HistoryFrom start)
    (future : A.CompletePlayFrom baseHistory.1) (n : ℕ) :
    (splice baseHistory future).historyAt n =
      baseHistory.append (future.historyAt n) :=
  rfl

/-- Prepend one legal child transition to a complete play.

The supplied play begins at `child`; the result begins one coordinate earlier
at `parent` and then follows the supplied play exactly. -/
def prependChild {parent child : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent)
    (play : A.CompletePlayFromHistory child) :
    A.CompletePlayFromHistory parent where
  historyAt
    | 0 => parent
    | n + 1 => play.historyAt n
  historyAt_zero := rfl
  step
    | 0 => by
        change
          (A.IsTerminal parent.1 ∧ play.historyAt 0 = parent) ∨
            A.IsChildFrom (play.historyAt 0) parent
        rw [play.historyAt_zero]
        exact Or.inr hchild
    | n + 1 => by
        simpa [Nat.add_assoc] using play.step n

@[simp]
theorem prependChild_at_zero {parent child : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent)
    (play : A.CompletePlayFromHistory child) :
    (prependChild hchild play).historyAt 0 = parent :=
  rfl

@[simp]
theorem prependChild_at_succ {parent child : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent)
    (play : A.CompletePlayFromHistory child) (n : ℕ) :
    (prependChild hchild play).historyAt (n + 1) =
      play.historyAt n :=
  rfl

/-- Prepend every action occurrence of a finite absolute history to a complete
play beginning at that history.

Unlike `splice`, this reconstructs the coordinates from the Arena root through
the supplied current history. -/
def prependHistory :
    {finish : A.State} →
      (path : A.History start finish) →
      A.CompletePlayFromHistory ⟨finish, path⟩ →
      A.CompletePlayFrom start
  | _, .nil, play => play
  | _, .snoc path action, play =>
      prependHistory path
        (prependChild
          (IsChildFrom.snoc ⟨_, path⟩ action)
          play)

/-- After the prepended finite prefix, `prependHistory` follows the supplied
tail play with the expected coordinate shift. -/
@[simp]
theorem prependHistory_at_add
    {finish : A.State} (path : A.History start finish)
    (play : A.CompletePlayFromHistory ⟨finish, path⟩)
    (n : ℕ) :
    (prependHistory path play).historyAt (path.length + n) =
      play.historyAt n := by
  induction path generalizing n with
  | nil =>
      simp [prependHistory]
  | @snoc middle path action ih =>
      simpa [prependHistory, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ih
          (prependChild
            (IsChildFrom.snoc ⟨middle, path⟩ action)
            play)
          (n + 1)

/-- A complete tail packaged together with its absolute starting history. -/
abbrev CompleteTail (A : Arena) (start : A.State) :=
  Σ current : A.HistoryFrom start,
    A.CompletePlayFromHistory current

/-- Reattach a packaged absolute tail to the Arena root. -/
def reattachTail (tail : CompleteTail A start) :
    A.CompletePlayFrom start :=
  prependHistory tail.1.2 tail.2

/-- Package the tail of a root play at one coordinate. -/
def droppedTail (play : A.CompletePlayFrom start) (n : ℕ) :
    CompleteTail A start :=
  ⟨play.historyAt n, play.drop n⟩

/-- Reattaching across a child is definitionally the same as first prepending
that child to the packaged tail. -/
theorem reattachTail_child
    {parent child : A.HistoryFrom start}
    (hchild : A.IsChildFrom child parent)
    (tail : A.CompletePlayFromHistory child) :
    reattachTail ⟨child, tail⟩ =
      reattachTail ⟨parent, prependChild hchild tail⟩ := by
  rcases hchild with ⟨action, rfl⟩
  rfl

/-- Dropping at a terminal coordinate leaves the unique constant tail. -/
theorem drop_eq_stutter_of_terminal
    (play : A.CompletePlayFromHistory current) (offset : ℕ)
    (hterminal : A.IsTerminal (play.historyAt offset).1) :
    play.drop offset =
      stutter (play.historyAt offset) hterminal := by
  apply CompletePlayFromHistory.ext
  funext n
  exact play.at_add_eq_of_terminal offset hterminal n

/-- A dropped tail can be reattached across the immediately preceding child
transition. -/
theorem prependChild_drop_succ
    (play : A.CompletePlayFromHistory current) (n : ℕ)
    (hchild :
      A.IsChildFrom (play.historyAt (n + 1)) (play.historyAt n)) :
    prependChild hchild (play.drop (n + 1)) =
      play.drop n := by
  apply CompletePlayFromHistory.ext
  funext k
  cases k with
  | zero =>
      simp [CompletePlayFromHistory.drop,
        CompletePlayFromHistory.prependChild]
  | succ k =>
      simp only [prependChild_at_succ, drop_at]
      congr 1
      omega

/-- Replaying the accumulated history and then following the dropped tail
reconstructs the original root play.

This remains true when `n` lies after an earlier terminal coordinate: the
stored history has then stopped growing and both tails stutter. -/
theorem prependHistory_drop
    (play : A.CompletePlayFrom start) :
    ∀ n,
      prependHistory (play.historyAt n).2 (play.drop n) = play
  | 0 => by
      change reattachTail (droppedTail play 0) = play
      have htail :
          droppedTail play 0 =
            ⟨HistoryFrom.nil A start, play⟩ := by
        apply Sigma.ext play.historyAt_zero
        apply CompletePlayFromHistory.hext
        funext k
        simp [droppedTail, CompletePlayFromHistory.drop]
      rw [htail]
      rfl
  | n + 1 => by
      rcases play.step n with hstutter | hchild
      · change reattachTail (droppedTail play (n + 1)) = play
        have htail :
            droppedTail play (n + 1) =
              droppedTail play n := by
          apply Sigma.ext hstutter.2
          apply CompletePlayFromHistory.hext
          funext k
          simp only [droppedTail, drop_at]
          rw [show n + 1 + k = n + (k + 1) by omega,
            play.at_add_eq_of_terminal n hstutter.1 (k + 1),
            play.at_add_eq_of_terminal n hstutter.1 k]
        rw [htail]
        exact play.prependHistory_drop n
      · change reattachTail (droppedTail play (n + 1)) = play
        simp only [droppedTail]
        rw [reattachTail_child hchild (play.drop (n + 1))]
        change
          prependHistory (play.historyAt n).2
              (prependChild hchild (play.drop (n + 1))) =
            play
        rw [play.prependChild_drop_succ n hchild]
        exact play.prependHistory_drop n

/-- A root play that has reached a terminal history is the canonical replay
of that finite history followed by terminal stuttering. -/
theorem prependHistory_stutter_eq_of_terminal
    (play : A.CompletePlayFrom start) (n : ℕ)
    (hterminal : A.IsTerminal (play.historyAt n).1) :
    prependHistory (play.historyAt n).2
        (stutter (play.historyAt n) hterminal) =
      play := by
  rw [← play.drop_eq_stutter_of_terminal n hterminal]
  exact play.prependHistory_drop n

/-- Resume a root-relative future after one accumulated absolute history,
reconstructing a complete play from the original root.

Coordinates through `current.2.length` replay the accumulated prefix. Later
coordinates are the absolute splice of the supplied future. -/
def resume (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) :
    A.CompletePlayFrom start :=
  prependHistory current.2 (splice current future)

/-- Resuming preserves the original root coordinate. -/
@[simp]
theorem resume_at_zero (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) :
    (resume current future).historyAt 0 =
      HistoryFrom.nil A start :=
  (resume current future).historyAt_zero

/-- The resumed play reaches `current` at exactly the accumulated history
length. -/
@[simp]
theorem resume_at_length (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) :
    (resume current future).historyAt current.2.length = current := by
  rw [show current.2.length = current.2.length + 0 by omega,
    resume, prependHistory_at_add, splice_at, future.historyAt_zero,
    HistoryFrom.append_nil]

/-- The tail of a resumed root play is exactly the absolute splice of the
future play. -/
@[simp]
theorem resume_at_add (current : A.HistoryFrom start)
    (future : A.CompletePlayFrom current.1) (n : ℕ) :
    (resume current future).historyAt
        (current.2.length + n) =
      current.append (future.historyAt n) := by
  rw [resume, prependHistory_at_add, splice_at]

end CompletePlayFromHistory

end Arena

namespace ControlledGame

variable {N : Type*}

/-- Complete legal histories of a payoff-free controlled game. -/
abbrev History (G : ControlledGame N) :=
  G.toArena.HistoryFrom G.init

/-- Complete terminal-absorbing plays of a payoff-free controlled game. -/
abbrev CompletePlay (G : ControlledGame N) :=
  G.toArena.CompletePlayFrom G.init

/-- Complete legal plays after one accumulated absolute history in a
payoff-free controlled game. -/
abbrev CompletePlayFromHistory (G : ControlledGame N)
    (current : G.History) :=
  G.toArena.CompletePlayFromHistory current

end ControlledGame
