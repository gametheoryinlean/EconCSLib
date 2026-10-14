/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Basic
import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

Terminal-aware, fuel-bounded execution for Arena histories.

The older `Arena.play` API takes a total chooser `(s : State) → Action s`.
Such a chooser cannot exist when terminal states have empty action types.  This
module instead uses a `HistoryPolicy`: an action is requested only together
with a proof that the current endpoint is nonterminal.  Execution stops
immediately at a terminal endpoint and otherwise appends exactly one typed
action to the accumulated history.

## Main definitions

* `Arena.HistoryPolicy` — a history-dependent action policy defined only at
  nonterminal endpoints.
* `Arena.stoppedHistoryFrom` — continue an accumulated history for at most the
  supplied fuel.
* `Arena.stoppedHistory` — execute from the empty history.
* `ExtensiveGame.stoppedPayoff` — a terminal payoff vector, returned only when
  execution actually reaches a terminal state.

## Main results

* `stoppedHistoryFrom_terminal` — terminal histories are fixed points.
* `stoppedHistoryFrom_add` — execution composes by addition of fuel.
* `stoppedHistoryFrom_terminal_or_length_eq` — a run either terminates or uses
  every available step.
* `stoppedHistoryFrom_add_of_terminal` — once stopped, additional fuel has no
  effect.
-/

namespace Arena

/-- A history-dependent policy that is queried only at nonterminal endpoints. -/
def HistoryPolicy (A : Arena) (start : A.State) : Type _ :=
  (h : A.HistoryFrom start) → ¬ A.IsTerminal h.1 → A.Action h.1

variable {A : Arena} {start : A.State}

/-- Continue an already accumulated history for at most `fuel` transitions.

At a terminal endpoint the history is returned unchanged.  At a nonterminal
endpoint the policy supplies one action, that action is appended, and execution
continues with one less unit of fuel. -/
def stoppedHistoryFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start)
    (current : A.HistoryFrom start) : ℕ → A.HistoryFrom start
  | 0 => current
  | fuel + 1 =>
      if hterminal : A.IsTerminal current.1 then
        current
      else
        let action := policy current hterminal
        stoppedHistoryFrom policy
          ⟨A.next current.1 action, current.2.snoc action⟩ fuel

/-- Execute a history policy from the empty history for at most `fuel` steps. -/
def stoppedHistory
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (fuel : ℕ) :
    A.HistoryFrom start :=
  stoppedHistoryFrom policy (HistoryFrom.nil A start) fuel

@[simp]
theorem stoppedHistoryFrom_zero
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    stoppedHistoryFrom policy current 0 = current := rfl

@[simp]
theorem stoppedHistoryFrom_succ_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (fuel : ℕ) (hterminal : A.IsTerminal current.1) :
    stoppedHistoryFrom policy current (fuel + 1) = current := by
  simp [stoppedHistoryFrom, hterminal]

theorem stoppedHistoryFrom_succ_of_not_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (fuel : ℕ) (hterminal : ¬ A.IsTerminal current.1) :
    stoppedHistoryFrom policy current (fuel + 1) =
      stoppedHistoryFrom policy
        ⟨A.next current.1 (policy current hterminal),
          current.2.snoc (policy current hterminal)⟩ fuel := by
  simp [stoppedHistoryFrom, hterminal]

/-- A terminal accumulated history is a fixed point for every fuel value. -/
theorem stoppedHistoryFrom_eq_self_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (hterminal : A.IsTerminal current.1) :
    ∀ fuel, stoppedHistoryFrom policy current fuel = current
  | 0 => rfl
  | fuel + 1 => stoppedHistoryFrom_succ_of_terminal policy current fuel hterminal

/-- Running for `first + second` steps is the same as running for `first`
steps and then continuing the resulting history for `second` more steps. -/
theorem stoppedHistoryFrom_add
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ) :
    stoppedHistoryFrom policy current (first + second) =
      stoppedHistoryFrom policy
        (stoppedHistoryFrom policy current first) second := by
  induction first generalizing current with
  | zero =>
      simp
  | succ first ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [Nat.succ_add]
        rw [stoppedHistoryFrom_succ_of_terminal policy current _ hterminal]
        rw [stoppedHistoryFrom_succ_of_terminal policy current first hterminal]
        exact
          (stoppedHistoryFrom_eq_self_of_terminal
            policy current hterminal second).symm
      · rw [Nat.succ_add]
        rw [stoppedHistoryFrom_succ_of_not_terminal policy current _ hterminal]
        rw [stoppedHistoryFrom_succ_of_not_terminal policy current first hterminal]
        exact ih
          ⟨A.next current.1 (policy current hterminal),
            current.2.snoc (policy current hterminal)⟩

/-- Execution never appends more actions than the supplied fuel. -/
theorem stoppedHistoryFrom_length_le
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ fuel,
      (stoppedHistoryFrom policy current fuel).2.length ≤
        current.2.length + fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      simp
  | succ fuel ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [stoppedHistoryFrom_succ_of_terminal policy current fuel hterminal]
        omega
      · rw [stoppedHistoryFrom_succ_of_not_terminal policy current fuel hterminal]
        have hle := ih
          ⟨A.next current.1 (policy current hterminal),
            current.2.snoc (policy current hterminal)⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

/-- A fuel-bounded run either reaches a terminal endpoint or appends exactly
one action for every available unit of fuel. -/
theorem stoppedHistoryFrom_terminal_or_length_eq
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start) :
    ∀ fuel,
      A.IsTerminal (stoppedHistoryFrom policy current fuel).1 ∨
        (stoppedHistoryFrom policy current fuel).2.length =
          current.2.length + fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      by_cases hterminal : A.IsTerminal current.1
      · exact Or.inl hterminal
      · exact Or.inr (by simp)
  | succ fuel ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [stoppedHistoryFrom_succ_of_terminal policy current fuel hterminal]
        exact Or.inl hterminal
      · rw [stoppedHistoryFrom_succ_of_not_terminal policy current fuel hterminal]
        rcases ih
            ⟨A.next current.1 (policy current hterminal),
              current.2.snoc (policy current hterminal)⟩ with hstopped | hlength
        · exact Or.inl hstopped
        · exact Or.inr (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength)

/-- Once a run has reached a terminal endpoint, adding more fuel cannot change
its result. -/
theorem stoppedHistoryFrom_add_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ)
    (hterminal :
      A.IsTerminal (stoppedHistoryFrom policy current first).1) :
    stoppedHistoryFrom policy current (first + second) =
      stoppedHistoryFrom policy current first := by
  rw [stoppedHistoryFrom_add]
  exact stoppedHistoryFrom_eq_self_of_terminal policy _ hterminal second

/-- Any two fuel bounds that both reach a terminal endpoint produce exactly
the same accumulated history.

This is the uniqueness fact needed to turn existential termination into a
well-defined total terminal-outcome semantics. -/
theorem stoppedHistoryFrom_eq_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (current : A.HistoryFrom start)
    (first second : ℕ)
    (hfirst : A.IsTerminal (stoppedHistoryFrom policy current first).1)
    (hsecond : A.IsTerminal (stoppedHistoryFrom policy current second).1) :
    stoppedHistoryFrom policy current first =
      stoppedHistoryFrom policy current second := by
  rcases Nat.le_total first second with hle | hle
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact
      (stoppedHistoryFrom_add_of_terminal
        policy current first extra hfirst).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact
      stoppedHistoryFrom_add_of_terminal
        policy current second extra hsecond

/-- From the empty history, a nonterminal result has length exactly `fuel`. -/
theorem stoppedHistory_terminal_or_length_eq
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (fuel : ℕ) :
    A.IsTerminal (stoppedHistory policy fuel).1 ∨
      (stoppedHistory policy fuel).2.length = fuel := by
  rcases stoppedHistoryFrom_terminal_or_length_eq policy
      (HistoryFrom.nil A start) fuel with hterminal | hlength
  · exact Or.inl hterminal
  · exact Or.inr (by simpa [stoppedHistory, HistoryFrom.nil] using hlength)

/-! ### Complete-play realization -/

/-- The terminal-aware finite executor at every fuel value forms one legal
terminal-absorbing complete play from the supplied absolute history. -/
def HistoryPolicy.completePlayFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start)
    (current : A.HistoryFrom start) :
    A.CompletePlayFromHistory current where
  historyAt fuel := stoppedHistoryFrom policy current fuel
  historyAt_zero := rfl
  step n := by
    rw [stoppedHistoryFrom_add policy current n 1]
    let reached := stoppedHistoryFrom policy current n
    change
      (A.IsTerminal reached.1 ∧
          stoppedHistoryFrom policy reached 1 = reached) ∨
        A.IsChildFrom
          (stoppedHistoryFrom policy reached 1) reached
    by_cases hterminal : A.IsTerminal reached.1
    · exact Or.inl
        ⟨hterminal,
          stoppedHistoryFrom_eq_self_of_terminal
            policy reached hterminal 1⟩
    · rw [stoppedHistoryFrom_succ_of_not_terminal
        policy reached 0 hterminal]
      exact Or.inr
        (IsChildFrom.snoc reached
          (policy reached hterminal))

/-- The complete play induced by a history policy from the empty history. -/
def HistoryPolicy.completePlay
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) :
    A.CompletePlayFrom start :=
  policy.completePlayFrom (HistoryFrom.nil A start)

@[simp]
theorem HistoryPolicy.completePlayFrom_historyAt
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ) :
    (policy.completePlayFrom current).historyAt fuel =
      stoppedHistoryFrom policy current fuel :=
  rfl

@[simp]
theorem HistoryPolicy.completePlay_historyAt
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.HistoryPolicy start) (fuel : ℕ) :
    policy.completePlay.historyAt fuel =
      stoppedHistory policy fuel :=
  rfl

end Arena

namespace ExtensiveGame

variable {N U : Type*}

/-- Return the terminal payoff vector reached by a stopped execution.

If the available fuel ends at a nonterminal state, return `none`; in
particular, arbitrary payoffs stored at nonterminal Arena states are never
reported as game outcomes. -/
def stoppedPayoff
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ) :
    Option (N → U) :=
  let result := G.toArena.stoppedHistory policy fuel
  if G.isTerminal result.1 then some (G.payoff result.1) else none

theorem stoppedPayoff_eq_some_of_terminal
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ)
    (hterminal :
      G.isTerminal (G.toArena.stoppedHistory policy fuel).1) :
    G.stoppedPayoff policy fuel =
      some (G.payoff (G.toArena.stoppedHistory policy fuel).1) := by
  simp [stoppedPayoff, hterminal]

theorem stoppedPayoff_eq_none_of_not_terminal
    (G : ExtensiveGame N U)
    [(s : G.State) → Decidable (G.isTerminal s)]
    (policy : G.toArena.HistoryPolicy G.init) (fuel : ℕ)
    (hterminal :
      ¬ G.isTerminal (G.toArena.stoppedHistory policy fuel).1) :
    G.stoppedPayoff policy fuel = none := by
  simp [stoppedPayoff, hterminal]

end ExtensiveGame
