/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution
import EconCSLib.Math.Probability.FiniteLaw

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution

Finite stochastic execution on an `Arena`.

A `StochasticHistoryPolicy` assigns an executable exact `FiniteLaw` at each
nonterminal complete history. `stochasticHistoryLawFrom` executes that policy
for bounded fuel, stopping early at terminal histories.  Unlike a mere support
relation, the result retains the complete probability law on histories.

The positive-atom theorem `exists_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom`
shows that every positive-probability result genuinely extends the input
history by a finite target fragment.  This is the bridge needed to combine
finite-law coupling with weak/stuttering Arena simulation.
-/

namespace Arena

variable (A : Arena) (start : A.State)

/-- A normalized, history-dependent stochastic action policy. -/
def StochasticHistoryPolicy : Type _ :=
  (h : A.HistoryFrom start) →
    ¬ A.IsTerminal h.1 →
    FiniteLaw (A.Action h.1)

variable {A start}

/-- Execute a stochastic history policy for bounded fuel, stopping at a
terminal history. -/
def stochasticHistoryLawFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    ℕ → FiniteLaw (A.HistoryFrom start)
  | 0 => FiniteLaw.pure current
  | fuel + 1 =>
      if hterminal : A.IsTerminal current.1 then
        FiniteLaw.pure current
      else
        (policy current hterminal).bind fun action =>
          stochasticHistoryLawFrom policy
            ⟨A.next current.1 action, current.2.snoc action⟩ fuel

@[simp]
theorem stochasticHistoryLawFrom_zero
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    A.stochasticHistoryLawFrom policy current 0 = FiniteLaw.pure current :=
  rfl

@[simp]
theorem stochasticHistoryLawFrom_succ_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (hterminal : A.IsTerminal current.1) :
    A.stochasticHistoryLawFrom policy current (fuel + 1) =
      FiniteLaw.pure current := by
  simp [stochasticHistoryLawFrom, hterminal]

@[simp]
theorem stochasticHistoryLawFrom_succ_of_not_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (hnonterminal : ¬ A.IsTerminal current.1) :
    A.stochasticHistoryLawFrom policy current (fuel + 1) =
      (policy current hnonterminal).bind fun action =>
        A.stochasticHistoryLawFrom policy
          ⟨A.next current.1 action, current.2.snoc action⟩ fuel := by
  simp [stochasticHistoryLawFrom, hnonterminal]

/-- Once execution is terminal, every additional fuel bound returns the same
Dirac history law. -/
theorem stochasticHistoryLawFrom_of_terminal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (hterminal : A.IsTerminal current.1) :
    ∀ fuel,
      A.stochasticHistoryLawFrom policy current fuel =
        FiniteLaw.pure current := by
  intro fuel
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      exact A.stochasticHistoryLawFrom_succ_of_terminal
        policy current fuel hterminal

/-- Finite stochastic execution composes by addition of fuel. -/
theorem stochasticHistoryLawFrom_add
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (first second : ℕ) :
    A.stochasticHistoryLawFrom policy current (first + second) =
      (A.stochasticHistoryLawFrom policy current first).bind
        (fun middle =>
          A.stochasticHistoryLawFrom policy middle second) := by
  induction first generalizing current with
  | zero =>
      simp
  | succ first ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [Nat.succ_add]
        rw [A.stochasticHistoryLawFrom_of_terminal
          policy current hterminal]
        rw [A.stochasticHistoryLawFrom_succ_of_terminal
          policy current first hterminal]
        simp [A.stochasticHistoryLawFrom_of_terminal
          policy current hterminal]
      · rw [Nat.succ_add]
        rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
          policy current (first + second) hterminal]
        rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
          policy current first hterminal]
        rw [FiniteLaw.bind_bind]
        apply congrArg
          (fun continuation =>
            (policy current hterminal).bind continuation)
        funext action
        exact ih
          ⟨A.next current.1 action, current.2.snoc action⟩

/-! ### Deterministic prefixes of stochastic execution -/

/-- A stochastic policy agrees with a deterministic history policy by Dirac
laws along the next `fuel` steps from `current`.

The predicate follows the realized deterministic path rather than imposing
purity at unrelated histories. -/
def StochasticHistoryPolicy.IsPureFor
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (stochastic : A.StochasticHistoryPolicy start)
    (deterministic : A.HistoryPolicy start) :
    (current : A.HistoryFrom start) → ℕ → Prop
  | _, 0 => True
  | current, fuel + 1 =>
      if hterminal : A.IsTerminal current.1 then
        True
      else
        stochastic current hterminal =
            FiniteLaw.pure (deterministic current hterminal) ∧
          stochastic.IsPureFor deterministic
            ⟨A.next current.1 (deterministic current hterminal),
              current.2.snoc (deterministic current hterminal)⟩
            fuel

/-- A stochastic execution whose next `fuel` action laws are Dirac is exactly
the Dirac law at the corresponding deterministic stopped history. -/
theorem stochasticHistoryLawFrom_eq_pure_stoppedHistoryFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (stochastic : A.StochasticHistoryPolicy start)
    (deterministic : A.HistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (hpure : stochastic.IsPureFor deterministic current fuel) :
    A.stochasticHistoryLawFrom stochastic current fuel =
      FiniteLaw.pure (A.stoppedHistoryFrom deterministic current fuel) := by
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hterminal : A.IsTerminal current.1
      · rw [A.stochasticHistoryLawFrom_succ_of_terminal
          stochastic current fuel hterminal]
        rw [A.stoppedHistoryFrom_succ_of_terminal
          deterministic current fuel hterminal]
      · have hpureStep :
            stochastic current hterminal =
              FiniteLaw.pure (deterministic current hterminal) := by
          have hpure' :
              stochastic current hterminal =
                  FiniteLaw.pure (deterministic current hterminal) ∧
                stochastic.IsPureFor deterministic
                  ⟨A.next current.1
                      (deterministic current hterminal),
                    current.2.snoc
                      (deterministic current hterminal)⟩
                  fuel := by
            simpa [StochasticHistoryPolicy.IsPureFor, hterminal] using
              hpure
          exact hpure'.1
        have hpureTail :
            stochastic.IsPureFor deterministic
              ⟨A.next current.1 (deterministic current hterminal),
                current.2.snoc (deterministic current hterminal)⟩
              fuel := by
          have hpure' :
              stochastic current hterminal =
                  FiniteLaw.pure (deterministic current hterminal) ∧
                stochastic.IsPureFor deterministic
                  ⟨A.next current.1
                      (deterministic current hterminal),
                    current.2.snoc
                      (deterministic current hterminal)⟩
                  fuel := by
            simpa [StochasticHistoryPolicy.IsPureFor, hterminal] using
              hpure
          exact hpure'.2
        rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
          stochastic current fuel hterminal]
        rw [A.stoppedHistoryFrom_succ_of_not_terminal
          deterministic current fuel hterminal]
        rw [hpureStep, FiniteLaw.pure_bind]
        exact ih _ hpureTail

/-- Every positive-probability execution result is obtained by appending a
finite valid Arena history to the input complete history. -/
theorem exists_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current endpoint : A.HistoryFrom start) :
    ∀ fuel,
      (A.stochasticHistoryLawFrom policy current fuel).HasPositiveAtom endpoint →
        ∃ suffix : A.History current.1 endpoint.1,
          endpoint.2 = current.2.append suffix := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      intro hsupport
      have heq : endpoint = current :=
        (FiniteLaw.hasPositiveAtom_pure_iff current endpoint).mp hsupport
      subst endpoint
      exact ⟨History.nil, rfl⟩
  | succ fuel ih =>
      intro hsupport
      by_cases hterminal : A.IsTerminal current.1
      · rw [A.stochasticHistoryLawFrom_succ_of_terminal
          policy current fuel hterminal] at hsupport
        have heq : endpoint = current :=
          (FiniteLaw.hasPositiveAtom_pure_iff current endpoint).mp hsupport
        subst endpoint
        exact ⟨History.nil, rfl⟩
      · rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
          policy current fuel hterminal] at hsupport
        obtain ⟨action, _, hendpoint⟩ :=
          (FiniteLaw.hasPositiveAtom_bind_iff
            (policy current hterminal)
            (fun action =>
              A.stochasticHistoryLawFrom policy
                ⟨A.next current.1 action, current.2.snoc action⟩ fuel)
            endpoint).mp hsupport
        obtain ⟨suffix, hsuffix⟩ :=
          ih
            (current :=
              ⟨A.next current.1 action, current.2.snoc action⟩)
            hendpoint
        refine
          ⟨(History.nil.snoc action).append suffix, ?_⟩
        calc
          endpoint.2 = (current.2.snoc action).append suffix := hsuffix
          _ = current.2.append
              ((History.nil.snoc action).append suffix) := by
                rw [← History.append_assoc]
                rfl

/-- With positive fuel and a nonterminal starting history, every
positive-probability result is reached by a nonempty suffix. -/
theorem exists_positive_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current endpoint : A.HistoryFrom start)
    (fuel : ℕ) (hfuel : 0 < fuel)
    (hnonterminal : ¬ A.IsTerminal current.1)
    (hsupport :
      (A.stochasticHistoryLawFrom policy current fuel).HasPositiveAtom endpoint) :
    ∃ suffix : A.History current.1 endpoint.1,
      0 < suffix.length ∧
      endpoint.2 = current.2.append suffix := by
  obtain ⟨remainingFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hfuel)
  rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
    policy current remainingFuel hnonterminal] at hsupport
  obtain ⟨action, _, hendpoint⟩ :=
    (FiniteLaw.hasPositiveAtom_bind_iff
      (policy current hnonterminal)
      (fun action =>
        A.stochasticHistoryLawFrom policy
          ⟨A.next current.1 action, current.2.snoc action⟩
          remainingFuel)
      endpoint).mp hsupport
  obtain ⟨suffix, hsuffix⟩ :=
    A.exists_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
      policy
      ⟨A.next current.1 action, current.2.snoc action⟩
      endpoint remainingFuel hendpoint
  refine
    ⟨(History.nil.snoc action).append suffix, ?_, ?_⟩
  · simp
  · calc
      endpoint.2 = (current.2.snoc action).append suffix := hsuffix
      _ = current.2.append
          ((History.nil.snoc action).append suffix) := by
            rw [← History.append_assoc]
            rfl

/-- The execution law is normalized at every fuel. -/
@[simp]
theorem stochasticHistoryLawFrom_normalized
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ) :
    FiniteLaw.totalWeight
        (A.stochasticHistoryLawFrom policy current fuel).atoms = 1 :=
  FiniteLaw.totalWeight_atoms _

end Arena
