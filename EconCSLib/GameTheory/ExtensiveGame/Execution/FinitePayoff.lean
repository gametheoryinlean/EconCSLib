/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel

/-!
# Executable finite-horizon EFG payoffs

This module evaluates rational observables directly on executable finite
history laws. It does not construct a measure or an infinite path. Payoffs may
inspect the complete accumulated Arena history, a complete state prefix, or a
complete action-recording event prefix; merged endpoint states therefore do
not erase route-dependent payoffs.

The stopped variants assign zero at a horizon that still ends at a
nonterminal state. This convention matches the analytic stopped-utility
layer, while remaining an exact rational computation. Terminal decisions are
explicit typeclass inputs and are not recovered by classical choice.

## Main definitions

* `Arena.StochasticHistoryPolicy.expectedHistoryPayoffFrom` and
  `stoppedExpectedPayoffFrom`;
* state/event `KernelArena` history-policy prefix expectations;
* stopped state/event prefix expectations;
* exact preservation of expectations when event histories forget actions.
-/

namespace Arena.StochasticHistoryPolicy

variable {A : Arena} {start : A.State}

/-- Exact rational expectation of a complete-history observable after a
bounded stochastic execution. -/
def expectedHistoryPayoffFrom
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (payoff : A.HistoryFrom start → ℚ) : ℚ :=
  (A.stochasticHistoryLawFrom policy current fuel).expectRat payoff

/-- Exact rational stopped payoff after bounded stochastic execution.
Nonterminal histories at the requested horizon contribute zero. -/
def stoppedExpectedPayoffFrom
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (payoff : A.HistoryFrom start → ℚ) : ℚ :=
  policy.expectedHistoryPayoffFrom current fuel fun history =>
    if A.IsTerminal history.1 then payoff history else 0

/-- A continuation already at a terminal history retains its payoff at every
fuel, including zero. -/
@[simp]
theorem stoppedExpectedPayoffFrom_of_terminal
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (fuel : ℕ)
    (payoff : A.HistoryFrom start → ℚ)
    (hterminal : A.IsTerminal current.1) :
    policy.stoppedExpectedPayoffFrom current fuel payoff = payoff current := by
  rw [stoppedExpectedPayoffFrom, expectedHistoryPayoffFrom,
    A.stochasticHistoryLawFrom_of_terminal policy current hterminal]
  simp [hterminal]

end Arena.StochasticHistoryPolicy

namespace KernelArena.StateHistoryPolicy

variable {A : KernelArena}

/-- Exact rational expectation of an observable on the complete state prefix
produced after `steps` transitions. -/
def expectedPrefixValueFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (value : A.StatePrefix (start + steps) → ℚ) : ℚ :=
  (policy.prefixLawFrom start initialPrefix steps).expectRat value

/-- Exact rational stopped value on state prefixes. Prefixes whose latest
state is still nonterminal at the requested horizon contribute zero. -/
def stoppedExpectedValueFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (payoff : A.StatePrefix (start + steps) → ℚ) : ℚ :=
  policy.expectedPrefixValueFrom start initialPrefix steps fun history =>
    if IsEmpty (A.Action history.latest) then payoff history else 0

@[simp]
theorem expectedPrefixValueFrom_zero
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (value : A.StatePrefix (start + 0) → ℚ) :
    policy.expectedPrefixValueFrom start initialPrefix 0 value =
      value initialPrefix := by
  simp [expectedPrefixValueFrom]

end KernelArena.StateHistoryPolicy

namespace KernelArena.EventHistoryPolicy

variable {A : KernelArena}

/-- Exact rational expectation of an observable on the complete
action-recording event prefix produced after `steps` transitions. -/
def expectedPrefixValueFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (value : A.EventPrefix (start + steps) → ℚ) : ℚ :=
  (policy.prefixLawFrom start initialPrefix steps).expectRat value

/-- Exact rational stopped value on event prefixes. Prefixes whose latest
state is still nonterminal at the requested horizon contribute zero. -/
def stoppedExpectedValueFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (payoff : A.EventPrefix (start + steps) → ℚ) : ℚ :=
  policy.expectedPrefixValueFrom start initialPrefix steps fun history =>
    if IsEmpty (A.Action history.latestState) then payoff history else 0

@[simp]
theorem expectedPrefixValueFrom_zero
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (value : A.EventPrefix (start + 0) → ℚ) :
    policy.expectedPrefixValueFrom start initialPrefix 0 value =
      value initialPrefix := by
  simp [expectedPrefixValueFrom]

/-- Recording selected actions does not change the expected value of an
observable that depends only on the state prefix. -/
theorem toEventHistoryPolicy_expectedPrefixValueFrom_states
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (value : A.StatePrefix (start + steps) → ℚ) :
    policy.toEventHistoryPolicy.expectedPrefixValueFrom
        start initialPrefix steps (fun history => value history.states) =
      policy.expectedPrefixValueFrom
        start initialPrefix.states steps value := by
  unfold KernelArena.EventHistoryPolicy.expectedPrefixValueFrom
    KernelArena.StateHistoryPolicy.expectedPrefixValueFrom
  rw [← toEventHistoryPolicy_prefixLawFrom_map_states
    policy start initialPrefix steps]
  rw [FiniteLaw.expectRat_map]
  rfl

/-- The stopped-value convention is also preserved when action occurrences
are forgotten. -/
theorem toEventHistoryPolicy_stoppedExpectedValueFrom_states
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (payoff : A.StatePrefix (start + steps) → ℚ) :
    policy.toEventHistoryPolicy.stoppedExpectedValueFrom
        start initialPrefix steps (fun history => payoff history.states) =
      policy.stoppedExpectedValueFrom
        start initialPrefix.states steps payoff := by
  unfold stoppedExpectedValueFrom
  simpa only [EventPrefix.latest_states] using
    toEventHistoryPolicy_expectedPrefixValueFrom_states
      policy start initialPrefix steps
      (fun history =>
        if IsEmpty (A.Action history.latest) then payoff history else 0)

end KernelArena.EventHistoryPolicy
