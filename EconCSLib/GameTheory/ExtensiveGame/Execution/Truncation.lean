/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff

/-!
# Exact finite truncation and horizon search

This module computes stopped rational payoff estimates and unfinished-mass
error radii from bounded Arena execution. A budgeted search is total and
returns `none` when no tested horizon meets the tolerance. An unbounded least
horizon requires an explicit existence proof; analytic almost-sure termination
results may supply that proof downstream without entering the runtime data.

All numerical operations use exact rationals. The module makes no claim that
almost-sure termination supplies a uniform termination bound, a convergence
rate, or finite expected hitting time. Zero tolerance is accepted only when a
finite budget or an explicit existence proof makes its operational meaning
clear.
-/

namespace Arena

variable {A : Arena} {start : A.State}

/-- Exact mass of histories still nonterminal after a bounded execution. -/
def unfinishedMass
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (steps : ℕ) : ℚ≥0 :=
  (A.stochasticHistoryLawFrom policy current steps).eventMass
    (fun history => decide (¬ A.IsTerminal history.1))

namespace StochasticHistoryPolicy

variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- Rational stopped-payoff center and nonnegative rational error radius.
Unfinished histories contribute zero to the center and their exact mass times
`bound` to the radius. -/
def truncationEstimate (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (payoff : A.HistoryFrom start → ℚ)
    (bound : ℚ≥0) (horizon : ℕ) : ℚ × ℚ≥0 :=
  (policy.stoppedExpectedPayoffFrom current horizon payoff,
    bound * Arena.unfinishedMass policy current horizon)

/-- Search horizons `0, ..., budget - 1` for the first radius within the
requested tolerance. The budget counts candidate horizons, including zero. -/
def searchTruncationHorizon (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0)
    (budget : ℕ) : Option ℕ :=
  (List.range budget).find? fun horizon =>
    decide (bound * Arena.unfinishedMass policy current horizon ≤ tolerance)

/-- Return the first budgeted horizon together with its exact center and
radius. -/
def searchTruncation (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (payoff : A.HistoryFrom start → ℚ)
    (bound tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × ℚ × ℚ≥0) :=
  (policy.searchTruncationHorizon current bound tolerance budget).map
    fun horizon => (horizon, policy.truncationEstimate current payoff bound horizon)

/-- A successful budgeted search stays inside its budget and meets the exact
rational tolerance. -/
theorem searchTruncationHorizon_sound
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0)
    (budget horizon : ℕ)
    (hsearch : policy.searchTruncationHorizon current bound tolerance budget =
      some horizon) :
    horizon < budget ∧
      bound * Arena.unfinishedMass policy current horizon ≤ tolerance := by
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some hsearch), ?_⟩
  have hp := List.find?_some
    (p := fun n =>
      decide (bound * Arena.unfinishedMass policy current n ≤ tolerance)) hsearch
  exact of_decide_eq_true hp

/-- Exhaustion means exactly that every tested radius exceeds the tolerance;
it makes no claim about later horizons. -/
theorem searchTruncationHorizon_eq_none_iff
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0)
    (budget : ℕ) :
    policy.searchTruncationHorizon current bound tolerance budget = none ↔
      ∀ horizon < budget,
        tolerance < bound * Arena.unfinishedMass policy current horizon := by
  simp [searchTruncationHorizon, List.find?_eq_none]

/-- Every returned tuple contains the computed estimate at the selected
horizon and a radius within tolerance. -/
theorem searchTruncation_sound
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (payoff : A.HistoryFrom start → ℚ)
    (bound tolerance : ℚ≥0) (budget horizon : ℕ)
    (center : ℚ) (radius : ℚ≥0)
    (hsearch : policy.searchTruncation current payoff bound tolerance budget =
      some (horizon, center, radius)) :
    horizon < budget ∧
      policy.truncationEstimate current payoff bound horizon =
        (center, radius) ∧
      radius ≤ tolerance := by
  obtain ⟨selected, hselected, heq⟩ := Option.map_eq_some_iff.mp hsearch
  have hsound := policy.searchTruncationHorizon_sound
    current bound tolerance budget selected hselected
  cases heq
  exact ⟨hsound.1, rfl, hsound.2⟩

/-- Compute the least acceptable horizon when a caller proves that one exists.
The proof may come from a structural bound, a finite-chain solver, or an
analytic convergence theorem; it is erased from the executed search. -/
def leastTruncationHorizon (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0)
    (hexists : ∃ horizon,
      bound * Arena.unfinishedMass policy current horizon ≤ tolerance) : ℕ :=
  Nat.find hexists

/-- The unbounded search returns the least horizon meeting the tolerance. -/
theorem leastTruncationHorizon_spec
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (bound tolerance : ℚ≥0)
    (hexists : ∃ horizon,
      bound * Arena.unfinishedMass policy current horizon ≤ tolerance) :
    bound * Arena.unfinishedMass policy current
        (policy.leastTruncationHorizon current bound tolerance hexists) ≤
        tolerance ∧
      ∀ earlier < policy.leastTruncationHorizon current bound tolerance hexists,
        tolerance < bound * Arena.unfinishedMass policy current earlier := by
  unfold leastTruncationHorizon
  exact ⟨Nat.find_spec hexists,
    fun _ hlt => lt_of_not_ge (Nat.find_min hexists hlt)⟩

/-- Compute the least-horizon estimate from an explicit existence proof. -/
def approximateAtLeastHorizon (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (payoff : A.HistoryFrom start → ℚ)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ horizon,
      bound * Arena.unfinishedMass policy current horizon ≤ tolerance) :
    ℕ × ℚ × ℚ≥0 :=
  let horizon := policy.leastTruncationHorizon current bound tolerance hexists
  (horizon, policy.truncationEstimate current payoff bound horizon)

end StochasticHistoryPolicy
end Arena
