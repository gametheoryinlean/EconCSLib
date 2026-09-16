/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff

/-!
# Exact finite truncation from complete kernel-arena prefixes

This module computes continuation truncations for finite rational
`KernelArena` history policies.  A continuation is specified by its absolute
starting time and a complete prefix at that time.  The existing
`prefixLawFrom` executors therefore retain the old states, retain selected
action occurrences in the event-history API, and invoke policies at the
absolute clock `start + steps`.

At every future horizon the module computes three exact quantities:

* the rational mass of prefixes whose latest state remains nonterminal;
* the stopped rational payoff center, with unfinished prefixes worth zero;
* the nonnegative radius `bound * unfinishedMass`.

Payoffs form an explicit dependent family because prefixes at distinct
horizons have distinct types.  Budgeted search tests horizons
`0, ..., budget - 1`.  An unbounded least horizon is exposed only when the
caller supplies a proof that an acceptable horizon exists.  All runtime data
remain finite and rational; this module imports neither measure theory nor the
analytic simulation layer.

## Analytic boundary

`Simulation.Equilibrium.FinitePayoff` already identifies a fixed-horizon
executable stopped expectation with the matching analytic partial trajectory
when an `AnalyticallyRealizedBy` certificate is supplied.  A theorem about an
observed game's original absolute-prefix continuation utility additionally
needs all of the following downstream adapters:

* realization of this finite event-history policy by the compiled analytic
  continuation policy;
* identification of this supplied `EventPrefix` with the observed model's
  canonical continuation prefix;
* factorization of the real path utility through a horizon-indexed rational
  prefix payoff, together with its uniform bound and terminal agreement.

Those adapters are presentation- and payoff-specific.  They are deliberately
not invented as data or assumptions in this measure-free algorithm module.
-/

namespace KernelArena

/-- A rational state-prefix payoff supplied separately at every future
horizon from absolute time `start`. -/
abbrev StateContinuationPayoff
    (A : KernelArena) (start : ℕ) :=
  (steps : ℕ) → A.StatePrefix (start + steps) → ℚ

/-- A rational action-recording event-prefix payoff supplied separately at
every future horizon from absolute time `start`. -/
abbrev EventContinuationPayoff
    (A : KernelArena) (start : ℕ) :=
  (steps : ℕ) → A.EventPrefix (start + steps) → ℚ

namespace StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

variable (policy : A.StateHistoryPolicy)

/-- Exact mass of state prefixes that remain nonterminal after `steps`
future transitions from the supplied complete prefix. -/
def unfinishedMassFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) : ℚ≥0 :=
  (policy.prefixLawFrom start initialPrefix steps).eventMass
    (fun history => decide (¬ IsEmpty (A.Action history.latest)))

/-- Exact stopped rational payoff from the supplied state prefix.  The
payoff at the selected horizon is used, and unfinished prefixes contribute
zero. -/
def stoppedCenterFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (payoff : A.StateContinuationPayoff start) (steps : ℕ) : ℚ :=
  policy.stoppedExpectedValueFrom
    start initialPrefix steps (payoff steps)

/-- Exact nonnegative truncation radius at one future horizon. -/
def truncationRadiusFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound : ℚ≥0) (steps : ℕ) : ℚ≥0 :=
  bound * policy.unfinishedMassFrom start initialPrefix steps

/-- Exact stopped center and unfinished-mass radius at one future horizon.
-/
def truncationEstimateFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (payoff : A.StateContinuationPayoff start)
    (bound : ℚ≥0) (steps : ℕ) : ℚ × ℚ≥0 :=
  (policy.stoppedCenterFrom start initialPrefix payoff steps,
    policy.truncationRadiusFrom start initialPrefix bound steps)

/-- Search future horizons `0, ..., budget - 1` for the first state-prefix
radius within `tolerance`.  The budget counts horizon zero. -/
def searchTruncationHorizonFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0) (budget : ℕ) : Option ℕ :=
  (List.range budget).find? fun steps =>
    decide
      (policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance)

/-- Return the first budgeted state-prefix horizon together with its exact
center and radius. -/
def searchTruncationFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (payoff : A.StateContinuationPayoff start)
    (bound tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × ℚ × ℚ≥0) :=
  (policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget).map fun steps =>
    (steps,
      policy.truncationEstimateFrom
        start initialPrefix payoff bound steps)

/-- A successful state-prefix horizon search stays inside its budget and
meets the exact rational tolerance. -/
theorem searchTruncationHorizonFrom_sound
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (hsearch : policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget = some steps) :
    steps < budget ∧
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance := by
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some hsearch), ?_⟩
  have hp := List.find?_some
    (p := fun horizon =>
      decide
        (policy.truncationRadiusFrom
          start initialPrefix bound horizon ≤ tolerance)) hsearch
  exact of_decide_eq_true hp

/-- A successful state-prefix search has rejected every earlier horizon. -/
theorem searchTruncationHorizonFrom_minimal
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (hsearch : policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget = some steps) :
    ∀ earlier < steps,
      tolerance <
        policy.truncationRadiusFrom start initialPrefix bound earlier := by
  have hfind := List.find?_range_eq_some.mp hsearch
  intro earlier hearlier
  have hfailed := hfind.2.2 earlier hearlier
  apply lt_of_not_ge
  simpa using hfailed

/-- Exhausting a state-prefix search means exactly that every tested horizon
fails.  It makes no claim about horizons beyond the budget. -/
theorem searchTruncationHorizonFrom_eq_none_iff
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0) (budget : ℕ) :
    policy.searchTruncationHorizonFrom
        start initialPrefix bound tolerance budget = none ↔
      ∀ steps < budget,
        tolerance <
          policy.truncationRadiusFrom start initialPrefix bound steps := by
  simp [searchTruncationHorizonFrom, List.find?_eq_none]

/-- Every returned state-prefix tuple contains the estimate at the selected
horizon and a radius within tolerance. -/
theorem searchTruncationFrom_sound
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (payoff : A.StateContinuationPayoff start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (center : ℚ) (radius : ℚ≥0)
    (hsearch : policy.searchTruncationFrom
      start initialPrefix payoff bound tolerance budget =
        some (steps, center, radius)) :
    steps < budget ∧
      policy.truncationEstimateFrom
          start initialPrefix payoff bound steps = (center, radius) ∧
      radius ≤ tolerance := by
  obtain ⟨selected, hselected, heq⟩ := Option.map_eq_some_iff.mp hsearch
  have hsound := policy.searchTruncationHorizonFrom_sound
    start initialPrefix bound tolerance budget selected hselected
  cases heq
  exact ⟨hsound.1, rfl, hsound.2⟩

/-- Least acceptable state-prefix horizon, given an explicit proof that one
exists.  The proof is erased from the computed natural number. -/
def leastTruncationHorizonFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) : ℕ :=
  Nat.find hexists

/-- The explicit-existence state-prefix search returns the least acceptable
horizon. -/
theorem leastTruncationHorizonFrom_spec
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) :
    policy.truncationRadiusFrom start initialPrefix bound
        (policy.leastTruncationHorizonFrom
          start initialPrefix bound tolerance hexists) ≤ tolerance ∧
      ∀ earlier < policy.leastTruncationHorizonFrom
          start initialPrefix bound tolerance hexists,
        tolerance <
          policy.truncationRadiusFrom
            start initialPrefix bound earlier := by
  unfold leastTruncationHorizonFrom
  exact ⟨Nat.find_spec hexists,
    fun _ hlt => lt_of_not_ge (Nat.find_min hexists hlt)⟩

/-- Compute the state-prefix estimate at the least horizon certified to
exist. -/
def approximateAtLeastHorizonFrom
    (start : ℕ)
    (initialPrefix : A.StatePrefix start)
    (payoff : A.StateContinuationPayoff start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) : ℕ × ℚ × ℚ≥0 :=
  let steps := policy.leastTruncationHorizonFrom
    start initialPrefix bound tolerance hexists
  (steps,
    policy.truncationEstimateFrom
      start initialPrefix payoff bound steps)

end StateHistoryPolicy

namespace EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

variable (policy : A.EventHistoryPolicy)

/-- Exact mass of action-recording event prefixes that remain nonterminal
after `steps` future transitions from the supplied complete prefix. -/
def unfinishedMassFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) : ℚ≥0 :=
  (policy.prefixLawFrom start initialPrefix steps).eventMass
    (fun history => decide (¬ IsEmpty (A.Action history.latestState)))

/-- Exact stopped rational payoff from the supplied event prefix.  The
payoff may inspect all earlier recorded action occurrences. -/
def stoppedCenterFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.EventContinuationPayoff start) (steps : ℕ) : ℚ :=
  policy.stoppedExpectedValueFrom
    start initialPrefix steps (payoff steps)

/-- Exact nonnegative event-prefix truncation radius at one future horizon.
-/
def truncationRadiusFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound : ℚ≥0) (steps : ℕ) : ℚ≥0 :=
  bound * policy.unfinishedMassFrom start initialPrefix steps

/-- Exact stopped event-prefix center and unfinished-mass radius at one
future horizon. -/
def truncationEstimateFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.EventContinuationPayoff start)
    (bound : ℚ≥0) (steps : ℕ) : ℚ × ℚ≥0 :=
  (policy.stoppedCenterFrom start initialPrefix payoff steps,
    policy.truncationRadiusFrom start initialPrefix bound steps)

/-- Search future horizons `0, ..., budget - 1` for the first event-prefix
radius within `tolerance`.  The budget counts horizon zero. -/
def searchTruncationHorizonFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0) (budget : ℕ) : Option ℕ :=
  (List.range budget).find? fun steps =>
    decide
      (policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance)

/-- Return the first budgeted event-prefix horizon together with its exact
center and radius. -/
def searchTruncationFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.EventContinuationPayoff start)
    (bound tolerance : ℚ≥0) (budget : ℕ) :
    Option (ℕ × ℚ × ℚ≥0) :=
  (policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget).map fun steps =>
    (steps,
      policy.truncationEstimateFrom
        start initialPrefix payoff bound steps)

/-- A successful event-prefix horizon search stays inside its budget and
meets the exact rational tolerance. -/
theorem searchTruncationHorizonFrom_sound
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (hsearch : policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget = some steps) :
    steps < budget ∧
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance := by
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some hsearch), ?_⟩
  have hp := List.find?_some
    (p := fun horizon =>
      decide
        (policy.truncationRadiusFrom
          start initialPrefix bound horizon ≤ tolerance)) hsearch
  exact of_decide_eq_true hp

/-- A successful event-prefix search has rejected every earlier horizon. -/
theorem searchTruncationHorizonFrom_minimal
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (hsearch : policy.searchTruncationHorizonFrom
      start initialPrefix bound tolerance budget = some steps) :
    ∀ earlier < steps,
      tolerance <
        policy.truncationRadiusFrom start initialPrefix bound earlier := by
  have hfind := List.find?_range_eq_some.mp hsearch
  intro earlier hearlier
  have hfailed := hfind.2.2 earlier hearlier
  apply lt_of_not_ge
  simpa using hfailed

/-- Exhausting an event-prefix search means exactly that every tested horizon
fails.  It makes no claim about horizons beyond the budget. -/
theorem searchTruncationHorizonFrom_eq_none_iff
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0) (budget : ℕ) :
    policy.searchTruncationHorizonFrom
        start initialPrefix bound tolerance budget = none ↔
      ∀ steps < budget,
        tolerance <
          policy.truncationRadiusFrom start initialPrefix bound steps := by
  simp [searchTruncationHorizonFrom, List.find?_eq_none]

/-- Every returned event-prefix tuple contains the estimate at the selected
horizon and a radius within tolerance. -/
theorem searchTruncationFrom_sound
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.EventContinuationPayoff start)
    (bound tolerance : ℚ≥0) (budget steps : ℕ)
    (center : ℚ) (radius : ℚ≥0)
    (hsearch : policy.searchTruncationFrom
      start initialPrefix payoff bound tolerance budget =
        some (steps, center, radius)) :
    steps < budget ∧
      policy.truncationEstimateFrom
          start initialPrefix payoff bound steps = (center, radius) ∧
      radius ≤ tolerance := by
  obtain ⟨selected, hselected, heq⟩ := Option.map_eq_some_iff.mp hsearch
  have hsound := policy.searchTruncationHorizonFrom_sound
    start initialPrefix bound tolerance budget selected hselected
  cases heq
  exact ⟨hsound.1, rfl, hsound.2⟩

/-- Least acceptable event-prefix horizon, given an explicit proof that one
exists.  The proof is erased from the computed natural number. -/
def leastTruncationHorizonFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) : ℕ :=
  Nat.find hexists

/-- The explicit-existence event-prefix search returns the least acceptable
horizon. -/
theorem leastTruncationHorizonFrom_spec
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) :
    policy.truncationRadiusFrom start initialPrefix bound
        (policy.leastTruncationHorizonFrom
          start initialPrefix bound tolerance hexists) ≤ tolerance ∧
      ∀ earlier < policy.leastTruncationHorizonFrom
          start initialPrefix bound tolerance hexists,
        tolerance <
          policy.truncationRadiusFrom
            start initialPrefix bound earlier := by
  unfold leastTruncationHorizonFrom
  exact ⟨Nat.find_spec hexists,
    fun _ hlt => lt_of_not_ge (Nat.find_min hexists hlt)⟩

/-- Compute the event-prefix estimate at the least horizon certified to
exist. -/
def approximateAtLeastHorizonFrom
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.EventContinuationPayoff start)
    (bound tolerance : ℚ≥0)
    (hexists : ∃ steps,
      policy.truncationRadiusFrom start initialPrefix bound steps ≤
        tolerance) : ℕ × ℚ × ℚ≥0 :=
  let steps := policy.leastTruncationHorizonFrom
    start initialPrefix bound tolerance hexists
  (steps,
    policy.truncationEstimateFrom
      start initialPrefix payoff bound steps)

end EventHistoryPolicy

namespace StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

variable (policy : A.StateHistoryPolicy)

/-- Recording actions and then forgetting them preserves the exact
unfinished mass of an embedded state-history policy. -/
theorem toEventHistoryPolicy_unfinishedMassFrom_states
    (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    policy.toEventHistoryPolicy.unfinishedMassFrom
        start initialPrefix steps =
      policy.unfinishedMassFrom start initialPrefix.states steps := by
  unfold EventHistoryPolicy.unfinishedMassFrom unfinishedMassFrom
  rw [← EventHistoryPolicy.toEventHistoryPolicy_prefixLawFrom_map_states
    policy start initialPrefix steps]
  rw [FiniteLaw.eventMass_map]
  rfl

/-- A state-only dependent payoff has the same stopped center when evaluated
through the action-recording policy. -/
theorem toEventHistoryPolicy_stoppedCenterFrom_states
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.StateContinuationPayoff start) (steps : ℕ) :
    policy.toEventHistoryPolicy.stoppedCenterFrom start initialPrefix
        (fun horizon history => payoff horizon history.states) steps =
      policy.stoppedCenterFrom
        start initialPrefix.states payoff steps := by
  unfold EventHistoryPolicy.stoppedCenterFrom stoppedCenterFrom
  exact EventHistoryPolicy.toEventHistoryPolicy_stoppedExpectedValueFrom_states
    policy start initialPrefix steps (payoff steps)

/-- Recording actions and then forgetting them preserves the radius computed
for an embedded state-history policy. -/
theorem toEventHistoryPolicy_truncationRadiusFrom_states
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (bound : ℚ≥0) (steps : ℕ) :
    policy.toEventHistoryPolicy.truncationRadiusFrom
        start initialPrefix bound steps =
      policy.truncationRadiusFrom
        start initialPrefix.states bound steps := by
  simp [EventHistoryPolicy.truncationRadiusFrom, truncationRadiusFrom,
    toEventHistoryPolicy_unfinishedMassFrom_states]

/-- The complete estimate is unchanged for state-only payoffs when event
prefixes retain and then forget selected-action occurrences. -/
theorem toEventHistoryPolicy_truncationEstimateFrom_states
    (start : ℕ)
    (initialPrefix : A.EventPrefix start)
    (payoff : A.StateContinuationPayoff start)
    (bound : ℚ≥0) (steps : ℕ) :
    policy.toEventHistoryPolicy.truncationEstimateFrom start initialPrefix
        (fun horizon history => payoff horizon history.states) bound steps =
      policy.truncationEstimateFrom
        start initialPrefix.states payoff bound steps := by
  simp [EventHistoryPolicy.truncationEstimateFrom, truncationEstimateFrom,
    toEventHistoryPolicy_stoppedCenterFrom_states,
    toEventHistoryPolicy_truncationRadiusFrom_states]

end StateHistoryPolicy
end KernelArena
