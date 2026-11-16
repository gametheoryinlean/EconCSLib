/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Execution.FinitePayoff

/-!
# Exact utilities of effective finite-prefix path laws

This module evaluates rational observables directly on coherent effective
state- and event-prefix laws.  Every query calls `FiniteLaw.expectRat` at one
requested finite horizon.  A rational observable determined by an earlier
prefix is a cylinder observable at every later horizon; projective coherence
proves that its exact expectation is unchanged.

Event-prefix observables receive the complete action-recording prefix, so
distinct routes and action occurrences are not replaced by their endpoint.
State-only observation of an event law is an explicit projection, with a
correspondence theorem for event execution compiled from a state-history
policy.

The running interface is measure-free and contains no infinite paths,
approximation tolerances, or discount factors.  Evaluating a supplied prefix
law is linear in its weighted occurrence list.  Producing that list still has
the execution-tree complexity of `prefixLawFrom` and can grow exponentially
with the horizon and branching degree.

## Main definitions and results

* state/event `expectedPrefixValue` for exact rational prefix observables;
* `expectedPrefixValue_extend` for rational cylinder coherence;
* event `expectedStatePrefixValue` for explicit action-forgetting projection;
* `expectedStatePrefixValue_extend` and the state-policy projection theorem.
-/

namespace KernelArena

universe uS uA

namespace StateEffectivePathLawFrom

variable {A : KernelArena} {start : ℕ}
variable {initialPrefix : A.StatePrefix start}

variable (law : StateEffectivePathLawFrom A start initialPrefix)

/-- Exact rational expectation of a state-prefix observable at one requested
horizon. -/
def expectedPrefixValue
    (steps : ℕ) (value : A.StatePrefix (start + steps) → ℚ) : ℚ :=
  (law.prefixLaw steps).expectRat value

/-- At zero new transitions, expectation is evaluation on the supplied
prefix. -/
@[simp]
theorem expectedPrefixValue_zero
    (value : A.StatePrefix (start + 0) → ℚ) :
    law.expectedPrefixValue 0 value = value initialPrefix := by
  rw [expectedPrefixValue, law.prefixLaw_zero,
    FiniteLaw.expectRat_pure]

/-- A rational observable determined by an earlier state prefix has the same
exact expectation at every later horizon after restriction to that prefix. -/
theorem expectedPrefixValue_extend
    (earlier extra : ℕ)
    (value : A.StatePrefix (start + earlier) → ℚ) :
    law.expectedPrefixValue (earlier + extra) (fun history =>
        value (StatePrefix.truncate history (start + earlier) (by omega))) =
      law.expectedPrefixValue earlier value := by
  change
    (law.prefixLaw (earlier + extra)).expectRat _ =
      (law.prefixLaw earlier).expectRat value
  calc
    (law.prefixLaw (earlier + extra)).expectRat
        (fun history =>
          value (StatePrefix.truncate history (start + earlier) (by omega))) =
        ((law.prefixLaw (earlier + extra)).map fun history =>
          StatePrefix.truncate history (start + earlier) (by omega)).expectRat
            value := by
      rw [FiniteLaw.expectRat_map]
      rfl
    _ = (law.prefixLaw earlier).expectRat value :=
      (FiniteLaw.equivalent_iff_expectRat.mp
        (law.coherent earlier extra)) value

end StateEffectivePathLawFrom

namespace EventEffectivePathLawFrom

variable {A : KernelArena} {start : ℕ}
variable {initialPrefix : A.EventPrefix start}

variable (law : EventEffectivePathLawFrom A start initialPrefix)

/-- Exact rational expectation of a complete action-recording prefix
observable at one requested horizon. -/
def expectedPrefixValue
    (steps : ℕ) (value : A.EventPrefix (start + steps) → ℚ) : ℚ :=
  (law.prefixLaw steps).expectRat value

/-- Exact rational expectation after explicitly forgetting recorded actions
but retaining every state coordinate. -/
def expectedStatePrefixValue
    (steps : ℕ) (value : A.StatePrefix (start + steps) → ℚ) : ℚ :=
  ((law.prefixLaw steps).map EventPrefix.states).expectRat value

/-- At zero new transitions, an event-prefix expectation is evaluation on the
supplied prefix. -/
@[simp]
theorem expectedPrefixValue_zero
    (value : A.EventPrefix (start + 0) → ℚ) :
    law.expectedPrefixValue 0 value = value initialPrefix := by
  rw [expectedPrefixValue, law.prefixLaw_zero,
    FiniteLaw.expectRat_pure]

/-- A rational observable determined by an earlier event prefix has the same
exact expectation at every later horizon after restriction.  The observable
may inspect every recorded action occurrence. -/
theorem expectedPrefixValue_extend
    (earlier extra : ℕ)
    (value : A.EventPrefix (start + earlier) → ℚ) :
    law.expectedPrefixValue (earlier + extra) (fun history =>
        value (EventPrefix.truncate history (start + earlier) (by omega))) =
      law.expectedPrefixValue earlier value := by
  change
    (law.prefixLaw (earlier + extra)).expectRat _ =
      (law.prefixLaw earlier).expectRat value
  calc
    (law.prefixLaw (earlier + extra)).expectRat
        (fun history =>
          value (EventPrefix.truncate history (start + earlier) (by omega))) =
        ((law.prefixLaw (earlier + extra)).map fun history =>
          EventPrefix.truncate history (start + earlier) (by omega)).expectRat
            value := by
      rw [FiniteLaw.expectRat_map]
      rfl
    _ = (law.prefixLaw earlier).expectRat value :=
      (FiniteLaw.equivalent_iff_expectRat.mp
        (law.coherent earlier extra)) value

/-- State-prefix expectation is exactly the event-prefix expectation of the
observable composed with action-forgetting projection. -/
theorem expectedStatePrefixValue_eq_expectedPrefixValue_states
    (steps : ℕ) (value : A.StatePrefix (start + steps) → ℚ) :
    law.expectedStatePrefixValue steps value =
      law.expectedPrefixValue steps (fun history => value history.states) := by
  rw [expectedStatePrefixValue, expectedPrefixValue,
    FiniteLaw.expectRat_map]
  rfl

/-- A rational state-prefix observable projected from an event law is also
unchanged by extending the requested horizon. -/
theorem expectedStatePrefixValue_extend
    (earlier extra : ℕ)
    (value : A.StatePrefix (start + earlier) → ℚ) :
    law.expectedStatePrefixValue (earlier + extra) (fun history =>
        value (StatePrefix.truncate history (start + earlier) (by omega))) =
      law.expectedStatePrefixValue earlier value := by
  rw [expectedStatePrefixValue_eq_expectedPrefixValue_states,
    expectedStatePrefixValue_eq_expectedPrefixValue_states]
  simpa only [EventPrefix.states, EventPrefix.truncate,
    StatePrefix.truncate] using
      law.expectedPrefixValue_extend earlier extra
        (fun history : A.EventPrefix (start + earlier) =>
          value history.states)

end EventEffectivePathLawFrom

namespace StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- The effective-law utility query reuses the existing exact state-prefix
payoff computation for a policy-derived law. -/
@[simp]
theorem effectivePathLawFrom_expectedPrefixValue
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (value : A.StatePrefix (start + steps) → ℚ) :
    (policy.effectivePathLawFrom start initialPrefix).expectedPrefixValue
        steps value =
      policy.expectedPrefixValueFrom start initialPrefix steps value :=
  rfl

end StateHistoryPolicy

namespace EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- The effective-law utility query reuses the existing exact event-prefix
payoff computation for a policy-derived law. -/
@[simp]
theorem effectivePathLawFrom_expectedPrefixValue
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (value : A.EventPrefix (start + steps) → ℚ) :
    (policy.effectivePathLawFrom start initialPrefix).expectedPrefixValue
        steps value =
      policy.expectedPrefixValueFrom start initialPrefix steps value :=
  rfl

/-- Executing a state-history policy with action recording and then forgetting
those actions preserves every exact rational state-prefix expectation. -/
theorem toEventHistoryPolicy_effectivePathLawFrom_expectedStatePrefixValue
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (value : A.StatePrefix (start + steps) → ℚ) :
    ((policy.toEventHistoryPolicy).effectivePathLawFrom
      start initialPrefix).expectedStatePrefixValue steps value =
      (policy.effectivePathLawFrom start initialPrefix.states).expectedPrefixValue
        steps value := by
  rw [EventEffectivePathLawFrom.expectedStatePrefixValue_eq_expectedPrefixValue_states]
  rw [effectivePathLawFrom_expectedPrefixValue,
    StateHistoryPolicy.effectivePathLawFrom_expectedPrefixValue]
  exact toEventHistoryPolicy_expectedPrefixValueFrom_states
    policy start initialPrefix steps value

end EventHistoryPolicy

end KernelArena
