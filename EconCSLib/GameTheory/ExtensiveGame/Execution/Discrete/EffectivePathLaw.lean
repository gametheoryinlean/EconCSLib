/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation

/-!
# Effective path laws from coherent finite prefixes

An effective path law exposes an exact `FiniteLaw` for every requested finite
horizon.  Its coherence proof says that extending execution and then
forgetting the new coordinates preserves the semantic finite law at the
earlier horizon.  Coherence uses `FiniteLaw.Equivalent`, because a later
finite-law presentation can split one earlier atom into several occurrences
with the same total weight.

The state and event variants below retain the absolute policy clock and the
whole supplied prefix.  Root laws are their time-zero specializations.  The
query interface contains only finite laws, exact rational masses, finite
coordinates, and Boolean cylinder predicates.  It does not expose an
infinite path, a measure, or an arbitrary measurable set.

Computing horizon `steps` expands the same exact finite execution tree as
`prefixLawFrom`.  Runtime and output size are therefore proportional to its
weighted occurrence list and can grow exponentially with the horizon and
branching degree.  This layer proves projective consistency; it deliberately
does not merge duplicate atoms or decide tail events.

## Main definitions

* `StateEffectivePathLawFrom` and `EventEffectivePathLawFrom`;
* `StateHistoryPolicy.effectivePathLawFrom` and
  `EventHistoryPolicy.effectivePathLawFrom`;
* `coordinateLaw` for exact coordinate marginals;
* `cylinderMass` for exact Boolean finite-prefix queries;
* `cylinderMass_extend` and `coordinateLaw_extend` for query coherence.
-/

namespace KernelArena

universe uS uA

private theorem map_const_equivalent_pure {α β : Type*}
    (law : FiniteLaw α) (target : β) :
    (law.map fun _ => target).Equivalent (FiniteLaw.pure target) := by
  intro value
  change
    (law.map fun _ => target).expectRat value =
      (FiniteLaw.pure target).expectRat value
  rw [FiniteLaw.expectRat_map, FiniteLaw.expectRat_pure]
  exact FiniteLaw.expectRat_const law (value target)

/-- A coherent family of exact state-prefix laws extending one supplied
prefix while retaining its absolute clock.  The argument to `prefixLaw` is
the number of new transitions, so its absolute horizon is `start + steps`. -/
structure StateEffectivePathLawFrom (A : KernelArena) (start : ℕ)
    (initialPrefix : A.StatePrefix start) where
  /-- Exact state-prefix law after the requested number of transitions. -/
  prefixLaw : (steps : ℕ) → FiniteLaw (A.StatePrefix (start + steps))
  /-- At zero new transitions the supplied prefix is deterministic. -/
  prefixLaw_zero : prefixLaw 0 = FiniteLaw.pure initialPrefix
  /-- Later laws restrict semantically to every earlier requested law. -/
  coherent : ∀ (earlier extra : ℕ),
    ((prefixLaw (earlier + extra)).map fun history =>
      StatePrefix.truncate history (start + earlier) (by omega)).Equivalent
        (prefixLaw earlier)

/-- A coherent family of exact action-recording event-prefix laws extending
one supplied prefix while retaining its absolute clock. -/
structure EventEffectivePathLawFrom (A : KernelArena) (start : ℕ)
    (initialPrefix : A.EventPrefix start) where
  /-- Exact event-prefix law after the requested number of transitions. -/
  prefixLaw : (steps : ℕ) → FiniteLaw (A.EventPrefix (start + steps))
  /-- At zero new transitions the supplied prefix is deterministic. -/
  prefixLaw_zero : prefixLaw 0 = FiniteLaw.pure initialPrefix
  /-- Later laws restrict semantically to every earlier requested law. -/
  coherent : ∀ (earlier extra : ℕ),
    ((prefixLaw (earlier + extra)).map fun history =>
      EventPrefix.truncate history (start + earlier) (by omega)).Equivalent
        (prefixLaw earlier)

/-- A time-zero effective state path law rooted at one state. -/
abbrev StateEffectivePathLaw (A : KernelArena) (root : A.State) :=
  StateEffectivePathLawFrom A 0 (StatePrefix.initial root)

/-- A time-zero effective event path law rooted at one state. -/
abbrev EventEffectivePathLaw (A : KernelArena) (root : A.State) :=
  EventEffectivePathLawFrom A 0 (EventPrefix.initial root)

namespace StateEffectivePathLawFrom

variable {A : KernelArena} {start : ℕ}
variable {initialPrefix : A.StatePrefix start}

variable (law : StateEffectivePathLawFrom A start initialPrefix)

/-- Exact law of one requested absolute state coordinate. -/
def coordinateLaw
    (steps : ℕ) (coordinate : Fin (start + steps + 1)) :
    FiniteLaw A.State :=
  (law.prefixLaw steps).map fun history => history coordinate

/-- Exact rational mass of a Boolean cylinder predicate on one finite state
prefix. -/
def cylinderMass
    (steps : ℕ) (event : A.StatePrefix (start + steps) → Bool) : ℚ≥0 :=
  (law.prefixLaw steps).eventMass event

/-- Coordinate-event queries are the corresponding finite-prefix cylinder
queries. -/
theorem coordinateEventMass_eq_cylinderMass
    (steps : ℕ) (coordinate : Fin (start + steps + 1))
    (event : A.State → Bool) :
    (law.coordinateLaw steps coordinate).eventMass event =
      law.cylinderMass steps (fun history => event (history coordinate)) := by
  rw [coordinateLaw, cylinderMass, FiniteLaw.eventMass_map]
  rfl

/-- A Boolean cylinder has the same exact mass at every later horizon after
lifting it by prefix restriction. -/
theorem cylinderMass_extend
    (earlier extra : ℕ)
    (event : A.StatePrefix (start + earlier) → Bool) :
    law.cylinderMass (earlier + extra) (fun history =>
        event (StatePrefix.truncate history (start + earlier) (by omega))) =
      law.cylinderMass earlier event := by
  have hmass := (law.coherent earlier extra).eventMass event
  simpa only [cylinderMass, FiniteLaw.eventMass_map,
    Function.comp_apply] using hmass

/-- An old coordinate marginal is unchanged by asking for additional future
coordinates. -/
theorem coordinateLaw_extend
    (earlier extra : ℕ) (coordinate : Fin (start + earlier + 1)) :
    (law.coordinateLaw (earlier + extra)
      (Fin.cast (by omega) (StatePrefix.oldIndex extra coordinate))).Equivalent
        (law.coordinateLaw earlier coordinate) := by
  have hmap := (law.coherent earlier extra).map
    (fun history : A.StatePrefix (start + earlier) => history coordinate)
  simpa only [coordinateLaw, FiniteLaw.map_comp, Function.comp_apply,
    StatePrefix.oldIndex, StatePrefix.truncate] using hmap

end StateEffectivePathLawFrom

namespace EventEffectivePathLawFrom

variable {A : KernelArena} {start : ℕ}
variable {initialPrefix : A.EventPrefix start}

variable (law : EventEffectivePathLawFrom A start initialPrefix)

/-- Exact law of one requested action-recording event coordinate. -/
def eventCoordinateLaw
    (steps : ℕ) (coordinate : Fin (start + steps + 1)) :
    FiniteLaw A.PathEvent :=
  (law.prefixLaw steps).map fun history => history coordinate

/-- Exact state-coordinate law, projected after action-recording execution. -/
def stateCoordinateLaw
    (steps : ℕ) (coordinate : Fin (start + steps + 1)) :
    FiniteLaw A.State :=
  (law.eventCoordinateLaw steps coordinate).map PathEvent.state

/-- Exact rational mass of a Boolean cylinder predicate on one finite event
prefix. -/
def cylinderMass
    (steps : ℕ) (event : A.EventPrefix (start + steps) → Bool) : ℚ≥0 :=
  (law.prefixLaw steps).eventMass event

/-- Event-coordinate queries are the corresponding event-prefix cylinder
queries. -/
theorem eventCoordinateEventMass_eq_cylinderMass
    (steps : ℕ) (coordinate : Fin (start + steps + 1))
    (event : A.PathEvent → Bool) :
    (law.eventCoordinateLaw steps coordinate).eventMass event =
      law.cylinderMass steps (fun history => event (history coordinate)) := by
  rw [eventCoordinateLaw, cylinderMass, FiniteLaw.eventMass_map]
  rfl

/-- State-coordinate queries are cylinders evaluated after the event-state
projection. -/
theorem stateCoordinateEventMass_eq_cylinderMass
    (steps : ℕ) (coordinate : Fin (start + steps + 1))
    (event : A.State → Bool) :
    (law.stateCoordinateLaw steps coordinate).eventMass event =
      law.cylinderMass steps
        (fun history => event (history coordinate).state) := by
  rw [stateCoordinateLaw, eventCoordinateLaw, cylinderMass,
    FiniteLaw.eventMass_map, FiniteLaw.eventMass_map]
  rfl

/-- A Boolean event cylinder has the same exact mass at every later horizon
after lifting it by prefix restriction. -/
theorem cylinderMass_extend
    (earlier extra : ℕ)
    (event : A.EventPrefix (start + earlier) → Bool) :
    law.cylinderMass (earlier + extra) (fun history =>
        event (EventPrefix.truncate history (start + earlier) (by omega))) =
      law.cylinderMass earlier event := by
  have hmass := (law.coherent earlier extra).eventMass event
  simpa only [cylinderMass, FiniteLaw.eventMass_map,
    Function.comp_apply] using hmass

/-- An old event-coordinate marginal is unchanged by asking for additional
future coordinates. -/
theorem eventCoordinateLaw_extend
    (law : EventEffectivePathLawFrom A start initialPrefix)
    (earlier extra : ℕ) (coordinate : Fin (start + earlier + 1)) :
    (law.eventCoordinateLaw (earlier + extra)
      (Fin.cast (by omega) (EventPrefix.oldIndex extra coordinate))).Equivalent
        (law.eventCoordinateLaw earlier coordinate) := by
  have hmap := (law.coherent earlier extra).map
    (fun history : A.EventPrefix (start + earlier) => history coordinate)
  simpa only [eventCoordinateLaw, FiniteLaw.map_comp, Function.comp_apply,
    EventPrefix.oldIndex, EventPrefix.truncate] using hmap

/-- The state projection of an old event coordinate is likewise unchanged by
asking for additional future coordinates. -/
theorem stateCoordinateLaw_extend
    (earlier extra : ℕ) (coordinate : Fin (start + earlier + 1)) :
    (law.stateCoordinateLaw (earlier + extra)
      (Fin.cast (by omega) (EventPrefix.oldIndex extra coordinate))).Equivalent
        (law.stateCoordinateLaw earlier coordinate) := by
  exact (law.eventCoordinateLaw_extend earlier extra coordinate).map
    PathEvent.state

end EventEffectivePathLawFrom

namespace StateHistoryPolicy

variable {A : KernelArena}

private theorem truncate_snoc
    {current kept : ℕ} (history : A.StatePrefix current) (state : A.State)
    (kept_le : kept ≤ current) :
    StatePrefix.truncate (history.snoc state) kept
        (kept_le.trans (Nat.le_succ current)) =
      StatePrefix.truncate history kept kept_le := by
  funext index
  have hindex :
      Fin.castLE (Nat.succ_le_succ (kept_le.trans (Nat.le_succ current)))
          index =
        (Fin.castLE (Nat.succ_le_succ kept_le) index).castSucc := by
    apply Fin.ext
    rfl
  change (history.snoc state) _ = history _
  rw [hindex]
  simpa only [StatePrefix.snoc] using
    (@Fin.snoc_castSucc (current + 1) (fun _ => A.State)
      state history (Fin.castLE (Nat.succ_le_succ kept_le) index))

variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

private theorem prefixLawFrom_truncate_succ_equivalent
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (earlier extra : ℕ) :
    ((policy.prefixLawFrom start initialPrefix (earlier + extra + 1)).map
      fun history =>
        StatePrefix.truncate history (start + earlier) (by omega)).Equivalent
      ((policy.prefixLawFrom start initialPrefix (earlier + extra)).map
        fun history =>
          StatePrefix.truncate history (start + earlier) (by omega)) := by
  rw [prefixLawFrom_succ, FiniteLaw.map_bind]
  let previous := policy.prefixLawFrom start initialPrefix (earlier + extra)
  let restrict : A.StatePrefix (start + (earlier + extra)) →
      A.StatePrefix (start + earlier) := fun history =>
    StatePrefix.truncate history (start + earlier) (by omega)
  apply FiniteLaw.Equivalent.trans
    (second := previous.bind fun history => FiniteLaw.pure (restrict history))
  · apply (FiniteLaw.Equivalent.refl previous).bind
    intro history
    rw [FiniteLaw.map_comp]
    change
      ((policy.stoppedStepLaw (start + (earlier + extra)) history).map
        fun state => StatePrefix.truncate (history.snoc state)
          (start + earlier) (by omega)).Equivalent
        (FiniteLaw.pure (restrict history))
    have hfunction :
        (fun state => StatePrefix.truncate (history.snoc state)
          (start + earlier) (by omega)) =
          (fun _ => restrict history) := by
      funext state
      exact truncate_snoc history state (by omega)
    rw [hfunction]
    exact map_const_equivalent_pure _ _
  · apply FiniteLaw.Equivalent.of_eq
    rw [FiniteLaw.map_eq_bind_pure_comp]
    rfl

private theorem prefixLawFrom_truncate_equivalent
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (earlier extra : ℕ) :
    ((policy.prefixLawFrom start initialPrefix (earlier + extra)).map
      fun history =>
        StatePrefix.truncate history (start + earlier) (by omega)).Equivalent
      (policy.prefixLawFrom start initialPrefix earlier) := by
  induction extra with
  | zero =>
      change
        ((policy.prefixLawFrom start initialPrefix earlier).map
          fun history => StatePrefix.truncate history
            (start + earlier) (by omega)).Equivalent
          (policy.prefixLawFrom start initialPrefix earlier)
      have hfunction :
          (fun history : A.StatePrefix (start + earlier) =>
            StatePrefix.truncate history (start + earlier) (by omega)) = id := by
        funext history
        exact StatePrefix.truncate_self history
      rw [hfunction, FiniteLaw.map_id]
      exact FiniteLaw.Equivalent.refl _
  | succ extra ih =>
      exact (prefixLawFrom_truncate_succ_equivalent
        policy start initialPrefix earlier extra).trans ih

/-- Package history-dependent bounded state execution as a coherent effective
path law retaining the supplied prefix and absolute policy clock. -/
def effectivePathLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) :
    StateEffectivePathLawFrom A start initialPrefix where
  prefixLaw := policy.prefixLawFrom start initialPrefix
  prefixLaw_zero := policy.prefixLawFrom_zero start initialPrefix
  coherent := fun earlier extra =>
    prefixLawFrom_truncate_equivalent
      policy start initialPrefix earlier extra

/-- Package time-zero state execution as an effective path law rooted at one
state. -/
def effectivePathLaw (policy : A.StateHistoryPolicy) (root : A.State) :
    StateEffectivePathLaw A root :=
  policy.effectivePathLawFrom 0 (StatePrefix.initial root)

@[simp]
theorem effectivePathLawFrom_prefixLaw
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    (policy.effectivePathLawFrom start initialPrefix).prefixLaw steps =
      policy.prefixLawFrom start initialPrefix steps :=
  rfl

@[simp]
theorem effectivePathLaw_prefixLaw_zero
    (policy : A.StateHistoryPolicy) (root : A.State) :
    (policy.effectivePathLaw root).prefixLaw 0 =
      FiniteLaw.pure (StatePrefix.initial root) :=
  policy.prefixLawFrom_zero 0 (StatePrefix.initial root)

end StateHistoryPolicy

namespace EventHistoryPolicy

variable {A : KernelArena}

private theorem truncate_snoc
    {current kept : ℕ} (history : A.EventPrefix current)
    (event : A.PathEvent) (kept_le : kept ≤ current) :
    EventPrefix.truncate (history.snoc event) kept
        (kept_le.trans (Nat.le_succ current)) =
      EventPrefix.truncate history kept kept_le := by
  funext index
  have hindex :
      Fin.castLE (Nat.succ_le_succ (kept_le.trans (Nat.le_succ current)))
          index =
        (Fin.castLE (Nat.succ_le_succ kept_le) index).castSucc := by
    apply Fin.ext
    rfl
  change (history.snoc event) _ = history _
  rw [hindex]
  simpa only [EventPrefix.snoc] using
    (@Fin.snoc_castSucc (current + 1) (fun _ => A.PathEvent)
      event history (Fin.castLE (Nat.succ_le_succ kept_le) index))

variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

private theorem prefixLawFrom_truncate_succ_equivalent
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (earlier extra : ℕ) :
    ((policy.prefixLawFrom start initialPrefix (earlier + extra + 1)).map
      fun history =>
        EventPrefix.truncate history (start + earlier) (by omega)).Equivalent
      ((policy.prefixLawFrom start initialPrefix (earlier + extra)).map
        fun history =>
          EventPrefix.truncate history (start + earlier) (by omega)) := by
  rw [prefixLawFrom_succ, FiniteLaw.map_bind]
  let previous := policy.prefixLawFrom start initialPrefix (earlier + extra)
  let restrict : A.EventPrefix (start + (earlier + extra)) →
      A.EventPrefix (start + earlier) := fun history =>
    EventPrefix.truncate history (start + earlier) (by omega)
  apply FiniteLaw.Equivalent.trans
    (second := previous.bind fun history => FiniteLaw.pure (restrict history))
  · apply (FiniteLaw.Equivalent.refl previous).bind
    intro history
    rw [FiniteLaw.map_comp]
    change
      ((policy.stoppedStepLaw (start + (earlier + extra)) history).map
        fun event => EventPrefix.truncate (history.snoc event)
          (start + earlier) (by omega)).Equivalent
        (FiniteLaw.pure (restrict history))
    have hfunction :
        (fun event => EventPrefix.truncate (history.snoc event)
          (start + earlier) (by omega)) =
          (fun _ => restrict history) := by
      funext event
      exact truncate_snoc history event (by omega)
    rw [hfunction]
    exact map_const_equivalent_pure _ _
  · apply FiniteLaw.Equivalent.of_eq
    rw [FiniteLaw.map_eq_bind_pure_comp]
    rfl

private theorem prefixLawFrom_truncate_equivalent
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (earlier extra : ℕ) :
    ((policy.prefixLawFrom start initialPrefix (earlier + extra)).map
      fun history =>
        EventPrefix.truncate history (start + earlier) (by omega)).Equivalent
      (policy.prefixLawFrom start initialPrefix earlier) := by
  induction extra with
  | zero =>
      change
        ((policy.prefixLawFrom start initialPrefix earlier).map
          fun history => EventPrefix.truncate history
            (start + earlier) (by omega)).Equivalent
          (policy.prefixLawFrom start initialPrefix earlier)
      have hfunction :
          (fun history : A.EventPrefix (start + earlier) =>
            EventPrefix.truncate history (start + earlier) (by omega)) = id := by
        funext history
        exact EventPrefix.truncate_self history
      rw [hfunction, FiniteLaw.map_id]
      exact FiniteLaw.Equivalent.refl _
  | succ extra ih =>
      exact (prefixLawFrom_truncate_succ_equivalent
        policy start initialPrefix earlier extra).trans ih

/-- Package history-dependent bounded event execution as a coherent effective
path law retaining the supplied prefix and absolute policy clock. -/
def effectivePathLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) :
    EventEffectivePathLawFrom A start initialPrefix where
  prefixLaw := policy.prefixLawFrom start initialPrefix
  prefixLaw_zero := policy.prefixLawFrom_zero start initialPrefix
  coherent := fun earlier extra =>
    prefixLawFrom_truncate_equivalent
      policy start initialPrefix earlier extra

/-- Package time-zero event execution as an effective path law rooted at one
state. -/
def effectivePathLaw (policy : A.EventHistoryPolicy) (root : A.State) :
    EventEffectivePathLaw A root :=
  policy.effectivePathLawFrom 0 (EventPrefix.initial root)

@[simp]
theorem effectivePathLawFrom_prefixLaw
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    (policy.effectivePathLawFrom start initialPrefix).prefixLaw steps =
      policy.prefixLawFrom start initialPrefix steps :=
  rfl

@[simp]
theorem effectivePathLaw_prefixLaw_zero
    (policy : A.EventHistoryPolicy) (root : A.State) :
    (policy.effectivePathLaw root).prefixLaw 0 =
      FiniteLaw.pure (EventPrefix.initial root) :=
  policy.prefixLawFrom_zero 0 (EventPrefix.initial root)

end EventHistoryPolicy

end KernelArena
