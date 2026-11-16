/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel

/-!
# Executable finite observations and restart prefixes

This module builds finite coordinate, tail, and fresh-restart queries from the
history-dependent `KernelArena` executor. Absolute continuations extend the
entire supplied prefix at its existing clock. Fresh restarts instead retain
only the latest state, run the same policy from time zero, and may then splice
the generated tail back after the old prefix.

All results are exact `FiniteLaw` values. State projections are applied only
after action-recording execution, so observing states does not erase actions
that may affect later policy choices. No infinite path law or measure is
constructed here.

## Main definitions

* `StateHistoryPolicy.coordinateLawFrom` and `tailPrefixLawFrom`;
* `EventHistoryPolicy.eventCoordinateLawFrom`, `stateCoordinateLawFrom`, and
  `tailPrefixLawFrom`;
* `freshPrefixLaw` for a time-zero restart;
* `freshSplicedPrefixLawFrom` for adjoining a fresh continuation to an old
  prefix without reusing the old absolute clock;
* `absolutePrefixLawFrom` and `splicedFreshAbsolutePrefixLawFrom` for arbitrary
  absolute horizons on either side of the splice point.
-/

namespace KernelArena

universe uS uA

namespace StatePrefix

variable {A : KernelArena} {start steps : ℕ}

/-- Restrict a finite state prefix to an earlier absolute horizon. -/
def truncate (history : A.StatePrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) : A.StatePrefix horizon :=
  fun index => history (Fin.castLE (Nat.succ_le_succ horizon_le) index)

@[simp]
theorem truncate_self (history : A.StatePrefix start) :
    truncate history start le_rfl = history := by
  funext index
  rfl

/-- Reindex the coordinates from absolute time `start` through
`start + steps` as a fresh prefix with coordinates `0, ..., steps`. -/
def tailFrom (history : A.StatePrefix (start + steps)) : A.StatePrefix steps :=
  fun index =>
    history (Fin.cast (Nat.add_assoc start steps 1).symm
      (Fin.natAdd start index))

/-- Embed an old-prefix coordinate into a prefix extended by `steps`. -/
def oldIndex (steps : ℕ) (index : Fin (start + 1)) :
    Fin (start + steps + 1) :=
  Fin.cast (by omega) (Fin.castAdd steps index)

/-- Embed a strictly positive fresh-tail coordinate after the old prefix. -/
def freshIndex (start : ℕ) (index : Fin steps) :
    Fin (start + steps + 1) :=
  Fin.cast (by omega) (Fin.natAdd (start + 1) index)

/-- Append all positive-time coordinates of a fresh prefix after an existing
prefix. The fresh coordinate zero is omitted because it represents the old
prefix's latest state. -/
def spliceFresh (initial : A.StatePrefix start) (fresh : A.StatePrefix steps) :
    A.StatePrefix (start + steps) :=
  fun index =>
    Fin.append initial (Fin.tail fresh) (Fin.cast (by omega) index)

@[simp]
theorem spliceFresh_oldIndex (initial : A.StatePrefix start)
    (fresh : A.StatePrefix steps) (index : Fin (start + 1)) :
    spliceFresh initial fresh (oldIndex steps index) = initial index := by
  simp [spliceFresh, oldIndex]

@[simp]
theorem spliceFresh_freshIndex (initial : A.StatePrefix start)
    (fresh : A.StatePrefix steps) (index : Fin steps) :
    spliceFresh initial fresh (freshIndex start index) = fresh index.succ := by
  simp [spliceFresh, freshIndex]
  rfl

end StatePrefix

namespace EventPrefix

variable {A : KernelArena} {start steps : ℕ}

/-- Restrict a finite event prefix to an earlier absolute horizon. -/
def truncate (history : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) : A.EventPrefix horizon :=
  fun index => history (Fin.castLE (Nat.succ_le_succ horizon_le) index)

@[simp]
theorem truncate_self (history : A.EventPrefix start) :
    truncate history start le_rfl = history := by
  funext index
  rfl

/-- Reindex an absolute action-recording continuation from `start` as a
freshly indexed finite tail. The action stored at absolute `start` is kept. -/
def tailFrom (history : A.EventPrefix (start + steps)) : A.EventPrefix steps :=
  fun index =>
    history (Fin.cast (Nat.add_assoc start steps 1).symm
      (Fin.natAdd start index))

/-- Embed an old event-prefix coordinate into an extended prefix. -/
def oldIndex (steps : ℕ) (index : Fin (start + 1)) :
    Fin (start + steps + 1) :=
  Fin.cast (by omega) (Fin.castAdd steps index)

/-- Embed a positive fresh-event coordinate after the old event prefix. -/
def freshIndex (start : ℕ) (index : Fin steps) :
    Fin (start + steps + 1) :=
  Fin.cast (by omega) (Fin.natAdd (start + 1) index)

/-- Append the positive-time events of a fresh restart after an existing
event prefix. Its time-zero marker is omitted at the splice point. -/
def spliceFresh (initial : A.EventPrefix start) (fresh : A.EventPrefix steps) :
    A.EventPrefix (start + steps) :=
  fun index =>
    Fin.append initial (Fin.tail fresh) (Fin.cast (by omega) index)

@[simp]
theorem spliceFresh_oldIndex (initial : A.EventPrefix start)
    (fresh : A.EventPrefix steps) (index : Fin (start + 1)) :
    spliceFresh initial fresh (oldIndex steps index) = initial index := by
  simp [spliceFresh, oldIndex]

@[simp]
theorem spliceFresh_freshIndex (initial : A.EventPrefix start)
    (fresh : A.EventPrefix steps) (index : Fin steps) :
    spliceFresh initial fresh (freshIndex start index) = fresh index.succ := by
  simp [spliceFresh, freshIndex]
  rfl

@[simp]
theorem states_tailFrom (history : A.EventPrefix (start + steps)) :
    (tailFrom history).states = StatePrefix.tailFrom history.states :=
  rfl

end EventPrefix

namespace StateHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- Exact law of any requested state coordinate in a bounded absolute-prefix
execution. -/
def coordinateLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) : FiniteLaw A.State :=
  (policy.prefixLawFrom start initialPrefix steps).map fun history =>
    history coordinate

/-- Exact law of the final state after `steps` absolute-clock transitions. -/
def finalStateLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) : FiniteLaw A.State :=
  policy.coordinateLawFrom start initialPrefix steps (Fin.last (start + steps))

/-- Exact law of the generated absolute continuation, reindexed from zero
while retaining every state from the splice coordinate onward. -/
def tailPrefixLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    FiniteLaw (A.StatePrefix steps) :=
  (policy.prefixLawFrom start initialPrefix steps).map StatePrefix.tailFrom

/-- Exact absolute-prefix law through any requested horizon. Horizons already
inside the supplied prefix are answered deterministically; later horizons run
exactly the missing number of transitions at the original absolute clock. -/
def absolutePrefixLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (horizon : ℕ) :
    FiniteLaw (A.StatePrefix horizon) :=
  if horizon_le : horizon ≤ start then
    FiniteLaw.pure (StatePrefix.truncate initialPrefix horizon horizon_le)
  else
    (policy.prefixLawFrom start initialPrefix (horizon - start)).map
      fun history index => history (Fin.cast (by omega) index)

@[simp]
theorem absolutePrefixLawFrom_of_le (policy : A.StateHistoryPolicy)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    policy.absolutePrefixLawFrom start initialPrefix horizon =
      FiniteLaw.pure
        (StatePrefix.truncate initialPrefix horizon horizon_le) := by
  simp [absolutePrefixLawFrom, horizon_le]

/-- Execute the policy from one state at a fresh time-zero clock. This executor
recurses directly on the fresh clock, so its result type is definitionally
indexed by `steps` rather than transported from `0 + steps`. -/
def freshPrefixLaw (policy : A.StateHistoryPolicy) (state : A.State) :
    (steps : ℕ) → FiniteLaw (A.StatePrefix steps)
  | 0 => FiniteLaw.pure (StatePrefix.initial state)
  | steps + 1 =>
      (policy.freshPrefixLaw state steps).bind fun history =>
        (policy.stoppedStepLaw steps history).map history.snoc

/-- Run a time-zero restart from the latest old state and splice its positive
coordinates after the unchanged old prefix. -/
def freshSplicedPrefixLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    FiniteLaw (A.StatePrefix (start + steps)) :=
  (policy.freshPrefixLaw initialPrefix.latest steps).map
    (StatePrefix.spliceFresh initialPrefix)

/-- Exact finite absolute-prefix law of a fresh-clock restart spliced after an
old prefix. A horizon inside the old prefix performs no stochastic execution. -/
def splicedFreshAbsolutePrefixLawFrom (policy : A.StateHistoryPolicy)
    (start : ℕ) (initialPrefix : A.StatePrefix start) (horizon : ℕ) :
    FiniteLaw (A.StatePrefix horizon) :=
  if horizon_le : horizon ≤ start then
    FiniteLaw.pure (StatePrefix.truncate initialPrefix horizon horizon_le)
  else
    (policy.freshSplicedPrefixLawFrom start initialPrefix
      (horizon - start)).map fun history index =>
        history (Fin.cast (by omega) index)

@[simp]
theorem splicedFreshAbsolutePrefixLawFrom_of_le
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    policy.splicedFreshAbsolutePrefixLawFrom start initialPrefix horizon =
      FiniteLaw.pure
        (StatePrefix.truncate initialPrefix horizon horizon_le) := by
  simp [splicedFreshAbsolutePrefixLawFrom, horizon_le]

@[simp]
theorem freshPrefixLaw_zero (policy : A.StateHistoryPolicy) (state : A.State) :
    policy.freshPrefixLaw state 0 =
      FiniteLaw.pure (StatePrefix.initial state) :=
  rfl

@[simp]
theorem freshPrefixLaw_succ (policy : A.StateHistoryPolicy) (state : A.State)
    (steps : ℕ) :
    policy.freshPrefixLaw state (steps + 1) =
      (policy.freshPrefixLaw state steps).bind fun history =>
        (policy.stoppedStepLaw steps history).map history.snoc :=
  rfl

@[simp]
theorem freshSplicedPrefixLawFrom_zero (policy : A.StateHistoryPolicy)
    (start : ℕ) (initialPrefix : A.StatePrefix start) :
    policy.freshSplicedPrefixLawFrom start initialPrefix 0 =
      FiniteLaw.pure initialPrefix := by
  rw [freshSplicedPrefixLawFrom, freshPrefixLaw_zero,
    FiniteLaw.pure_map]
  congr
  funext index
  let oldIndex : Fin (start + 1) := Fin.cast (by omega) index
  have happend := Fin.append_left initialPrefix
    (Fin.tail (StatePrefix.initial initialPrefix.latest)) oldIndex
  simpa [StatePrefix.spliceFresh, oldIndex] using happend

end StateHistoryPolicy

namespace EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- Exact law of any requested action-recording event coordinate. -/
def eventCoordinateLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) : FiniteLaw A.PathEvent :=
  (policy.prefixLawFrom start initialPrefix steps).map fun history =>
    history coordinate

/-- Exact state-coordinate law obtained after executing with the complete
action-recording history. -/
def stateCoordinateLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) : FiniteLaw A.State :=
  (policy.eventCoordinateLawFrom start initialPrefix steps coordinate).map
    PathEvent.state

/-- Exact law of the final action-recording event. -/
def finalEventLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    FiniteLaw A.PathEvent :=
  policy.eventCoordinateLawFrom start initialPrefix steps
    (Fin.last (start + steps))

/-- Exact law of the final state, projected after action-recording execution. -/
def finalStateLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) : FiniteLaw A.State :=
  policy.stateCoordinateLawFrom start initialPrefix steps
    (Fin.last (start + steps))

/-- Exact action-recording continuation reindexed from the supplied absolute
prefix coordinate. -/
def tailPrefixLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    FiniteLaw (A.EventPrefix steps) :=
  (policy.prefixLawFrom start initialPrefix steps).map EventPrefix.tailFrom

/-- Exact action-recording absolute-prefix law through any horizon. Earlier
horizons truncate the supplied prefix; later horizons preserve its clock and
execute only the missing transitions. -/
def absolutePrefixLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    FiniteLaw (A.EventPrefix horizon) :=
  if horizon_le : horizon ≤ start then
    FiniteLaw.pure (EventPrefix.truncate initialPrefix horizon horizon_le)
  else
    (policy.prefixLawFrom start initialPrefix (horizon - start)).map
      fun history index => history (Fin.cast (by omega) index)

@[simp]
theorem absolutePrefixLawFrom_of_le (policy : A.EventHistoryPolicy)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    policy.absolutePrefixLawFrom start initialPrefix horizon =
      FiniteLaw.pure
        (EventPrefix.truncate initialPrefix horizon horizon_le) := by
  simp [absolutePrefixLawFrom, horizon_le]

/-- Execute an action-recording policy from one state at a fresh clock. This
recurses on the fresh clock directly and records every selected action. -/
def freshPrefixLaw (policy : A.EventHistoryPolicy) (state : A.State) :
    (steps : ℕ) → FiniteLaw (A.EventPrefix steps)
  | 0 => FiniteLaw.pure (EventPrefix.initial state)
  | steps + 1 =>
      (policy.freshPrefixLaw state steps).bind fun history =>
        (policy.stoppedStepLaw steps history).map history.snoc

/-- Run a fresh event-history continuation from the old latest state and
splice its positive-time events after the old prefix. -/
def freshSplicedPrefixLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    FiniteLaw (A.EventPrefix (start + steps)) :=
  (policy.freshPrefixLaw initialPrefix.latestState steps).map
    (EventPrefix.spliceFresh initialPrefix)

/-- Exact finite absolute-prefix law for splicing a fresh-clock event
continuation after an old prefix, including horizons before the splice point. -/
def splicedFreshAbsolutePrefixLawFrom (policy : A.EventHistoryPolicy)
    (start : ℕ) (initialPrefix : A.EventPrefix start) (horizon : ℕ) :
    FiniteLaw (A.EventPrefix horizon) :=
  if horizon_le : horizon ≤ start then
    FiniteLaw.pure (EventPrefix.truncate initialPrefix horizon horizon_le)
  else
    (policy.freshSplicedPrefixLawFrom start initialPrefix
      (horizon - start)).map fun history index =>
        history (Fin.cast (by omega) index)

@[simp]
theorem splicedFreshAbsolutePrefixLawFrom_of_le
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (horizon : ℕ)
    (horizon_le : horizon ≤ start) :
    policy.splicedFreshAbsolutePrefixLawFrom start initialPrefix horizon =
      FiniteLaw.pure
        (EventPrefix.truncate initialPrefix horizon horizon_le) := by
  simp [splicedFreshAbsolutePrefixLawFrom, horizon_le]

/-- Executing with action memory and then observing one state coordinate
agrees with the state-history specialization. -/
theorem toEventHistoryPolicy_stateCoordinateLawFrom
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (coordinate : Fin (start + steps + 1)) :
    (policy.toEventHistoryPolicy).stateCoordinateLawFrom
        start initialPrefix steps coordinate =
      policy.coordinateLawFrom start initialPrefix.states steps coordinate := by
  have hprojection := congrArg
    (fun law : FiniteLaw (A.StatePrefix (start + steps)) =>
      law.map fun history => history coordinate)
    (toEventHistoryPolicy_prefixLawFrom_map_states
      policy start initialPrefix steps)
  simpa only [stateCoordinateLawFrom, eventCoordinateLawFrom,
    StateHistoryPolicy.coordinateLawFrom, FiniteLaw.map_comp,
    Function.comp_def, EventPrefix.states] using hprojection

@[simp]
theorem freshPrefixLaw_zero (policy : A.EventHistoryPolicy) (state : A.State) :
    policy.freshPrefixLaw state 0 =
      FiniteLaw.pure (EventPrefix.initial state) :=
  rfl

@[simp]
theorem freshPrefixLaw_succ (policy : A.EventHistoryPolicy) (state : A.State)
    (steps : ℕ) :
    policy.freshPrefixLaw state (steps + 1) =
      (policy.freshPrefixLaw state steps).bind fun history =>
        (policy.stoppedStepLaw steps history).map history.snoc :=
  rfl

@[simp]
theorem freshSplicedPrefixLawFrom_zero (policy : A.EventHistoryPolicy)
    (start : ℕ) (initialPrefix : A.EventPrefix start) :
    policy.freshSplicedPrefixLawFrom start initialPrefix 0 =
      FiniteLaw.pure initialPrefix := by
  rw [freshSplicedPrefixLawFrom, freshPrefixLaw_zero,
    FiniteLaw.pure_map]
  congr
  funext index
  let oldIndex : Fin (start + 1) := Fin.cast (by omega) index
  have happend := Fin.append_left initialPrefix
    (Fin.tail (EventPrefix.initial initialPrefix.latestState)) oldIndex
  simpa [EventPrefix.spliceFresh, oldIndex] using happend

end EventHistoryPolicy

end KernelArena
