/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory

/-!
# Discrete history-dependent stochastic execution

This module is the executable finite-history kernel for `KernelArena`.  A
state-history policy may inspect the complete finite state history and its
absolute time.  An event-history policy may additionally inspect every
selected action occurrence.  Both policies return exact `FiniteLaw` values
only at nonterminal prefixes.

The action layer uses `Option (FiniteLaw A.ActionBundle)`: `none` means that
the latest state has an empty action type.  It is not confused with a
normalized law on an empty type.  State and event execution instead absorb at
terminal states, extending their fixed-length prefixes by the current state
and by an event with no incoming action, respectively.

The recursive executors retain their initial history and use the absolute time
`start + elapsed`; continuation therefore does not silently restart the
policy clock.  No state-space `Fintype` or `DecidableEq` instance is required.

## Main definitions

* `KernelArena.StateHistoryPolicy` and `EventHistoryPolicy`;
* `StateHistoryPolicy.actionLaw?` and `EventHistoryPolicy.actionLaw?`;
* terminal-absorbing state and action-recording event step laws;
* `statePrefixLawFrom` and `eventPrefixLawFrom` for bounded execution;
* `StateHistoryPolicy.toEventHistoryPolicy` for the state-history special case.

All declarations in this file are executable.  Measure and kernel
interpretations belong to the analytic correspondence layer.
-/

namespace KernelArena

universe uS uA

/-- The dependent carrier of a state together with one legal action. -/
abbrev ActionBundle (A : KernelArena) :=
  Σ state, A.Action state

/-- A complete state history through the absolute coordinate `time`. -/
abbrev StatePrefix (A : KernelArena) (time : ℕ) :=
  Fin (time + 1) → A.State

/-- A state and the incoming selected action occurrence, if there was one. -/
abbrev PathEvent (A : KernelArena) :=
  A.State × (Unit ⊕ A.ActionBundle)

/-- A complete action-recording event history through `time`. -/
abbrev EventPrefix (A : KernelArena) (time : ℕ) :=
  Fin (time + 1) → A.PathEvent

namespace StatePrefix

variable {A : KernelArena} {time : ℕ}

/-- The state at the last coordinate of a nonempty indexed history. -/
def latest (history : A.StatePrefix time) : A.State :=
  history (Fin.last time)

/-- The singleton history at absolute coordinate zero. -/
def initial (state : A.State) : A.StatePrefix 0 :=
  fun _ => state

/-- Extend a complete history by one successor state. -/
def snoc (history : A.StatePrefix time) (state : A.State) :
    A.StatePrefix (time + 1) :=
  Fin.snoc history state

@[simp]
theorem latest_initial (state : A.State) :
    (initial state).latest = state :=
  rfl

@[simp]
theorem latest_snoc (history : A.StatePrefix time) (state : A.State) :
    (history.snoc state).latest = state := by
  simp [latest, snoc]

end StatePrefix

namespace PathEvent

variable {A : KernelArena}

/-- The state stored by an action-recording event. -/
def state (event : A.PathEvent) : A.State :=
  event.1

/-- The optional incoming action occurrence stored by an event. -/
def action (event : A.PathEvent) : Unit ⊕ A.ActionBundle :=
  event.2

/-- The initial or terminal-absorption event at a state. -/
def initial (state : A.State) : A.PathEvent :=
  (state, Sum.inl ())

/-- Record an action occurrence beside the successor it generated. -/
def after
    (source : A.State) (selected : A.Action source)
    (target : A.State) : A.PathEvent :=
  (target, Sum.inr ⟨source, selected⟩)

@[simp]
theorem state_initial (state : A.State) :
    (initial state : A.PathEvent).state = state :=
  rfl

@[simp]
theorem state_after
    (source : A.State) (selected : A.Action source)
    (target : A.State) :
    (after source selected target : A.PathEvent).state = target :=
  rfl

end PathEvent

namespace EventPrefix

variable {A : KernelArena} {time : ℕ}

/-- The event at the last coordinate of a nonempty indexed history. -/
def latest (history : A.EventPrefix time) : A.PathEvent :=
  history (Fin.last time)

/-- The state stored in the last event of a history. -/
def latestState (history : A.EventPrefix time) : A.State :=
  history.latest.state

/-- The singleton event history rooted at one state. -/
def initial (state : A.State) : A.EventPrefix 0 :=
  fun _ => PathEvent.initial state

/-- Extend a complete event history by one event. -/
def snoc (history : A.EventPrefix time) (event : A.PathEvent) :
    A.EventPrefix (time + 1) :=
  Fin.snoc history event

/-- Forget all recorded actions while retaining every state coordinate. -/
def states (history : A.EventPrefix time) : A.StatePrefix time :=
  fun index => (history index).state

@[simp]
theorem latest_initial (state : A.State) :
    (initial state).latest = PathEvent.initial state :=
  rfl

@[simp]
theorem latestState_initial (state : A.State) :
    (initial state).latestState = state :=
  rfl

@[simp]
theorem latest_snoc (history : A.EventPrefix time) (event : A.PathEvent) :
    (history.snoc event).latest = event := by
  simp [latest, snoc]

@[simp]
theorem latestState_snoc
    (history : A.EventPrefix time) (event : A.PathEvent) :
    (history.snoc event).latestState = event.state := by
  simp [latestState]

@[simp]
theorem states_initial (state : A.State) :
    (initial state).states = StatePrefix.initial state :=
  rfl

@[simp]
theorem states_snoc (history : A.EventPrefix time) (event : A.PathEvent) :
    (history.snoc event).states = history.states.snoc event.state := by
  funext index
  cases index using Fin.lastCases <;>
    simp [states, snoc, StatePrefix.snoc]

@[simp]
theorem latest_states (history : A.EventPrefix time) :
    history.states.latest = history.latestState :=
  rfl

end EventPrefix

/-- An exact finite action policy on complete state prefixes.

The proof argument makes a normalized action law unnecessary at terminal
prefixes.  The policy may depend on absolute time and every prior state. -/
abbrev StateHistoryPolicy (A : KernelArena) :=
  (time : ℕ) → (history : A.StatePrefix time) →
    ¬ IsEmpty (A.Action history.latest) →
      FiniteLaw (A.Action history.latest)

/-- An exact finite action policy on complete action-recording event prefixes.

This is strictly more informative than `StateHistoryPolicy`: two prefixes
with equal states may still contain different selected-action occurrences. -/
abbrev EventHistoryPolicy (A : KernelArena) :=
  (time : ℕ) → (history : A.EventPrefix time) →
    ¬ IsEmpty (A.Action history.latestState) →
      FiniteLaw (A.Action history.latestState)

namespace StateHistoryPolicy

variable {A : KernelArena}

/-- The bundled action law at a state history, or `none` exactly at a terminal
history. -/
def actionLaw?
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time) :
    Option (FiniteLaw A.ActionBundle) :=
  if hterminal : IsEmpty (A.Action history.latest) then
    none
  else
    some <| (policy time history hterminal).map fun action =>
      ⟨history.latest, action⟩

/-- The successor-state law at a known nonterminal state history. -/
def stepLaw
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latest)) :
    FiniteLaw A.State :=
  (policy time history hnonterminal).bind
    (A.next history.latest)

/-- One terminal-absorbing successor-state step. -/
def stoppedStepLaw
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time) : FiniteLaw A.State :=
  if hterminal : IsEmpty (A.Action history.latest) then
    FiniteLaw.pure history.latest
  else
    policy.stepLaw time history hterminal

@[simp]
theorem actionLaw?_eq_none_iff
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time) :
    policy.actionLaw? time history = none ↔
      IsEmpty (A.Action history.latest) := by
  simp [actionLaw?]

@[simp]
theorem actionLaw?_of_nonterminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latest)) :
    policy.actionLaw? time history =
      some ((policy time history hnonterminal).map fun action =>
        (⟨history.latest, action⟩ : A.ActionBundle)) := by
  simp [actionLaw?, hnonterminal]

@[simp]
theorem stoppedStepLaw_of_terminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time)
    (hterminal : IsEmpty (A.Action history.latest)) :
    policy.stoppedStepLaw time history = FiniteLaw.pure history.latest := by
  simp [stoppedStepLaw, hterminal]

@[simp]
theorem stoppedStepLaw_of_nonterminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.StatePrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latest)) :
    policy.stoppedStepLaw time history =
      policy.stepLaw time history hnonterminal := by
  simp [stoppedStepLaw, hnonterminal]

/-- Execute a state-history policy for a bounded number of transitions while
retaining the complete incoming history and the absolute clock. -/
def prefixLawFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) :
    (steps : ℕ) → FiniteLaw (A.StatePrefix (start + steps))
  | 0 => FiniteLaw.pure initialPrefix
  | steps + 1 =>
      (policy.prefixLawFrom start initialPrefix steps).bind fun history =>
        (policy.stoppedStepLaw (start + steps) history).map history.snoc

@[simp]
theorem prefixLawFrom_zero
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) :
    policy.prefixLawFrom start initialPrefix 0 =
      FiniteLaw.pure initialPrefix :=
  rfl

@[simp]
theorem prefixLawFrom_succ
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    policy.prefixLawFrom start initialPrefix (steps + 1) =
      (policy.prefixLawFrom start initialPrefix steps).bind fun history =>
        (policy.stoppedStepLaw (start + steps) history).map history.snoc :=
  rfl

/-- Regard a state-history policy as an event-history policy by forgetting
all recorded actions before choosing the next action. -/
def toEventHistoryPolicy
    (policy : A.StateHistoryPolicy) : A.EventHistoryPolicy :=
  fun time history hnonterminal =>
    policy time history.states (by simpa using hnonterminal)

end StateHistoryPolicy

namespace Policy

variable {A : KernelArena}

/-- A Markov policy is the state-history policy which reads only the latest
state and ignores both the absolute clock and the earlier prefix. -/
def toStateHistoryPolicy (policy : A.Policy) : A.StateHistoryPolicy :=
  fun _time history hnonterminal =>
    policy history.latest hnonterminal

/-- The history-policy step of an embedded Markov policy is the established
`KernelArena.stepLaw`. -/
theorem toStateHistoryPolicy_stepLaw
    (policy : A.Policy) (time : ℕ) (history : A.StatePrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latest)) :
    policy.toStateHistoryPolicy.stepLaw time history hnonterminal =
      A.stepLaw policy history.latest hnonterminal :=
  rfl

/-- At one bounded step, the new terminal-absorbing history executor agrees
with the established state executor for a Markov policy. -/
theorem toStateHistoryPolicy_stoppedStepLaw
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.Policy) (time : ℕ) (history : A.StatePrefix time) :
    policy.toStateHistoryPolicy.stoppedStepLaw time history =
      A.stateLawFrom policy 1 history.latest := by
  by_cases hterminal : IsEmpty (A.Action history.latest)
  · rw [StateHistoryPolicy.stoppedStepLaw_of_terminal
      _ _ _ hterminal]
    simp [stateLawFrom, hterminal]
  · rw [StateHistoryPolicy.stoppedStepLaw_of_nonterminal
      _ _ _ hterminal]
    simp [stateLawFrom, hterminal, toStateHistoryPolicy_stepLaw]

/-- A terminal state remains a point law for every horizon in the established
Markov executor. -/
theorem stateLawFrom_of_terminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.Policy) (state : A.State)
    (hterminal : IsEmpty (A.Action state)) :
    ∀ horizon, A.stateLawFrom policy horizon state = FiniteLaw.pure state := by
  intro horizon
  cases horizon with
  | zero => rfl
  | succ horizon => simp [stateLawFrom, hterminal]

/-- The established Markov state executor composes by addition of horizons.
This is the endpoint-level law used to compare it with prefix-retaining
history execution. -/
theorem stateLawFrom_add
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.Policy) (state : A.State) (first second : ℕ) :
    A.stateLawFrom policy (first + second) state =
      (A.stateLawFrom policy first state).bind
        (A.stateLawFrom policy second) := by
  induction first generalizing state with
  | zero => simp [stateLawFrom]
  | succ first ih =>
      by_cases hterminal : IsEmpty (A.Action state)
      · rw [Nat.succ_add]
        rw [stateLawFrom_of_terminal policy state hterminal]
        rw [stateLawFrom_of_terminal policy state hterminal]
        simp [stateLawFrom_of_terminal policy state hterminal]
      · rw [Nat.succ_add]
        simp only [stateLawFrom]
        simp [hterminal, FiniteLaw.bind_bind]
        apply congrArg
          (fun continuation =>
            (A.stepLaw policy state hterminal).bind continuation)
        funext nextState
        exact ih nextState

/-- The endpoint of the prefix-retaining history executor for an embedded
Markov policy is exactly the pre-existing `stateLawFrom` result at every
horizon. -/
theorem toStateHistoryPolicy_prefixLawFrom_map_latest
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.Policy) (start : ℕ)
    (initialPrefix : A.StatePrefix start) (steps : ℕ) :
    (policy.toStateHistoryPolicy.prefixLawFrom
        start initialPrefix steps).map StatePrefix.latest =
      A.stateLawFrom policy steps initialPrefix.latest := by
  induction steps with
  | zero =>
      rw [StateHistoryPolicy.prefixLawFrom_zero]
      exact FiniteLaw.pure_map _ _
  | succ steps ih =>
      rw [StateHistoryPolicy.prefixLawFrom_succ]
      rw [FiniteLaw.map_bind]
      have hmap (history : A.StatePrefix (start + steps)) :
          (policy.toStateHistoryPolicy.stoppedStepLaw
              (start + steps) history).map
                (fun state => (history.snoc state).latest) =
            policy.toStateHistoryPolicy.stoppedStepLaw
              (start + steps) history := by
        simp only [StatePrefix.latest_snoc]
        exact FiniteLaw.map_id _
      simp_rw [FiniteLaw.map_comp]
      simp only [Function.comp_def]
      simp_rw [hmap, toStateHistoryPolicy_stoppedStepLaw]
      have hbind := congrArg
        (fun law : FiniteLaw A.State =>
          law.bind (A.stateLawFrom policy 1))
        ih
      dsimp only at hbind
      rw [FiniteLaw.bind_map] at hbind
      calc
        _ = (A.stateLawFrom policy steps initialPrefix.latest).bind
              (A.stateLawFrom policy 1) := by
            simpa only [Function.comp_apply] using hbind
        _ = A.stateLawFrom policy (steps + 1)
              initialPrefix.latest :=
            (stateLawFrom_add
              policy initialPrefix.latest steps 1).symm

end Policy

namespace EventHistoryPolicy

variable {A : KernelArena}

/-- The bundled selected-action law at an event history, or `none` exactly at a
terminal history. -/
def actionLaw?
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) :
    Option (FiniteLaw A.ActionBundle) :=
  if hterminal : IsEmpty (A.Action history.latestState) then
    none
  else
    some <| (policy time history hterminal).map fun action =>
      ⟨history.latestState, action⟩

/-- The action-recording event law at a known nonterminal history. -/
def stepLaw
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    FiniteLaw A.PathEvent :=
  (policy time history hnonterminal).bind fun action =>
    (A.next history.latestState action).map
      (PathEvent.after history.latestState action)

/-- One terminal-absorbing action-recording event step. -/
def stoppedStepLaw
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) : FiniteLaw A.PathEvent :=
  if hterminal : IsEmpty (A.Action history.latestState) then
    FiniteLaw.pure (PathEvent.initial history.latestState)
  else
    policy.stepLaw time history hterminal

@[simp]
theorem actionLaw?_eq_none_iff
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) :
    policy.actionLaw? time history = none ↔
      IsEmpty (A.Action history.latestState) := by
  simp [actionLaw?]

@[simp]
theorem actionLaw?_of_nonterminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    policy.actionLaw? time history =
      some ((policy time history hnonterminal).map fun action =>
        (⟨history.latestState, action⟩ : A.ActionBundle)) := by
  simp [actionLaw?, hnonterminal]

@[simp]
theorem stoppedStepLaw_of_terminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time)
    (hterminal : IsEmpty (A.Action history.latestState)) :
    policy.stoppedStepLaw time history =
      FiniteLaw.pure (PathEvent.initial history.latestState) := by
  simp [stoppedStepLaw, hterminal]

@[simp]
theorem stoppedStepLaw_of_nonterminal
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    policy.stoppedStepLaw time history =
      policy.stepLaw time history hnonterminal := by
  simp [stoppedStepLaw, hnonterminal]

/-- Execute an event-history policy for a bounded number of transitions while
retaining every incoming event and the absolute clock. -/
def prefixLawFrom
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) :
    (steps : ℕ) → FiniteLaw (A.EventPrefix (start + steps))
  | 0 => FiniteLaw.pure initialPrefix
  | steps + 1 =>
      (policy.prefixLawFrom start initialPrefix steps).bind fun history =>
        (policy.stoppedStepLaw (start + steps) history).map history.snoc

@[simp]
theorem prefixLawFrom_zero
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) :
    policy.prefixLawFrom start initialPrefix 0 =
      FiniteLaw.pure initialPrefix :=
  rfl

@[simp]
theorem prefixLawFrom_succ
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    policy.prefixLawFrom start initialPrefix (steps + 1) =
      (policy.prefixLawFrom start initialPrefix steps).bind fun history =>
        (policy.stoppedStepLaw (start + steps) history).map history.snoc :=
  rfl

/-- Forgetting the recorded action from one nonterminal event step gives the
state step induced by the corresponding state-history policy. -/
theorem toEventHistoryPolicy_stepLaw_map_state
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    ((policy.toEventHistoryPolicy).stepLaw time history hnonterminal).map
        PathEvent.state =
      policy.stepLaw time history.states (by simpa using hnonterminal) := by
  simp only [stepLaw, StateHistoryPolicy.toEventHistoryPolicy,
    StateHistoryPolicy.stepLaw, FiniteLaw.map_bind]
  apply congrArg
  funext action
  rw [FiniteLaw.map_comp]
  change (A.next history.latestState action).map id =
    A.next history.latestState action
  exact FiniteLaw.map_id _

/-- The same state projection equality holds for the terminal-absorbing step.
-/
theorem toEventHistoryPolicy_stoppedStepLaw_map_state
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) :
    ((policy.toEventHistoryPolicy).stoppedStepLaw time history).map
        PathEvent.state =
      policy.stoppedStepLaw time history.states := by
  by_cases hterminal : IsEmpty (A.Action history.latestState)
  · rw [stoppedStepLaw_of_terminal _ _ _ hterminal]
    rw [StateHistoryPolicy.stoppedStepLaw_of_terminal]
    · rw [FiniteLaw.pure_map]
      rfl
    · simpa using hterminal
  · rw [stoppedStepLaw_of_nonterminal _ _ _ hterminal]
    rw [StateHistoryPolicy.stoppedStepLaw_of_nonterminal]
    exact toEventHistoryPolicy_stepLaw_map_state
      policy time history hterminal

/-- Recording every selected action is semantically conservative: after any
bounded number of steps, forgetting those occurrences gives exactly the state
history law computed directly from the same state-history policy. -/
theorem toEventHistoryPolicy_prefixLawFrom_map_states
    [(state : A.State) → Decidable (IsEmpty (A.Action state))]
    (policy : A.StateHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    ((policy.toEventHistoryPolicy).prefixLawFrom
        start initialPrefix steps).map EventPrefix.states =
      policy.prefixLawFrom start initialPrefix.states steps := by
  induction steps with
  | zero =>
      rw [prefixLawFrom_zero, StateHistoryPolicy.prefixLawFrom_zero]
      exact FiniteLaw.pure_map _ _
  | succ steps ih =>
      rw [prefixLawFrom_succ, StateHistoryPolicy.prefixLawFrom_succ]
      rw [FiniteLaw.map_bind]
      simp_rw [FiniteLaw.map_comp]
      simp only [Function.comp_def, EventPrefix.states_snoc]
      have hmap (history : A.EventPrefix (start + steps)) :
          ((policy.toEventHistoryPolicy).stoppedStepLaw
              (start + steps) history).map
                (fun event => history.states.snoc event.state) =
            (((policy.toEventHistoryPolicy).stoppedStepLaw
                (start + steps) history).map PathEvent.state).map
              history.states.snoc := by
        rw [FiniteLaw.map_comp]
        rfl
      simp_rw [hmap]
      simp_rw [toEventHistoryPolicy_stoppedStepLaw_map_state]
      have hbind := congrArg
        (fun law : FiniteLaw (A.StatePrefix (start + steps)) =>
          law.bind fun history =>
            (policy.stoppedStepLaw (start + steps) history).map
              history.snoc)
        ih
      dsimp only at hbind
      rw [FiniteLaw.bind_map] at hbind
      simpa only [Function.comp_apply] using hbind

end EventHistoryPolicy

end KernelArena
