/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw

/-!
# Finite complete event paths from bounded discrete execution

This module turns a bounded action-recording `KernelArena` execution into a
finite law of on-demand complete event paths.  Execution starts from a supplied
absolute event prefix, so policies continue to see the original clock and all
earlier action occurrences.  Each finite outcome is replayed at its original
absolute coordinates; after its last coordinate the replay emits the initial
marker at the terminal endpoint forever.

The construction does not create an action law at terminal states.  The
underlying `EventHistoryPolicy.prefixLawFrom` uses its terminal-absorbing event
step, and the correctness results require an explicit certificate saying that
every positive atom at the selected bound is terminal.  Zero-weight unfinished
atoms may remain in the sparse representation.

The returned law has function-valued outcomes but remains executable: mapping
the finite atom list never compares paths for equality, and a coordinate query
only tests whether it lies inside the stored prefix.  This owner is measure-free.

## Main definitions

* `EventHistoryPolicy.IsLegalAbsorbingTransition` is the positive-support
  relation of one terminal-aware event step;
* `EventHistoryPolicy.IsLegalPrefixFrom` records exact stepwise legality from a
  supplied absolute prefix;
* `FiniteCompleteEventPath.replay` replays a finite event prefix and absorbs at
  its endpoint;
* `FiniteCompleteEventPath.law` maps bounded execution to complete paths;
* `FiniteCompleteEventPath.stateLaw` explicitly forgets recorded actions only
  after the complete event-path law has been constructed;
* `law_prefix`, `law_eventCoordinate`, and `law_stateCoordinate` prove exact
  finite-query consistency;
* `law_legal`, `law_absorbs_after`, and `law_terminal` certify positive paths.
-/

namespace KernelArena

namespace EventHistoryPolicy

variable {A : KernelArena}
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- One event is a legal terminal-absorbing successor of a complete prefix
when it has positive mass in the executable stopped-step law. -/
def IsLegalAbsorbingTransition
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) (nextEvent : A.PathEvent) : Prop :=
  (policy.stoppedStepLaw time history).HasPositiveAtom nextEvent

/-- The operational support relation records either terminal absorption or a
positive policy action followed by a positive transition atom. -/
theorem isLegalAbsorbingTransition_iff
    (policy : A.EventHistoryPolicy) (time : ℕ)
    (history : A.EventPrefix time) (nextEvent : A.PathEvent) :
    policy.IsLegalAbsorbingTransition time history nextEvent ↔
      (IsEmpty (A.Action history.latestState) ∧
          nextEvent = PathEvent.initial history.latestState) ∨
        ∃ hnonterminal : ¬ IsEmpty (A.Action history.latestState),
          ∃ action,
            (policy time history hnonterminal).HasPositiveAtom action ∧
              ∃ target,
                (A.next history.latestState action).HasPositiveAtom target ∧
                  PathEvent.after history.latestState action target =
                    nextEvent := by
  by_cases hterminal : IsEmpty (A.Action history.latestState)
  · rw [IsLegalAbsorbingTransition,
      policy.stoppedStepLaw_of_terminal time history hterminal]
    simp [hterminal]
  · rw [IsLegalAbsorbingTransition,
      policy.stoppedStepLaw_of_nonterminal time history hterminal]
    simp only [stepLaw, FiniteLaw.hasPositiveAtom_bind_iff,
      FiniteLaw.hasPositiveAtom_map_iff]
    simp [hterminal]

/-- A finite event prefix extends the supplied absolute prefix and every new
coordinate has positive mass in the stopped-step law selected by its complete
preceding prefix. -/
def IsLegalPrefixFrom
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) {steps : ℕ}
    (history : A.EventPrefix (start + steps)) : Prop :=
  EventPrefix.truncate history start (by omega) = initialPrefix ∧
    ∀ offset : Fin steps,
      policy.IsLegalAbsorbingTransition (start + offset.1)
        (EventPrefix.truncate history (start + offset.1) (by omega))
        (history ⟨start + offset.1 + 1, by omega⟩)

/-- A complete event path retains the supplied absolute prefix and follows the
terminal-aware positive-support relation at every later absolute time. -/
def IsLegalAbsorbingPathFrom
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (path : ℕ → A.PathEvent) : Prop :=
  (fun index : Fin (start + 1) ↦ path index.1) = initialPrefix ∧
    ∀ time, start ≤ time →
      policy.IsLegalAbsorbingTransition time
        (fun index : Fin (time + 1) ↦ path index.1)
        (path (time + 1))

end EventHistoryPolicy

namespace FiniteCompleteEventPath

variable {A : KernelArena}

/-- Restrict a complete event path to one absolute finite horizon. -/
def pathPrefix (path : ℕ → A.PathEvent) (time : ℕ) : A.EventPrefix time :=
  fun index ↦ path index.1

/-- Restrict a complete state path to one absolute finite horizon. -/
def statePathPrefix (path : ℕ → A.State) (time : ℕ) : A.StatePrefix time :=
  fun index ↦ path index.1

/-- Replay a retained absolute event prefix and emit terminal-absorption
markers after its final coordinate.  The final recorded action occurrence is
therefore preserved; absorption starts only at the following coordinate. -/
def replay {finish : ℕ} (history : A.EventPrefix finish) : ℕ → A.PathEvent :=
  fun time ↦
    if h : time ≤ finish then
      history ⟨time, Nat.lt_succ_iff.mpr h⟩
    else
      PathEvent.initial history.latestState

@[simp]
theorem replay_of_le {finish : ℕ} (history : A.EventPrefix finish)
    (time : ℕ) (h : time ≤ finish) :
    replay history time = history ⟨time, Nat.lt_succ_iff.mpr h⟩ := by
  simp [replay, h]

@[simp]
theorem replay_of_lt {finish : ℕ} (history : A.EventPrefix finish)
    (time : ℕ) (h : finish < time) :
    replay history time = PathEvent.initial history.latestState := by
  simp [replay, Nat.not_le.mpr h]

/-- Before the retained prefix ends, replay restriction is ordinary prefix
restriction. -/
theorem pathPrefix_replay {finish : ℕ} (history : A.EventPrefix finish)
    (time : ℕ) (h : time ≤ finish) :
    pathPrefix (replay history) time =
      EventPrefix.truncate history time h := by
  funext index
  change replay history index.1 = _
  rw [replay_of_le history index.1 (by omega)]
  rfl

@[simp]
theorem pathPrefix_replay_self {finish : ℕ}
    (history : A.EventPrefix finish) :
    pathPrefix (replay history) finish = history := by
  rw [pathPrefix_replay history finish le_rfl,
    EventPrefix.truncate_self]

@[simp]
theorem replay_finish {finish : ℕ} (history : A.EventPrefix finish) :
    replay history finish = history.latest := by
  rw [replay_of_le history finish le_rfl]
  congr 1

/-- Once the requested coordinate is past the stored prefix, its state is the
stored endpoint state. -/
theorem replay_state_of_finish_le {finish : ℕ}
    (history : A.EventPrefix finish) (time : ℕ) (h : finish ≤ time) :
    (replay history time).state = history.latestState := by
  rcases h.eq_or_lt with rfl | hlt
  · rw [replay_finish]
    rfl
  · rw [replay_of_lt history time hlt, PathEvent.state_initial]

/-- The latest state of every replayed prefix at or after the stored horizon
is the stored endpoint state. -/
theorem pathPrefix_replay_latestState_of_finish_le {finish : ℕ}
    (history : A.EventPrefix finish) (time : ℕ) (h : finish ≤ time) :
    (pathPrefix (replay history) time).latestState = history.latestState := by
  change (replay history time).state = history.latestState
  exact replay_state_of_finish_le history time h

/-- Extend a finite event prefix by repeated endpoint absorption markers.

The split `start + steps` index keeps the result definitionally aligned with
`prefixLawFrom start initialPrefix (steps + extra)`. -/
def absorbingPrefix {start steps : ℕ}
    (history : A.EventPrefix (start + steps)) :
    (extra : ℕ) → A.EventPrefix (start + (steps + extra))
  | 0 => history
  | extra + 1 =>
      (absorbingPrefix history extra).snoc
        (PathEvent.initial history.latestState)

@[simp]
theorem absorbingPrefix_zero {start steps : ℕ}
    (history : A.EventPrefix (start + steps)) :
    absorbingPrefix history 0 = history :=
  rfl

@[simp]
theorem absorbingPrefix_succ {start steps : ℕ}
    (history : A.EventPrefix (start + steps)) (extra : ℕ) :
    absorbingPrefix history (extra + 1) =
      (absorbingPrefix history extra).snoc
        (PathEvent.initial history.latestState) :=
  rfl

@[simp]
theorem absorbingPrefix_latestState {start steps : ℕ}
    (history : A.EventPrefix (start + steps)) (extra : ℕ) :
    (absorbingPrefix history extra).latestState = history.latestState := by
  induction extra with
  | zero => rfl
  | succ extra _ih =>
      rw [absorbingPrefix_succ, EventPrefix.latestState_snoc,
        PathEvent.state_initial]

/-- Restricting a replay after the retained horizon is exactly repeated
endpoint absorption. -/
theorem pathPrefix_replay_after {start steps : ℕ}
    (history : A.EventPrefix (start + steps)) (extra : ℕ) :
    pathPrefix (replay history) (start + (steps + extra)) =
      absorbingPrefix history extra := by
  induction extra with
  | zero => exact pathPrefix_replay_self history
  | succ extra ih =>
      rw [absorbingPrefix_succ]
      funext index
      refine Fin.lastCases ?_ (fun earlier ↦ ?_) index
      · change replay history (start + (steps + extra) + 1) = _
        rw [replay_of_lt history (start + (steps + extra) + 1) (by omega)]
        simpa only [EventPrefix.snoc] using
          (@Fin.snoc_last (start + (steps + extra) + 1)
            (fun _ ↦ A.PathEvent)
            (PathEvent.initial history.latestState)
            (absorbingPrefix history extra)).symm
      · change replay history earlier.1 = _
        simpa only [EventPrefix.snoc, Fin.snoc_castSucc] using
          congrFun ih earlier

section Execution

variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- Execute for `steps` absolute-clock transitions and replay every resulting
finite prefix as an on-demand terminal-absorbing complete event path. -/
def law (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    FiniteLaw (ℕ → A.PathEvent) :=
  (policy.prefixLawFrom start initialPrefix steps).map replay

/-- Complete state paths obtained by explicitly forgetting each recorded
action occurrence after constructing the complete event-path law.  This is a
finite law of function-valued atoms and remains executable. -/
def stateLaw (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) :
    FiniteLaw (ℕ → A.State) :=
  (law policy start initialPrefix steps).map fun path time ↦
    (path time).state

/-- The selected bound terminates every positive finite-prefix atom. -/
def PositiveSupportTerminates
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ) : Prop :=
  ∀ history,
    (policy.prefixLawFrom start initialPrefix steps).HasPositiveAtom history →
      IsEmpty (A.Action history.latestState)

/-- Every earlier absolute prefix of the complete-path law agrees semantically
with direct bounded execution. -/
theorem law_prefix (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (earlier extra : ℕ) :
    ((law policy start initialPrefix (earlier + extra)).map fun path ↦
        pathPrefix path (start + earlier)).Equivalent
      (policy.prefixLawFrom start initialPrefix earlier) := by
  rw [law, FiniteLaw.map_comp]
  have hfunction :
      ((fun path ↦ pathPrefix path (start + earlier)) ∘
        (replay : A.EventPrefix (start + (earlier + extra)) →
          ℕ → A.PathEvent)) =
      (fun history ↦
        EventPrefix.truncate history (start + earlier) (by omega)) := by
    funext history
    exact pathPrefix_replay history (start + earlier) (by omega)
  rw [hfunction]
  exact (policy.effectivePathLawFrom start initialPrefix).coherent earlier extra

/-- Every earlier absolute event coordinate has the same finite law as direct
bounded execution to that coordinate. -/
theorem law_eventCoordinate (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (earlier extra : ℕ)
    (coordinate : Fin (start + earlier + 1)) :
    ((law policy start initialPrefix (earlier + extra)).map fun path ↦
        path coordinate.1).Equivalent
      ((policy.prefixLawFrom start initialPrefix earlier).map fun history ↦
        history coordinate) := by
  have h := (law_prefix policy start initialPrefix earlier extra).map
    (fun history ↦ history coordinate)
  rw [FiniteLaw.map_comp] at h
  simpa only [Function.comp_apply, pathPrefix] using h

/-- State-coordinate laws are preserved after forgetting the recorded action
occurrence at the queried coordinate. -/
theorem law_stateCoordinate (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (earlier extra : ℕ)
    (coordinate : Fin (start + earlier + 1)) :
    ((law policy start initialPrefix (earlier + extra)).map fun path ↦
        (path coordinate.1).state).Equivalent
      ((policy.prefixLawFrom start initialPrefix earlier).map fun history ↦
        (history coordinate).state) := by
  have h :=
    (law_eventCoordinate policy start initialPrefix earlier extra coordinate).map
      PathEvent.state
  rw [FiniteLaw.map_comp, FiniteLaw.map_comp] at h
  simpa only [Function.comp_apply] using h

private def continuationPrefixLaw
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (first : ℕ) (initialPrefix : A.EventPrefix (start + first)) :
    (extra : ℕ) → FiniteLaw (A.EventPrefix (start + (first + extra)))
  | 0 => FiniteLaw.pure initialPrefix
  | extra + 1 =>
      (continuationPrefixLaw policy start first initialPrefix extra).bind
        fun history ↦
          (policy.stoppedStepLaw (start + (first + extra)) history).map
            history.snoc

private theorem prefixLawFrom_add
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (first second : ℕ) :
    policy.prefixLawFrom start initialPrefix (first + second) =
      (policy.prefixLawFrom start initialPrefix first).bind fun history ↦
        continuationPrefixLaw policy start first history second := by
  induction second with
  | zero =>
      simp only [Nat.add_zero, continuationPrefixLaw]
      change
        policy.prefixLawFrom start initialPrefix first =
          (policy.prefixLawFrom start initialPrefix first).bind FiniteLaw.pure
      exact (FiniteLaw.bind_pure _).symm
  | succ second ih =>
      change
        policy.prefixLawFrom start initialPrefix ((first + second) + 1) =
          (policy.prefixLawFrom start initialPrefix first).bind
            (fun history ↦
              (continuationPrefixLaw policy start first history second).bind
                fun previous ↦
                  (policy.stoppedStepLaw (start + (first + second)) previous).map
                    previous.snoc)
      rw [policy.prefixLawFrom_succ, ih, FiniteLaw.bind_bind]

/-- Starting from a terminal event prefix, bounded execution is the point law
of repeated endpoint absorption markers. -/
private theorem continuationPrefixLaw_of_terminal
    (policy : A.EventHistoryPolicy) {start first : ℕ}
    (history : A.EventPrefix (start + first))
    (hterminal : IsEmpty (A.Action history.latestState)) (extra : ℕ) :
    continuationPrefixLaw policy start first history extra =
      FiniteLaw.pure (absorbingPrefix history extra) := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [continuationPrefixLaw, ih, FiniteLaw.pure_bind,
        policy.stoppedStepLaw_of_terminal]
      · rw [FiniteLaw.pure_map]
        congr 2
        rw [absorbingPrefix_latestState]
      · simpa only [absorbingPrefix_latestState] using hterminal

/-- Once the selected positive support is terminal, every later absolute
prefix of the replay law agrees with direct terminal-absorbing execution. -/
theorem law_prefix_after (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (extra : ℕ) :
    ((law policy start initialPrefix steps).map fun path ↦
        pathPrefix path (start + (steps + extra))).Equivalent
      (policy.prefixLawFrom start initialPrefix (steps + extra)) := by
  let finalLaw := policy.prefixLawFrom start initialPrefix steps
  have hleft :
      (law policy start initialPrefix steps).map
          (fun path ↦ pathPrefix path (start + (steps + extra))) =
        finalLaw.map (fun history ↦ absorbingPrefix history extra) := by
    rw [law, FiniteLaw.map_comp]
    congr 1
    funext history
    exact pathPrefix_replay_after history extra
  rw [hleft, prefixLawFrom_add]
  rw [FiniteLaw.map_eq_bind_pure_comp]
  apply finalLaw.bind_congr_positive
  intro history hhistory
  apply FiniteLaw.Equivalent.of_eq
  change
    FiniteLaw.pure (absorbingPrefix history extra) =
      continuationPrefixLaw policy start steps history extra
  exact (continuationPrefixLaw_of_terminal policy history
    (terminated history hhistory) extra).symm

/-- With the positive-support termination certificate, the complete-path law
answers every finite absolute-prefix query exactly, on either side of the
selected termination bound. -/
theorem law_prefix_all (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) :
    ((law policy start initialPrefix steps).map fun path ↦
        pathPrefix path (start + querySteps)).Equivalent
      (policy.prefixLawFrom start initialPrefix querySteps) := by
  by_cases hquery : querySteps ≤ steps
  · obtain ⟨extra, hsteps⟩ := Nat.exists_eq_add_of_le hquery
    simpa only [hsteps] using
      law_prefix policy start initialPrefix querySteps extra
  · have hsteps : steps ≤ querySteps := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hsteps
    exact law_prefix_after policy start initialPrefix steps terminated extra

/-- Every finite absolute state-prefix query of the complete state-path law
agrees with state projection of direct action-recording execution, on either
side of the selected termination bound. -/
theorem stateLaw_prefix_all (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) :
    ((stateLaw policy start initialPrefix steps).map fun path ↦
        statePathPrefix path (start + querySteps)).Equivalent
      ((policy.prefixLawFrom start initialPrefix querySteps).map fun history ↦
        fun index ↦ (history index).state) := by
  have h :=
    (law_prefix_all policy start initialPrefix steps terminated querySteps).map
      (fun history index ↦ (history index).state)
  rw [FiniteLaw.map_comp] at h
  rw [stateLaw, FiniteLaw.map_comp]
  simpa only [Function.comp_apply, statePathPrefix, pathPrefix] using h

/-- Every absolute event-coordinate query agrees with direct execution, even
after the selected bound. -/
theorem law_eventCoordinate_all (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) (coordinate : Fin (start + querySteps + 1)) :
    ((law policy start initialPrefix steps).map fun path ↦
        path coordinate.1).Equivalent
      ((policy.prefixLawFrom start initialPrefix querySteps).map fun history ↦
        history coordinate) := by
  have h :=
    (law_prefix_all policy start initialPrefix steps terminated querySteps).map
      (fun history ↦ history coordinate)
  rw [FiniteLaw.map_comp] at h
  simpa only [Function.comp_apply, pathPrefix] using h

/-- Every absolute state-coordinate query agrees with direct execution, even
after the selected bound. -/
theorem law_stateCoordinate_all (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) (coordinate : Fin (start + querySteps + 1)) :
    ((law policy start initialPrefix steps).map fun path ↦
        (path coordinate.1).state).Equivalent
      ((policy.prefixLawFrom start initialPrefix querySteps).map fun history ↦
        (history coordinate).state) := by
  have h :=
    (law_eventCoordinate_all policy start initialPrefix steps terminated
      querySteps coordinate).map PathEvent.state
  rw [FiniteLaw.map_comp, FiniteLaw.map_comp] at h
  simpa only [Function.comp_apply] using h

/-- Every coordinate of the complete state-path law agrees with direct
action-recording execution followed by state projection. -/
theorem stateLaw_coordinate_all (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (querySteps : ℕ) (coordinate : Fin (start + querySteps + 1)) :
    ((stateLaw policy start initialPrefix steps).map fun path ↦
        path coordinate.1).Equivalent
      ((policy.prefixLawFrom start initialPrefix querySteps).map fun history ↦
        (history coordinate).state) := by
  rw [stateLaw, FiniteLaw.map_comp]
  simpa only [Function.comp_apply] using
    law_stateCoordinate_all policy start initialPrefix steps terminated
      querySteps coordinate

omit [(state : A.State) → Decidable (IsEmpty (A.Action state))] in
private theorem truncate_snoc {time horizon : ℕ}
    (history : A.EventPrefix time) (event : A.PathEvent)
    (horizon_le : horizon ≤ time) :
    EventPrefix.truncate (history.snoc event) horizon
        (horizon_le.trans (Nat.le_succ time)) =
      EventPrefix.truncate history horizon horizon_le := by
  funext index
  have hindex :
      Fin.castLE
          (Nat.succ_le_succ (horizon_le.trans (Nat.le_succ time))) index =
        (Fin.castLE (Nat.succ_le_succ horizon_le) index).castSucc := by
    apply Fin.ext
    rfl
  change (history.snoc event) _ = history _
  rw [hindex]
  simpa only [EventPrefix.snoc] using
    (@Fin.snoc_castSucc (time + 1) (fun _ ↦ A.PathEvent)
      event history (Fin.castLE (Nat.succ_le_succ horizon_le) index))

omit [(state : A.State) → Decidable (IsEmpty (A.Action state))] in
private theorem snoc_apply_of_le {time : ℕ}
    (history : A.EventPrefix time) (event : A.PathEvent)
    (coordinate : ℕ) (coordinate_le : coordinate ≤ time) :
    (history.snoc event) ⟨coordinate, by omega⟩ =
      history ⟨coordinate, Nat.lt_succ_iff.mpr coordinate_le⟩ := by
  change (history.snoc event) _ = history _
  have hindex :
      (⟨coordinate, by omega⟩ : Fin (time + 1 + 1)) =
        (⟨coordinate, Nat.lt_succ_iff.mpr coordinate_le⟩ :
          Fin (time + 1)).castSucc := by
    apply Fin.ext
    rfl
  rw [hindex]
  simpa only [EventPrefix.snoc] using
    (@Fin.snoc_castSucc (time + 1) (fun _ ↦ A.PathEvent)
      event history
      (⟨coordinate, Nat.lt_succ_iff.mpr coordinate_le⟩ : Fin (time + 1)))

omit [(state : A.State) → Decidable (IsEmpty (A.Action state))] in
private theorem snoc_apply_last {time : ℕ}
    (history : A.EventPrefix time) (event : A.PathEvent) :
    (history.snoc event) ⟨time + 1, by omega⟩ = event := by
  change (history.snoc event) _ = event
  have hindex :
      (⟨time + 1, by omega⟩ : Fin (time + 1 + 1)) =
        Fin.last (time + 1) := by
    apply Fin.ext
    rfl
  rw [hindex]
  simpa only [EventPrefix.snoc] using
    (@Fin.snoc_last (time + 1) (fun _ ↦ A.PathEvent) event history)

/-- Positive atoms of bounded execution retain the initial prefix and consist
entirely of positive terminal-aware event steps. -/
theorem positive_prefixLawFrom_isLegal
    (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (history : A.EventPrefix (start + steps))
    (hpositive :
      (policy.prefixLawFrom start initialPrefix steps).HasPositiveAtom history) :
    policy.IsLegalPrefixFrom start initialPrefix history := by
  induction steps with
  | zero =>
      rw [policy.prefixLawFrom_zero] at hpositive
      have heq := (FiniteLaw.hasPositiveAtom_pure_iff _ _).mp hpositive
      subst history
      constructor
      · exact EventPrefix.truncate_self initialPrefix
      · intro offset
        exact Fin.elim0 offset
  | succ steps ih =>
      rw [policy.prefixLawFrom_succ] at hpositive
      obtain ⟨previous, hprevious, hextension⟩ :=
        (FiniteLaw.hasPositiveAtom_bind_iff _ _ _).mp hpositive
      obtain ⟨event, hevent, hhistory⟩ :=
        (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hextension
      subst history
      have hlegal := ih previous hprevious
      constructor
      · rw [truncate_snoc previous event (by omega)]
        exact hlegal.1
      · intro offset
        refine Fin.lastCases ?_ (fun earlier ↦ ?_) offset
        · change
            policy.IsLegalAbsorbingTransition (start + steps)
              (EventPrefix.truncate (previous.snoc event) (start + steps)
                (by omega))
              ((previous.snoc event) ⟨start + steps + 1, by omega⟩)
          rw [truncate_snoc previous event le_rfl,
            EventPrefix.truncate_self, snoc_apply_last]
          exact hevent
        · change
            policy.IsLegalAbsorbingTransition (start + earlier.1)
              (EventPrefix.truncate (previous.snoc event)
                (start + earlier.1) (by omega))
              ((previous.snoc event)
                ⟨start + earlier.1 + 1, by omega⟩)
          rw [truncate_snoc previous event (by omega),
            snoc_apply_of_le previous event (start + earlier.1 + 1) (by omega)]
          exact hlegal.2 earlier

/-- Every positive complete replay extends the actual incoming absolute event
prefix. -/
theorem law_initialPrefix (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path) :
    pathPrefix path start = initialPrefix := by
  obtain ⟨history, hhistory, rfl⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  rw [pathPrefix_replay history start (by omega)]
  exact (positive_prefixLawFrom_isLegal
    policy start initialPrefix steps history hhistory).1

/-- The stored finite part of every positive complete replay is stepwise
legal. -/
theorem law_legalPrefix (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path) :
    policy.IsLegalPrefixFrom start initialPrefix
      (pathPrefix path (start + steps)) := by
  obtain ⟨history, hhistory, rfl⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  rw [pathPrefix_replay_self]
  exact positive_prefixLawFrom_isLegal
    policy start initialPrefix steps history hhistory

/-- A positive complete replay is terminal at the selected absolute bound. -/
theorem law_terminal (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path) :
    IsEmpty (A.Action (path (start + steps)).state) := by
  obtain ⟨history, hhistory, rfl⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  simpa only [replay_finish, EventPrefix.latestState] using
    terminated history hhistory

/-- After the selected bound, every positive replay emits the terminal
absorption marker while retaining the real final action occurrence at the
bound itself. -/
theorem law_absorbs_after (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path)
    (extra : ℕ) :
    path (start + steps + 1 + extra) =
      PathEvent.initial (path (start + steps)).state := by
  obtain ⟨history, _hhistory, rfl⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  rw [replay_of_lt history (start + steps + 1 + extra) (by omega),
    replay_finish]
  rfl

/-- Endpoint states stay fixed from the selected bound onward. -/
theorem law_state_absorbing (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path)
    (extra : ℕ) :
    (path (start + steps + extra)).state =
      (path (start + steps)).state := by
  cases extra with
  | zero => rfl
  | succ extra =>
      rw [show start + steps + (extra + 1) =
        start + steps + 1 + extra by omega,
        law_absorbs_after policy start initialPrefix steps path hpath extra,
        PathEvent.state_initial]

/-- Under the positive-support termination certificate, every positive replay
is a legal terminal-absorbing complete event path from the supplied absolute
prefix. -/
theorem law_legal (policy : A.EventHistoryPolicy) (start : ℕ)
    (initialPrefix : A.EventPrefix start) (steps : ℕ)
    (terminated : PositiveSupportTerminates policy start initialPrefix steps)
    (path : ℕ → A.PathEvent)
    (hpath : (law policy start initialPrefix steps).HasPositiveAtom path) :
    policy.IsLegalAbsorbingPathFrom start initialPrefix path := by
  obtain ⟨history, hhistory, rfl⟩ :=
    (FiniteLaw.hasPositiveAtom_map_iff _ _ _).mp hpath
  have hlegal := positive_prefixLawFrom_isLegal
    policy start initialPrefix steps history hhistory
  change
    pathPrefix (replay history) start = initialPrefix ∧
      ∀ time, start ≤ time →
        policy.IsLegalAbsorbingTransition time
          (pathPrefix (replay history) time)
          (replay history (time + 1))
  constructor
  · exact law_initialPrefix policy start initialPrefix steps
      (replay history)
      ((FiniteLaw.hasPositiveAtom_map_iff _ _ _).mpr
        ⟨history, hhistory, rfl⟩)
  · intro time hstart
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hstart
    by_cases hbefore : offset < steps
    · have hstep := hlegal.2 (⟨offset, hbefore⟩ : Fin steps)
      rw [pathPrefix_replay history (start + offset) (by omega),
        replay_of_le history (start + offset + 1) (by omega)]
      exact hstep
    · have hfinish : start + steps ≤ start + offset := by omega
      have hlatest :=
        pathPrefix_replay_latestState_of_finish_le history
          (start + offset) hfinish
      have hterminal :
          IsEmpty
            (A.Action
              (pathPrefix (replay history) (start + offset)).latestState) := by
        rw [hlatest]
        exact terminated history hhistory
      rw [EventHistoryPolicy.IsLegalAbsorbingTransition,
        policy.stoppedStepLaw_of_terminal (start + offset)
          (pathPrefix (replay history) (start + offset)) hterminal,
        replay_of_lt history (start + offset + 1) (by omega)]
      exact (FiniteLaw.hasPositiveAtom_pure_iff _ _).mpr (by
        rw [hlatest])

end Execution

end FiniteCompleteEventPath

end KernelArena
