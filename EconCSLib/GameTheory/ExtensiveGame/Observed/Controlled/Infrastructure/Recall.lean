/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# Payoff-free recall infrastructure

Personal-decision histories, classic recall, asynchronous private/public
signal recall, event-clock specializations, no-absent-mindedness, and their
factorization certificates.
The event-clock trace appends one signal at every arena transition and
therefore reveals transition count. `SignalTraceBuilder` is an optional
external asynchronous trace layer whose `eventSignal` may return `none` for a
silent event. The always-emitting builder recovers the event-clock trace; no
equivalence with arbitrary silent-event recall is claimed.

Recall uses the general `DecisionInfoWitness` and `RepresentedInfo` from the
carrier module and has no finite-EFG, structural history-length, or execution
dependency.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-! ## Classic, private-signal, and public recall -/

/-- One remembered information-state/action pair. -/
abbrev PersonalDecision
    (G : ControlledObservedGame N) (i : N) :=
  Σ information : G.RepresentedInfo i,
    G.InfoAction i information.1

/-- Package the abstract decision represented by a concrete action. -/
def personalDecisionAt
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History)
    (hmover : G.base.mover history.1 = some i)
    (action : G.base.Action history.1) :
    G.PersonalDecision i :=
  let hdecision : G.base.toArena.IsDecision history.1 := ⟨action⟩
  ⟨G.representedInfoAt history i hmover hdecision,
    (G.actionEquiv history i hmover hdecision).symm action⟩

/-- Packaging an action just realized from the information fiber recovers
that information/action pair. -/
@[simp]
theorem personalDecisionAt_actionEquiv
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1)
    (action :
      G.InfoAction i (G.infoAt history i hmover hdecision)) :
    G.personalDecisionAt i history hmover
        (G.actionEquiv history i hmover hdecision action) =
      ⟨G.representedInfoAt history i hmover hdecision, action⟩ := by
  simp [personalDecisionAt]

/-- Path-recursive worker extracting one player's past decisions. -/
def ownDecisionHistoryPath [DecidableEq N]
    (G : ControlledObservedGame N) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (G.PersonalDecision i)
  | _, .nil => []
  | _, @Arena.History.snoc _ _ state path action =>
      let previous : G.base.History := ⟨state, path⟩
      if hmover : G.base.mover state = some i then
        G.ownDecisionHistoryPath i path ++
          [G.personalDecisionAt i previous hmover action]
      else
        G.ownDecisionHistoryPath i path

/-- Ordered sequence of a player's past information/action decisions. -/
def ownDecisionHistory [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History) :
    List (G.PersonalDecision i) :=
  G.ownDecisionHistoryPath i history.2

/-- A concrete occurrence of one remembered personal decision in a complete
history. -/
structure PersonalDecisionOccurrence
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History)
    (decision : G.PersonalDecision i) where
  /-- State at which the remembered decision occurred. -/
  state : G.base.State
  /-- Prefix ending at that decision state. -/
  before : G.base.toArena.History G.base.init state
  /-- Player `i` controls the occurrence. -/
  mover : G.base.mover state = some i
  /-- Concrete action chosen at the occurrence. -/
  action : G.base.Action state
  /-- Suffix following the remembered action. -/
  after :
    G.base.toArena.History
      (G.base.next state action) history.1
  /-- Prefix, action, and suffix reconstruct the complete history. -/
  path_eq :
    (before.snoc action).append after = history.2
  /-- The concrete occurrence represents the requested abstract decision. -/
  decision_eq :
    G.personalDecisionAt
        i ⟨state, before⟩ mover action =
      decision

/-- Every remembered personal decision has a concrete occurrence in the
underlying occurrence-sensitive history. -/
theorem exists_personalDecisionOccurrence_of_mem
    [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History)
    (decision : G.PersonalDecision i)
    (hmem : decision ∈ G.ownDecisionHistory i history) :
    Nonempty
      (G.PersonalDecisionOccurrence i history decision) := by
  obtain ⟨finish, path⟩ := history
  induction path with
  | nil =>
      simp [ownDecisionHistory, ownDecisionHistoryPath] at hmem
  | @snoc state path action ih =>
      let previous : G.base.History := ⟨state, path⟩
      by_cases hmover : G.base.mover state = some i
      · simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]
          at hmem
        rcases hmem with hprevious | hcurrent
        · obtain ⟨occurrence⟩ := ih hprevious
          exact
            ⟨{
              state := occurrence.state
              before := occurrence.before
              mover := occurrence.mover
              action := occurrence.action
              after := occurrence.after.snoc action
              path_eq := by
                rw [Arena.History.append_snoc,
                  occurrence.path_eq]
              decision_eq := occurrence.decision_eq
            }⟩
        · have hdecision :
              G.personalDecisionAt
                  i previous hmover action =
                decision := hcurrent.symm
          exact
            ⟨{
              state := state
              before := path
              mover := hmover
              action := action
              after := Arena.History.nil
              path_eq := by simp
              decision_eq := hdecision
            }⟩
      · simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]
          at hmem
        obtain ⟨occurrence⟩ := ih hmem
        exact
          ⟨{
            state := occurrence.state
            before := occurrence.before
            mover := occurrence.mover
            action := occurrence.action
            after := occurrence.after.snoc action
            path_eq := by
              rw [Arena.History.append_snoc,
                occurrence.path_eq]
            decision_eq := occurrence.decision_eq
          }⟩

@[simp]
theorem ownDecisionHistory_nil [DecidableEq N]
    (G : ControlledObservedGame N) (i : N) :
    G.ownDecisionHistory i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) = [] :=
  rfl

@[simp]
theorem ownDecisionHistory_snoc_of_mover [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state = some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ ++
        [G.personalDecisionAt i ⟨state, path⟩ hmover action] := by
  simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]

@[simp]
theorem ownDecisionHistory_snoc_of_not_mover [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state ≠ some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ := by
  simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]

/-- Appending a legal suffix cannot shorten remembered own decisions. -/
theorem ownDecisionHistory_length_le_append [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    {middle finish : G.base.State}
    (basePath :
      G.base.toArena.History G.base.init middle)
    (suffix :
      G.base.toArena.History middle finish) :
    (G.ownDecisionHistory i ⟨middle, basePath⟩).length ≤
      (G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩).length := by
  induction suffix with
  | nil =>
      exact Nat.le_refl _
  | @snoc state suffix action ih =>
      rw [Arena.History.append_snoc]
      by_cases hmover : G.base.mover state = some i
      · rw [G.ownDecisionHistory_snoc_of_mover
          i (basePath.append suffix) action hmover]
        rw [List.length_append, List.length_singleton]
        exact ih.trans (Nat.le_succ _)
      · rw [G.ownDecisionHistory_snoc_of_not_mover
          i (basePath.append suffix) action hmover]
        exact ih

/-- A continuation extends, rather than rewrites, every player's remembered
personal-decision history. -/
theorem ownDecisionHistory_prefix_append
    [DecidableEq N]
    (G : ControlledObservedGame N) (i : N)
    {middle finish : G.base.State}
    (basePath :
      G.base.toArena.History G.base.init middle)
    (suffix :
      G.base.toArena.History middle finish) :
    G.ownDecisionHistory i
        ⟨middle, basePath⟩ <+:
      G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩ := by
  induction suffix with
  | nil =>
      exact List.prefix_refl _
  | @snoc state suffix action ih =>
      rw [Arena.History.append_snoc]
      by_cases hmover : G.base.mover state = some i
      · rw [G.ownDecisionHistory_snoc_of_mover
          i (basePath.append suffix) action hmover]
        exact ih.trans (List.prefix_append _ _)
      · rw [G.ownDecisionHistory_snoc_of_not_mover
          i (basePath.append suffix) action hmover]
        exact ih

/-- Classic perfect recall of one's own previous information and actions. -/
def HasPerfectRecall [DecidableEq N]
    (G : ControlledObservedGame N) (i : N) : Prop :=
  ∀ (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_decision : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_decision : G.base.toArena.IsDecision second.1),
    G.infoAt first i hfirst hfirst_decision =
        G.infoAt second i hsecond hsecond_decision →
      G.ownDecisionHistory i first =
        G.ownDecisionHistory i second

/-- Every player has classic perfect recall. -/
def PerfectRecall [DecidableEq N]
    (G : ControlledObservedGame N) : Prop :=
  ∀ i, G.HasPerfectRecall i

/-- Equal information at decisions determines the complete history. -/
def HasSingletonInformation
    (G : ControlledObservedGame N) (i : N) : Prop :=
  ∀ (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_decision : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_decision : G.base.toArena.IsDecision second.1),
    G.infoAt first i hfirst hfirst_decision =
        G.infoAt second i hsecond hsecond_decision →
      first = second

/-- Every player has singleton decision information. -/
def PerfectInformation
    (G : ControlledObservedGame N) : Prop :=
  ∀ i, G.HasSingletonInformation i

/-- Singleton decision information implies classic perfect recall. -/
theorem HasSingletonInformation.hasPerfectRecall [DecidableEq N]
    {i : N} (h : G.HasSingletonInformation i) :
    G.HasPerfectRecall i := by
  intro first second hfirst hfirst_nonterminal hsecond
    hsecond_nonterminal hsame
  exact congrArg (G.ownDecisionHistory i)
    (h first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame)

/-- A player never revisits the same decision information after acting. -/
def HasNoAbsentMindedness
    (G : ControlledObservedGame N) (i : N) : Prop :=
  ∀ (first : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (action : G.base.Action first.1)
    (finish : G.base.State)
    (suffix :
      G.base.toArena.History
        (G.base.next first.1 action) finish)
    (hsecond : G.base.mover finish = some i)
    (hsecond_decision : G.base.toArena.IsDecision finish),
    G.infoAt first i hfirst
        ⟨action⟩ ≠
      G.infoAt
        ⟨finish, (first.2.snoc action).append suffix⟩
        i hsecond hsecond_decision

/-- Under no absent-mindedness, an earlier remembered information state
differs from the current decision information state. -/
theorem HasNoAbsentMindedness.info_ne_of_mem_ownDecisionHistory
    [DecidableEq N]
    {i : N}
    (hnoAbsent : G.HasNoAbsentMindedness i)
    (history : G.base.History)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1)
    (decision : G.PersonalDecision i)
    (hmem : decision ∈ G.ownDecisionHistory i history) :
    decision.1 ≠ G.representedInfoAt history i hmover hdecision := by
  obtain ⟨occurrence⟩ :=
    G.exists_personalDecisionOccurrence_of_mem
      i history decision hmem
  have hdistinct :=
    hnoAbsent
      ⟨occurrence.state, occurrence.before⟩
      occurrence.mover occurrence.action
      history.1 occurrence.after hmover hdecision
  rw [occurrence.path_eq] at hdistinct
  have hfirst :
      G.representedInfoAt
          ⟨occurrence.state, occurrence.before⟩
          i occurrence.mover
          ⟨occurrence.action⟩ =
        decision.1 :=
    by
      simpa [personalDecisionAt] using
        congrArg Sigma.fst occurrence.decision_eq
  intro hequal
  exact hdistinct (congrArg Subtype.val (hfirst.trans hequal))

/-- No player is absent-minded. -/
def NoAbsentMindedness
    (G : ControlledObservedGame N) : Prop :=
  ∀ i, G.HasNoAbsentMindedness i

/-- Classic perfect recall rules out absent-mindedness. -/
theorem HasPerfectRecall.hasNoAbsentMindedness [DecidableEq N]
    {i : N} (hrecall : G.HasPerfectRecall i) :
    G.HasNoAbsentMindedness i := by
  intro first hfirst action finish suffix hsecond
    hsecond_nonterminal hsame
  let afterFirst : G.base.History :=
    ⟨G.base.next first.1 action, first.2.snoc action⟩
  let second : G.base.History :=
    ⟨finish, (first.2.snoc action).append suffix⟩
  have hstep :
      G.ownDecisionHistory i afterFirst =
        G.ownDecisionHistory i first ++
          [G.personalDecisionAt i first hfirst action] :=
    G.ownDecisionHistory_snoc_of_mover
      i first.2 action hfirst
  have htail :
      (G.ownDecisionHistory i afterFirst).length ≤
        (G.ownDecisionHistory i second).length :=
    G.ownDecisionHistory_length_le_append
      i (first.2.snoc action) suffix
  have hstrict :
      (G.ownDecisionHistory i first).length <
        (G.ownDecisionHistory i second).length := by
    rw [hstep] at htail
    simpa using htail
  have hequal :=
    hrecall first second hfirst
      ⟨action⟩
      hsecond hsecond_nonterminal hsame
  rw [hequal] at hstrict
  exact Nat.lt_irrefl _ hstrict

/-- Private observations along a complete history, including both endpoints. -/
def signalHistoryPath
    (G : ControlledObservedGame N) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (G.Observation i)
  | _, .nil =>
      [G.observe i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)]
  | _, @Arena.History.snoc _ _ state path action =>
      G.signalHistoryPath i path ++
        [G.observe i
          ⟨G.base.next state action, path.snoc action⟩]

/-- Private-signal sequence of a complete history. -/
def signalHistory
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History) :
    List (G.Observation i) :=
  G.signalHistoryPath i history.2

@[simp]
theorem signalHistory_nil
    (G : ControlledObservedGame N) (i : N) :
    G.signalHistory i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      [G.observe i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)] :=
  rfl

@[simp]
theorem signalHistory_snoc
    (G : ControlledObservedGame N) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state) :
    G.signalHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.signalHistory i ⟨state, path⟩ ++
        [G.observe i
          ⟨G.base.next state action, path.snoc action⟩] :=
  rfl

/-- Public observations along a complete history. -/
def publicSignalHistoryPath
    (G : ControlledObservedGame N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List G.PublicObservation
  | _, .nil =>
      [G.publicObserve
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)]
  | _, @Arena.History.snoc _ _ state path action =>
      G.publicSignalHistoryPath path ++
        [G.publicObserve
          ⟨G.base.next state action, path.snoc action⟩]

/-- Public-signal sequence of a complete history. -/
def publicSignalHistory
    (G : ControlledObservedGame N)
    (history : G.base.History) :
    List G.PublicObservation :=
  G.publicSignalHistoryPath history.2

@[simp]
theorem publicSignalHistory_nil
    (G : ControlledObservedGame N) :
    G.publicSignalHistory
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      [G.publicObserve
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)] :=
  rfl

@[simp]
theorem publicSignalHistory_snoc
    (G : ControlledObservedGame N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state) :
    G.publicSignalHistory
        ⟨G.base.next state action, path.snoc action⟩ =
      G.publicSignalHistory ⟨state, path⟩ ++
        [G.publicObserve
          ⟨G.base.next state action, path.snoc action⟩] :=
  rfl

/-! ### Optional silent-event signal traces -/

/-- External builder for player-indexed signal traces.

The builder is not part of the minimal observed-game carrier. `eventSignal`
returns `none` for a silent transition and `some signal` for a disclosed
event, so trace length need not reveal the number of Arena transitions. -/
structure SignalTraceBuilder (G : ControlledObservedGame N) where
  /-- Signal carrier for each player. -/
  Signal : N → Type*
  /-- Initial signal before any transition. -/
  initial : (i : N) → Signal i
  /-- Optional signal emitted by one legal transition. -/
  eventSignal :
    (i : N) →
      (history : G.base.History) →
        G.base.Action history.1 → Option (Signal i)

namespace SignalTraceBuilder

/-- Trace built along one dependent history, omitting silent events. -/
def tracePath
    (builder : G.SignalTraceBuilder) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (builder.Signal i)
  | _, .nil => [builder.initial i]
  | _, @Arena.History.snoc _ _ state path action =>
      builder.tracePath i path ++
        (builder.eventSignal i ⟨state, path⟩ action).toList

/-- Signal trace of a complete history. -/
def trace
    (builder : G.SignalTraceBuilder) (i : N)
    (history : G.base.History) :
    List (builder.Signal i) :=
  builder.tracePath i history.2

/-- Recall relative to an external, possibly silent-event trace builder. -/
def HasPerfectRecall
    (builder : G.SignalTraceBuilder) (i : N) : Prop :=
  ∀ (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_decision : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_decision : G.base.toArena.IsDecision second.1),
    G.infoAt first i hfirst hfirst_decision =
        G.infoAt second i hsecond hsecond_decision →
      builder.trace i first = builder.trace i second

end SignalTraceBuilder

/-- External builder for a public signal trace with optional silent events.

Unlike `publicSignalHistory`, the trace does not append at every Arena
transition. Its length therefore need not reveal a public clock. -/
structure PublicSignalTraceBuilder (G : ControlledObservedGame N) where
  /-- Public signal carrier. -/
  Signal : Type*
  /-- Initial public signal before any transition. -/
  initial : Signal
  /-- Optional public signal emitted by one legal transition. -/
  eventSignal :
    (history : G.base.History) →
      G.base.Action history.1 → Option Signal

namespace PublicSignalTraceBuilder

/-- Public trace built along one dependent history, omitting silent events. -/
def tracePath
    (builder : G.PublicSignalTraceBuilder) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List builder.Signal
  | _, .nil => [builder.initial]
  | _, @Arena.History.snoc _ _ state path action =>
      builder.tracePath path ++
        (builder.eventSignal ⟨state, path⟩ action).toList

/-- Asynchronous public trace of a complete history. -/
def trace
    (builder : G.PublicSignalTraceBuilder)
    (history : G.base.History) :
    List builder.Signal :=
  builder.tracePath history.2

/-- Current public observation determines an external public trace, without
assuming that every transition emits a signal. -/
def HasPerfectRecall
    (builder : G.PublicSignalTraceBuilder) : Prop :=
  ∀ first second : G.base.History,
    G.publicObserve first = G.publicObserve second →
      builder.trace first = builder.trace second

end PublicSignalTraceBuilder

/-- The existing observation sequence as an event-clock trace builder.

Every Arena transition emits exactly one private observation. -/
def eventClockSignalTraceBuilder
    (G : ControlledObservedGame N) :
    G.SignalTraceBuilder where
  Signal := G.Observation
  initial := fun i =>
    G.observe i
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
  eventSignal := fun i history action =>
    some
      (G.observe i
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩)

/-- Event-clock trace construction is definitionally the existing private
signal history after structural recursion. -/
theorem eventClockSignalTraceBuilder_trace
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History) :
    (G.eventClockSignalTraceBuilder.trace i history) =
      G.signalHistory i history := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | snoc path action ih =>
      simp only [SignalTraceBuilder.trace,
        SignalTraceBuilder.tracePath, eventClockSignalTraceBuilder,
        Option.toList_some, signalHistory, signalHistoryPath]
      exact congrArg (fun trace => trace ++ [_]) ih

/-- The existing public-observation sequence as an always-emitting public
trace builder. -/
def eventClockPublicSignalTraceBuilder
    (G : ControlledObservedGame N) :
    G.PublicSignalTraceBuilder where
  Signal := G.PublicObservation
  initial :=
    G.publicObserve
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
  eventSignal := fun history action =>
    some
      (G.publicObserve
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩)

/-- The always-emitting public trace is the existing event-clock public signal
history. -/
theorem eventClockPublicSignalTraceBuilder_trace
    (G : ControlledObservedGame N)
    (history : G.base.History) :
    G.eventClockPublicSignalTraceBuilder.trace history =
      G.publicSignalHistory history := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | snoc path action ih =>
      simp only [PublicSignalTraceBuilder.trace,
        PublicSignalTraceBuilder.tracePath,
        eventClockPublicSignalTraceBuilder,
        Option.toList_some, publicSignalHistory,
        publicSignalHistoryPath]
      exact congrArg (fun trace => trace ++ [_]) ih

/-- The private-signal sequence factors through current decision information
under the event-clock convention: the initial observation is recorded and
every Arena transition appends exactly one signal. -/
def HasEventClockSignalPerfectRecall
    (G : ControlledObservedGame N) (i : N) : Prop :=
  ∀ (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_decision : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_decision : G.base.toArena.IsDecision second.1),
    G.infoAt first i hfirst hfirst_decision =
        G.infoAt second i hsecond hsecond_decision →
      G.signalHistory i first =
        G.signalHistory i second

/-- Event-clock signal recall is precisely recall for the always-emitting
external trace builder. No equivalence is asserted for builders with silent
events. -/
theorem hasEventClockSignalPerfectRecall_iff
    (G : ControlledObservedGame N) (i : N) :
    G.HasEventClockSignalPerfectRecall i ↔
      G.eventClockSignalTraceBuilder.HasPerfectRecall i := by
  constructor
  · intro hrecall first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame
    rw [G.eventClockSignalTraceBuilder_trace i first,
      G.eventClockSignalTraceBuilder_trace i second]
    exact hrecall first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame
  · intro hrecall first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame
    rw [← G.eventClockSignalTraceBuilder_trace i first,
      ← G.eventClockSignalTraceBuilder_trace i second]
    exact hrecall first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame

/-- Every player has private-signal recall. -/
def EventClockSignalPerfectRecall
    (G : ControlledObservedGame N) : Prop :=
  ∀ i, G.HasEventClockSignalPerfectRecall i

/-- Current public observation determines the complete public-signal sequence
under the event-clock convention. Because one public observation is appended
at every Arena transition, this predicate exposes event count. -/
def HasEventClockPublicPerfectRecall
    (G : ControlledObservedGame N) : Prop :=
  ∀ first second : G.base.History,
    G.publicObserve first = G.publicObserve second →
      G.publicSignalHistory first =
        G.publicSignalHistory second

/-- Event-clock public recall is exactly asynchronous public recall for the
always-emitting builder. Builders with silent events impose no public clock. -/
theorem hasEventClockPublicPerfectRecall_iff
    (G : ControlledObservedGame N) :
    G.HasEventClockPublicPerfectRecall ↔
      G.eventClockPublicSignalTraceBuilder.HasPerfectRecall := by
  constructor
  · intro hrecall first second hsame
    rw [G.eventClockPublicSignalTraceBuilder_trace first,
      G.eventClockPublicSignalTraceBuilder_trace second]
    exact hrecall first second hsame
  · intro hrecall first second hsame
    rw [← G.eventClockPublicSignalTraceBuilder_trace first,
      ← G.eventClockPublicSignalTraceBuilder_trace second]
    exact hrecall first second hsame

/-- Singleton decision information implies private-signal recall. -/
theorem HasSingletonInformation.hasEventClockSignalPerfectRecall
    {i : N} (hinformation : G.HasSingletonInformation i) :
    G.HasEventClockSignalPerfectRecall i := by
  intro first second hfirst hfirst_nonterminal hsecond
    hsecond_nonterminal hsame
  exact congrArg (G.signalHistory i)
    (hinformation first second hfirst hfirst_nonterminal
      hsecond hsecond_nonterminal hsame)

/-- Private signal histories have one more coordinate than action histories. -/
theorem signalHistory_length
    (G : ControlledObservedGame N) (i : N)
    (history : G.base.History) :
    (G.signalHistory i history).length =
      history.2.length + 1 := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | snoc path action ih =>
      change
        (G.signalHistoryPath i path).length =
          path.length + 1 at ih
      simp [signalHistory, signalHistoryPath, ih,
        Nat.add_assoc]

/-- A public signal history has one more coordinate than its action history. -/
theorem publicSignalHistory_length
    (G : ControlledObservedGame N)
    (history : G.base.History) :
    (G.publicSignalHistory history).length =
      history.2.length + 1 := by
  rcases history with ⟨finish, path⟩
  induction path with
  | nil => rfl
  | snoc path action ih =>
      change
        (G.publicSignalHistoryPath path).length =
          path.length + 1 at ih
      simp [publicSignalHistory,
        publicSignalHistoryPath, ih, Nat.add_assoc]

/-- Signal recall rules out absent-mindedness because every action adds one
signal coordinate. -/
theorem HasEventClockSignalPerfectRecall.hasNoAbsentMindedness
    {i : N} (hrecall : G.HasEventClockSignalPerfectRecall i) :
    G.HasNoAbsentMindedness i := by
  intro first hfirst action finish suffix hsecond
    hsecond_nonterminal hsame
  let second : G.base.History :=
    ⟨finish, (first.2.snoc action).append suffix⟩
  have hsignals :=
    hrecall first second hfirst
      ⟨action⟩
      hsecond hsecond_nonterminal hsame
  have hfirstLength := G.signalHistory_length i first
  have hsecondLength := G.signalHistory_length i second
  have hpathLength :
      second.2.length =
        first.2.length + 1 + suffix.length := by
    simp [second, Nat.add_assoc]
  have hequalLength := congrArg List.length hsignals
  rw [hfirstLength, hsecondLength, hpathLength] at hequalLength
  omega

/-- Perfect information implies private-signal recall for every player. -/
theorem PerfectInformation.eventClockSignalPerfectRecall
    (hinformation : G.PerfectInformation) :
    G.EventClockSignalPerfectRecall :=
  fun i => (hinformation i).hasEventClockSignalPerfectRecall

/-- Private-signal recall for every player implies global
no-absent-mindedness. -/
theorem EventClockSignalPerfectRecall.noAbsentMindedness
    (hrecall : G.EventClockSignalPerfectRecall) :
    G.NoAbsentMindedness :=
  fun i => (hrecall i).hasNoAbsentMindedness

/-- Factorization certificate for classic perfect recall. -/
structure RecallCertificate [DecidableEq N]
    (G : ControlledObservedGame N) where
  /-- Remembered own-decision trace for every information state. -/
  remembered :
    (i : N) → G.RepresentedInfo i →
      List (G.PersonalDecision i)
  /-- The assigned trace agrees at every represented decision. -/
  remembered_infoAt :
    ∀ (i : N) (history : G.base.History)
      (hmover : G.base.mover history.1 = some i)
      (hdecision : G.base.toArena.IsDecision history.1),
      remembered i (G.representedInfoAt history i hmover hdecision) =
        G.ownDecisionHistory i history

/-- A recall factorization certificate proves perfect recall. -/
theorem RecallCertificate.perfectRecall [DecidableEq N]
    (certificate : G.RecallCertificate) :
    G.PerfectRecall := by
  intro i first second hfirst hfirst_nonterminal hsecond
    hsecond_nonterminal hsame
  rw [← certificate.remembered_infoAt i first hfirst
    hfirst_nonterminal]
  rw [← certificate.remembered_infoAt i second hsecond
    hsecond_nonterminal]
  exact congrArg (certificate.remembered i) (Subtype.ext hsame)

/-- Perfect recall is equivalent to the existence of a factorization
certificate.  The reverse implication is purely propositional: representative
choice is confined to this theorem and is never projected as executable
data. -/
theorem recallCertificate_nonempty_iff_perfectRecall
    [DecidableEq N]
    (G : ControlledObservedGame N) :
    Nonempty G.RecallCertificate ↔ G.PerfectRecall := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.perfectRecall
  · intro hrecall
    classical
    refine ⟨{
      remembered := fun i information =>
        G.ownDecisionHistory i
          (Classical.choice information.2).history
      remembered_infoAt := ?_ }⟩
    intro i history hmover hdecision
    let information := G.representedInfoAt history i hmover hdecision
    let witness := Classical.choice information.2
    exact
      hrecall i
        witness.history history
        witness.mover witness.decision
        hmover hdecision
        witness.infoAt_eq

/-- Factorization certificate for payoff-free private-signal recall. -/
structure SignalRecallCertificate
    (G : ControlledObservedGame N) where
  /-- Signal sequence assigned to every decision information state. -/
  rememberedSignals :
    (i : N) → G.RepresentedInfo i →
      List (G.Observation i)
  /-- The assigned sequence agrees with every represented decision history. -/
  rememberedSignals_infoAt :
    ∀ (i : N) (history : G.base.History)
      (hmover : G.base.mover history.1 = some i)
      (hdecision : G.base.toArena.IsDecision history.1),
      rememberedSignals i
        (G.representedInfoAt history i hmover hdecision) =
        G.signalHistory i history

/-- A payoff-free private-signal factorization certificate proves signal
recall. -/
theorem SignalRecallCertificate.eventClockSignalPerfectRecall
    (certificate : G.SignalRecallCertificate) :
    G.EventClockSignalPerfectRecall := by
  intro i first second hfirst hfirst_nonterminal hsecond
    hsecond_nonterminal hsame
  rw [← certificate.rememberedSignals_infoAt i first hfirst
    hfirst_nonterminal]
  rw [← certificate.rememberedSignals_infoAt i second hsecond
    hsecond_nonterminal]
  exact congrArg (certificate.rememberedSignals i) (Subtype.ext hsame)

/-- Factorization certificate for payoff-free public recall. -/
structure PublicRecallCertificate
    (G : ControlledObservedGame N) where
  /-- Public-signal sequence assigned to each current public observation. -/
  rememberedPublicSignals :
    G.PublicObservation → List G.PublicObservation
  /-- The assigned sequence agrees with every represented history. -/
  rememberedPublicSignals_publicObserve :
    ∀ history : G.base.History,
      rememberedPublicSignals (G.publicObserve history) =
        G.publicSignalHistory history

/-- A payoff-free public-signal factorization certificate proves public
recall. -/
theorem PublicRecallCertificate.hasEventClockPublicPerfectRecall
    (certificate : G.PublicRecallCertificate) :
    G.HasEventClockPublicPerfectRecall := by
  intro first second hsame
  rw [← certificate.rememberedPublicSignals_publicObserve first]
  rw [← certificate.rememberedPublicSignals_publicObserve second]
  rw [hsame]

end ExtensiveGame.ControlledObservedGame
