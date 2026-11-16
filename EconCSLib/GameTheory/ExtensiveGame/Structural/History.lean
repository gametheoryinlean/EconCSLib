/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Structural.Reachability

/-!
# Payoff-free histories and history unfolding

An `Arena` state is a world state, not necessarily an occurrence in an
unrolled tree: different action paths may merge into one state.
`Arena.History A start endpoint` records one finite legal path, and
`Arena.unfoldFrom` uses complete histories as the states of a tree-shaped
Arena.

The construction does not assume finiteness, acyclicity, decidable
terminality, payoffs, objectives, or probability.

## Main definitions

* `Arena.History` — typed finite action histories.
* `Arena.HistoryFrom` — a history bundled with its endpoint.
* `Arena.unfoldFrom` — occurrence-sensitive history unfolding.
* `Arena.unfoldEndpoint` — projection back to the compact Arena.
* `ControlledGame.unfold` — payoff-free controlled history unfolding.
-/

namespace Arena

/-- A typed finite history in `A`, starting at `start` and ending at the state
indexed by the result type. -/
inductive History (A : Arena) (start : A.State) : A.State → Type _
  | nil : History A start start
  | snoc {state : A.State}
      (history : History A start state) (action : A.Action state) :
      History A start (A.next state action)

namespace History

variable {A : Arena} {start : A.State}

/-- Concatenate histories whose intermediate endpoint agrees. -/
def append {middle finish : A.State}
    (first : A.History start middle)
    (suffix : A.History middle finish) :
    A.History start finish :=
  match suffix with
  | .nil => first
  | .snoc rest action => (first.append rest).snoc action

@[simp]
theorem append_nil (first : A.History start middle) :
    first.append (History.nil : A.History middle middle) = first := rfl

@[simp]
theorem append_snoc (first : A.History start middle)
    (suffix : A.History middle finish) (action : A.Action finish) :
    first.append (suffix.snoc action) =
      (first.append suffix).snoc action := rfl

@[simp]
theorem append_assoc {middle finish last : A.State}
    (first : A.History start middle)
    (second : A.History middle finish)
    (third : A.History finish last) :
    (first.append second).append third =
      first.append (second.append third) := by
  induction third with
  | nil =>
      rfl
  | snoc third action ih =>
      simp only [append_snoc, ih]

/-- The number of transitions in a history. -/
def length : {state : A.State} → A.History start state → ℕ
  | _, .nil => 0
  | _, .snoc history _ => history.length + 1

@[simp]
theorem length_nil :
    (History.nil : A.History start start).length = 0 := rfl

@[simp]
theorem length_snoc (history : A.History start state)
    (action : A.Action state) :
    (history.snoc action).length = history.length + 1 := rfl

@[simp]
theorem length_append {middle finish : A.State}
    (first : A.History start middle)
    (suffix : A.History middle finish) :
    (first.append suffix).length = first.length + suffix.length := by
  induction suffix with
  | nil =>
      simp
  | snoc suffix action ih =>
      simp [ih, Nat.add_assoc]

/-- Forget action occurrences and retain endpoint reachability. -/
def toReachable {state : A.State} :
    (history : A.History start state) → A.Reachable start state
  | .nil => .refl _
  | .snoc history action => history.toReachable.step' action

end History

/-- Endpoint reachability is exactly the proposition that at least one typed
finite history connects the endpoints.

The `Nonempty` wrapper is essential: `Reachable` is proof-irrelevant, whereas
an Arena may have several distinguishable action histories with the same
start and endpoint. -/
theorem reachable_iff_nonempty_history
    (A : Arena) (start finish : A.State) :
    A.Reachable start finish ↔
      Nonempty (A.History start finish) := by
  constructor
  · intro reachable
    induction reachable with
    | refl =>
        exact ⟨History.nil⟩
    | @step source target action reachable ih =>
        rcases ih with ⟨suffix⟩
        exact
          ⟨(History.nil.snoc action).append suffix⟩
  · rintro ⟨history⟩
    exact history.toReachable

/-- A history from `start`, bundled with its endpoint. This is the state type
of the history unfolding. -/
abbrev HistoryFrom (A : Arena) (start : A.State) :=
  Σ state : A.State, A.History start state

/-- The empty history at `start`. -/
def HistoryFrom.nil (A : Arena) (start : A.State) : A.HistoryFrom start :=
  ⟨start, History.nil⟩

/-- Unroll an Arena from `start`, using complete histories as states.

Two histories remain distinct even when their endpoints in `A` are equal. -/
def unfoldFrom (A : Arena) (start : A.State) : Arena where
  State := A.HistoryFrom start
  Action := fun history => A.Action history.1
  next := fun history action =>
    ⟨A.next history.1 action, history.2.snoc action⟩

/-- Project a state of the history unfolding to its endpoint in the compact
Arena. -/
def unfoldEndpoint (A : Arena) (start : A.State) :
    (A.unfoldFrom start).State → A.State :=
  Sigma.fst

@[simp]
theorem unfoldEndpoint_nil (A : Arena) (start : A.State) :
    A.unfoldEndpoint start (HistoryFrom.nil A start) = start := rfl

@[simp]
theorem unfoldFrom_next (A : Arena) (start : A.State)
    (history : A.HistoryFrom start) (action : A.Action history.1) :
    (A.unfoldFrom start).next history action =
      ⟨A.next history.1 action, history.2.snoc action⟩ := rfl

@[simp]
theorem unfoldEndpoint_next (A : Arena) (start : A.State)
    (history : A.HistoryFrom start) (action : A.Action history.1) :
    A.unfoldEndpoint start
        ((A.unfoldFrom start).next history action) =
      A.next (A.unfoldEndpoint start history) action := rfl

@[simp]
theorem unfoldFrom_isTerminal_iff (A : Arena) (start : A.State)
    (history : A.HistoryFrom start) :
    (A.unfoldFrom start).IsTerminal history ↔
      A.IsTerminal (A.unfoldEndpoint start history) :=
  Iff.rfl

namespace History

variable {A : Arena} {start : A.State}

/-- Lift a suffix in the compact Arena to a history in the unfolding, starting
at the complete base history and ending at the appended complete history. -/
def liftAppend {middle finish : A.State}
    (baseHistory : A.History start middle)
    (suffix : A.History middle finish) :
    (A.unfoldFrom start).History
      ⟨middle, baseHistory⟩
      ⟨finish, baseHistory.append suffix⟩ :=
  match suffix with
  | .nil => .nil
  | .snoc rest action => (baseHistory.liftAppend rest).snoc action

@[simp]
theorem liftAppend_nil (baseHistory : A.History start middle) :
    baseHistory.liftAppend (History.nil : A.History middle middle) =
      History.nil := rfl

@[simp]
theorem liftAppend_snoc (baseHistory : A.History start middle)
    (suffix : A.History middle finish) (action : A.Action finish) :
    baseHistory.liftAppend (suffix.snoc action) =
      (baseHistory.liftAppend suffix).snoc action := rfl

@[simp]
theorem length_liftAppend {middle finish : A.State}
    (baseHistory : A.History start middle)
    (suffix : A.History middle finish) :
    (baseHistory.liftAppend suffix).length = suffix.length := by
  induction suffix with
  | nil =>
      rfl
  | snoc suffix action ih =>
      change (baseHistory.liftAppend suffix).length + 1 =
        suffix.length + 1
      rw [ih]

end History

/-- Every history-state is reachable from the empty history in the
unfolding. -/
theorem History.reachableInUnfolding (A : Arena) (start : A.State)
    {state : A.State} (history : A.History start state) :
    (A.unfoldFrom start).Reachable
      (HistoryFrom.nil A start) ⟨state, history⟩ := by
  induction history with
  | nil =>
      exact .refl _
  | snoc history action ih =>
      exact ih.step' action

end Arena

namespace ControlledGame

variable {N : Type*}

/-- Every nonterminal complete history generated from the root has a strategic
mover.

Unlike `ControlledGame.NoChance`, this predicate does not constrain
nonterminal ambient states that are unreachable from `G.init`. -/
def NoChanceOnHistories (G : ControlledGame N) : Prop :=
  ∀ history : G.toArena.HistoryFrom G.init,
    ¬ G.isTerminal history.1 →
      ∃ player : N, G.mover history.1 = some player

/-- A global no-chance game is no-chance on all rooted histories. -/
theorem NoChance.noChanceOnHistories
    {G : ControlledGame N} (hNoChance : G.NoChance) :
    G.NoChanceOnHistories :=
  fun history hnonterminal =>
    hNoChance history.1 hnonterminal

/-- Unroll a payoff-free controlled game into its complete-history tree.

Movers are read from endpoint world states, while histories with a shared
endpoint remain distinct unfolding states. -/
def unfold (G : ControlledGame N) : ControlledGame N where
  State := G.toArena.HistoryFrom G.init
  Action := fun history => G.Action history.1
  next := fun history action =>
    ⟨G.next history.1 action, history.2.snoc action⟩
  init := Arena.HistoryFrom.nil G.toArena G.init
  mover := fun history => G.mover history.1

@[simp]
theorem unfold_init (G : ControlledGame N) :
    G.unfold.init = Arena.HistoryFrom.nil G.toArena G.init :=
  rfl

@[simp]
theorem unfold_next (G : ControlledGame N)
    (history : G.toArena.HistoryFrom G.init)
    (action : G.Action history.1) :
    G.unfold.next history action =
      ⟨G.next history.1 action, history.2.snoc action⟩ :=
  rfl

@[simp]
theorem unfold_mover (G : ControlledGame N)
    (history : G.toArena.HistoryFrom G.init) :
    G.unfold.mover history = G.mover history.1 :=
  rfl

@[simp]
theorem unfold_isTerminal_iff
    (G : ControlledGame N)
    (history : G.toArena.HistoryFrom G.init) :
    G.unfold.isTerminal history ↔ G.isTerminal history.1 :=
  Iff.rfl

/-- Every state of the controlled history unfolding is reachable from its
empty-history root. -/
theorem unfold_isReachable (G : ControlledGame N)
    (history : G.toArena.HistoryFrom G.init) :
    G.unfold.IsReachable history :=
  history.2.reachableInUnfolding G.toArena G.init

end ControlledGame
