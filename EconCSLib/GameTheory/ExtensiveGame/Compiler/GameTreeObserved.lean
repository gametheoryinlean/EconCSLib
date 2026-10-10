/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
import EconCSLib.GameTheory.ExtensiveGame.Observed.SPE

/-!
# EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved

Compile a finite structural `GameTree` into an endpoint-observed
history-indexed extensive-game presentation.

A compiled state is a subtree.  At a node, a legal action is a child together
with evidence that it occurs in the node's nonempty child list.  Player and
public observations reveal the current subtree, while a decision information
state stores the full node context `(mover, head, tail)`.  Its indexed abstract
action type is definitionally the old `GameTree` child-choice type.

This compiler deliberately inherits the historical endpoint/global strategy
semantics: structurally equal subtree values have equal observations and node
information even when they occur at different complete histories. It is not
the canonical occurrence-sensitive perfect-information presentation. Use
`GameTreeOccurrenceObserved` when distinct history occurrences must be
distinguishable.

This module supplies validation targets for the observed-game design:

* one player's observed pure strategies are equivalent to
  `GameTree.PlayerStrategy`;
* stopped execution of a translated strategy reaches the same terminal payoff
  as `GameTree.outcome`;
* compiled histories correspond to `GameTree.Subtree` occurrences;
* the compiled game is pure terminating from every history root; and
* termination-certified observed Nash on presentation-designated
  continuations is equivalent to the existing root-scoped
  `GameTree.IsGlobalEndpointSubgamePerfectOn`.
-/

namespace GameTree

variable {N U : Type*}

/-! ### Base extensive game -/

/-- Legal actions in the Arena presentation of a tree. -/
def arenaAction : GameTree N U → Type _
  | .Leaf _ => PEmpty
  | .Node _ head tail => {child : GameTree N U // child ∈ head :: tail}

/-- Follow the child selected by a legal tree action. -/
def arenaNext :
    (g : GameTree N U) → arenaAction g → GameTree N U
  | .Leaf _, action => nomatch action
  | .Node _ _ _, action => action.1

/-- The root-independent Arena of `GameTree` states and child-selection
actions.  A particular compiled extensive game adds only its chosen initial
root, mover, and payoff fields. -/
def treeArena (N U : Type*) : Arena where
  State := GameTree N U
  Action := arenaAction
  next := arenaNext

/-- A total payoff field for the base `ExtensiveGame`.

Only leaf payoffs are semantically observed.  At a nonterminal node this picks
the head subtree's representative payoff solely to fill the deliberately total
base-game field. -/
def representativePayoff : GameTree N U → (N → U)
  | .Leaf payoff => payoff
  | .Node _ head _ => representativePayoff head

/-- View a finite structural tree as an `ExtensiveGame` whose states
are subtrees and whose actions select children. -/
def toExtensiveGame (root : GameTree N U) : ExtensiveGame N U where
  toArena := treeArena N U
  init := root
  mover
    | .Leaf _ => none
    | .Node mover _ _ => some mover
  payoff := representativePayoff

@[simp]
theorem toExtensiveGame_init (root : GameTree N U) :
    (toExtensiveGame root).init = root := rfl

@[simp]
theorem toExtensiveGame_action_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).Action (.Leaf payoff) = PEmpty := rfl

@[simp]
theorem toExtensiveGame_action_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    (toExtensiveGame root).Action (.Node mover head tail) =
      {child : GameTree N U // child ∈ head :: tail} := rfl

@[simp]
theorem toExtensiveGame_next_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
    (action : (toExtensiveGame root).Action (.Node mover head tail)) :
    (toExtensiveGame root).next (.Node mover head tail) action = action.1 := rfl

@[simp]
theorem toExtensiveGame_mover_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).mover (.Leaf payoff) = none := rfl

@[simp]
theorem toExtensiveGame_mover_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    (toExtensiveGame root).mover (.Node mover head tail) = some mover := rfl

@[simp]
theorem toExtensiveGame_payoff_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).payoff (.Leaf payoff) = payoff := rfl

/-- Leaves are terminal in the compiled base game. -/
theorem toExtensiveGame_isTerminal_leaf (root : GameTree N U)
    (payoff : N → U) :
    (toExtensiveGame root).isTerminal (.Leaf payoff) :=
  ⟨fun action => nomatch action⟩

/-- Nodes are nonterminal in the compiled base game. -/
theorem toExtensiveGame_not_isTerminal_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    ¬ (toExtensiveGame root).isTerminal (.Node mover head tail) := by
  intro hterminal
  exact hterminal.false ⟨head, List.mem_cons_self⟩

/-- Terminality of the compiled tree game is decidable by inspecting the
subtree constructor. -/
def toExtensiveGame_terminalDecidable (root : GameTree N U) :
    (g : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal g)
  | .Leaf payoff => isTrue (toExtensiveGame_isTerminal_leaf root payoff)
  | .Node mover head tail =>
      isFalse (toExtensiveGame_not_isTerminal_node root mover head tail)

instance toExtensiveGame.instTerminalDecidable (root : GameTree N U) :
    (g : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal g) :=
  toExtensiveGame_terminalDecidable root

/-- The compiled structural tree has no chance nodes. -/
theorem toExtensiveGame_noChance (root : GameTree N U) :
    (toExtensiveGame root).NoChance := by
  intro g hnonterminal
  cases g with
  | Leaf payoff =>
      exact (hnonterminal
        (toExtensiveGame_isTerminal_leaf root payoff)).elim
  | Node mover head tail =>
      exact ⟨mover, rfl⟩

/-- Reachable specialization of the compiled tree's ambient no-chance
certificate for canonical pure execution and equilibrium APIs. -/
theorem toExtensiveGame_noChanceOnHistories (root : GameTree N U) :
    (toExtensiveGame root).NoChanceOnHistories :=
  (toExtensiveGame_noChance root).noChanceOnHistories

/-! ### Histories and designated continuation roots -/

/-- The endpoint of every compiled Arena history is a subtree of the original
root. -/
theorem arenaHistory_subtree {root : GameTree N U} :
    ∀ {g : GameTree N U},
      (treeArena N U).History root g → Subtree g root
  | _, .nil =>
      Subtree.self root
  | _, @Arena.History.snoc _ _ current history action => by
      have ih := arenaHistory_subtree history
      cases current with
      | Leaf payoff =>
          exact nomatch action
      | Node mover head tail =>
          exact
            (Subtree.child_mem mover head tail action.2).trans ih

/-- Every subtree occurrence has at least one corresponding compiled Arena
history from the original root. -/
theorem Subtree.arenaHistory_nonempty {subtree root : GameTree N U}
    (hsubtree : Subtree subtree root) :
    Nonempty ((toExtensiveGame root).toArena.History root subtree) := by
  induction hsubtree with
  | refl =>
      exact ⟨Arena.History.nil⟩
  | inHead mover head tail _ ih =>
      obtain ⟨rest⟩ := ih
      let first :
          (toExtensiveGame (.Node mover head tail)).toArena.Action
            (.Node mover head tail) :=
        ⟨head, List.mem_cons_self⟩
      exact ⟨(Arena.History.nil.snoc first).append rest⟩
  | inTail mover head tail hmem _ ih =>
      obtain ⟨rest⟩ := ih
      let first :
          (toExtensiveGame (.Node mover head tail)).toArena.Action
            (.Node mover head tail) :=
        ⟨_, List.mem_cons_of_mem head hmem⟩
      exact ⟨(Arena.History.nil.snoc first).append rest⟩

/-! ### Endpoint observations and decision information -/

/-- A node context, used as the decision information state in the compiled
endpoint-observed game. Equal node-context values at different occurrences are
intentionally identified. -/
structure NodeInfo (N U : Type*) where
  mover : N
  head : GameTree N U
  tail : List (GameTree N U)

namespace NodeInfo

/-- Reconstruct the tree node represented by a decision information state. -/
def tree (I : NodeInfo N U) : GameTree N U :=
  .Node I.mover I.head I.tail

/-- Abstract actions at a node information state. -/
def Action (I : NodeInfo N U) : Type _ :=
  {child : GameTree N U // child ∈ I.head :: I.tail}

end NodeInfo

/-- Extract the node context at a compiled player-controlled state. -/
def nodeInfoAt (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    NodeInfo N U :=
  match g with
  | .Leaf _ => False.elim (by simp at hmover)
  | .Node mover head tail => ⟨mover, head, tail⟩

@[simp]
theorem nodeInfoAt_tree (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    (nodeInfoAt root g i hmover).tree = g := by
  cases g with
  | Leaf payoff =>
      simp at hmover
  | Node mover head tail =>
      rfl

/-- The node-context action type and compiled Arena action type agree at every
player-controlled state. -/
def nodeActionEquiv (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    (nodeInfoAt root g i hmover).Action ≃
      (toExtensiveGame root).Action g :=
  match g with
  | .Leaf _ => False.elim (by simp at hmover)
  | .Node _ _ _ => Equiv.refl _

/-- Compile a `GameTree` into an endpoint-observed extensive game.

Every player and the public observe the complete current subtree.  A
player-controlled history maps to the node context at its endpoint. Distinct
histories ending in structurally equal subtrees are not distinguished. -/
def toObservedGame (root : GameTree N U) :
    ExtensiveGame.ObservedGame N U where
  base := toExtensiveGame root
  Observation := fun _ => GameTree N U
  PublicObservation := GameTree N U
  observe := fun _ history => history.1
  publicObserve := fun history => history.1
  publicOf := fun _ observation => observation
  observe_public := by
    intro i history
    rfl
  InfoState := fun _ => NodeInfo N U
  infoObserve := fun _ info => info.tree
  infoAt := fun history i hmover _hnonterminal =>
    nodeInfoAt root history.1 i hmover
  infoAt_observe := fun history i hmover _hnonterminal =>
    nodeInfoAt_tree root history.1 i hmover
  InfoAction := fun _ info => info.Action
  actionEquiv := fun history i hmover _hnonterminal =>
    nodeActionEquiv root history.1 i hmover

instance toObservedGame.instTerminalDecidable (root : GameTree N U) :
    (g : (toObservedGame root).base.State) →
      Decidable ((toObservedGame root).base.isTerminal g) :=
  toExtensiveGame_terminalDecidable root

/-! ### Strategy correspondence -/

/-- Restrict a structural endpoint plan to node contexts represented by a
genuine decision history from `root`.  Unlike the former API, this is not
claimed to be an equivalence: an unrestricted `PlayerStrategy` also contains
irrelevant coordinates at node values that never occur below `root`. -/
def playerStrategyToObservedStrategy (root : GameTree N U) (i : N)
    (strategy : PlayerStrategy N U) :
    (toObservedGame root).PureStrategy i :=
  fun information =>
    strategy information.1.mover information.1.head information.1.tail

/-- Translate the old global tree strategy into an observed pure profile.
The outer player argument is irrelevant because the old global strategy
already dispatches on the mover stored in each node context. -/
def strategyToObservedProfile (root : GameTree N U) (σ : Strategy N U) :
    (toObservedGame root).PureProfile :=
  fun _ info => σ info.1.mover info.1.head info.1.tail

/-- Translate a strategic-form profile player by player into the observed
pure-profile type. -/
def playerProfileToObservedProfile (root : GameTree N U)
    (σ : N → PlayerStrategy N U) :
    (toObservedGame root).PureProfile :=
  fun i => playerStrategyToObservedStrategy root i (σ i)

/-- The terminal-aware base-history policy induced by a translated global
tree strategy. -/
def strategyHistoryPolicy (root : GameTree N U) (σ : Strategy N U) :
    (toExtensiveGame root).toArena.HistoryPolicy root :=
  (strategyToObservedProfile root σ).toHistoryPolicy
    (toObservedGame root) (toExtensiveGame_noChanceOnHistories root)

/-- The terminal-aware base-history policy induced by a translated
strategic-form player profile. -/
def playerProfileHistoryPolicy (root : GameTree N U)
    (σ : N → PlayerStrategy N U) :
    (toExtensiveGame root).toArena.HistoryPolicy root :=
  (playerProfileToObservedProfile root σ).toHistoryPolicy
    (toObservedGame root) (toExtensiveGame_noChanceOnHistories root)

/-- At a concrete node history, translating a global tree strategy prescribes
exactly its original child choice. -/
theorem strategyHistoryPolicy_node (root : GameTree N U)
    (σ : Strategy N U) (mover : N) (head : GameTree N U)
    (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root (.Node mover head tail))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)) :
    strategyHistoryPolicy root σ ⟨.Node mover head tail, history⟩
        hnonterminal =
      σ mover head tail := by
  rw [strategyHistoryPolicy,
    ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
      (toObservedGame root) _ _ _ _ mover rfl]
  simp only [ExtensiveGame.ObservedGame.PureProfile.actionAt,
    ExtensiveGame.ObservedGame.PureStrategy.actionAt,
    toObservedGame, nodeActionEquiv, nodeInfoAt]
  rfl

/-- At a concrete node history, translating a player profile prescribes the
same action as `GameTree.profileStrategy`. -/
theorem playerProfileHistoryPolicy_node (root : GameTree N U)
    (σ : N → PlayerStrategy N U) (mover : N)
    (head : GameTree N U) (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root (.Node mover head tail))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)) :
    playerProfileHistoryPolicy root σ ⟨.Node mover head tail, history⟩
        hnonterminal =
      profileStrategy σ mover head tail := by
  rw [playerProfileHistoryPolicy,
    ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
      (toObservedGame root) _ _ _ _ mover rfl]
  simp only [ExtensiveGame.ObservedGame.PureProfile.actionAt,
    ExtensiveGame.ObservedGame.PureStrategy.actionAt,
    playerProfileToObservedProfile, profileStrategy, toObservedGame,
    nodeActionEquiv, nodeInfoAt]
  rfl

/-! ### Result correspondence -/

/-- Any terminal-aware history policy that agrees with a `GameTree.Strategy`
at node histories reaches a leaf carrying `GameTree.outcome`, provided the
fuel is at least the current subtree's structural size. -/
theorem stoppedHistoryFrom_policy_reaches_outcome
    (root : GameTree N U) (σ : Strategy N U)
    (policy : (toExtensiveGame root).toArena.HistoryPolicy root)
    (hpolicy :
      ∀ (mover : N) (head : GameTree N U)
        (tail : List (GameTree N U))
        (history :
          (toExtensiveGame root).toArena.History root
            (.Node mover head tail))
        (hnonterminal :
          ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)),
        policy ⟨.Node mover head tail, history⟩ hnonterminal =
          σ mover head tail)
    (g : GameTree N U)
    (history : (toExtensiveGame root).toArena.History root g)
    (fuel : ℕ) (hsize : g.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toExtensiveGame root).toArena.stoppedHistoryFrom
        policy ⟨g, history⟩ fuel).1 = .Leaf payoff ∧
      payoff = outcome σ g := by
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ (subhistory :
        (toExtensiveGame root).toArena.History root subtree)
      (subfuel : ℕ), subtree.size ≤ subfuel →
      ∃ payoff : N → U,
        ((toExtensiveGame root).toArena.stoppedHistoryFrom
          policy ⟨subtree, subhistory⟩ subfuel).1 = .Leaf payoff ∧
        payoff = outcome σ subtree
  apply GameTree.strong_induction (motive := motive)
  · intro payoff subhistory subfuel hsubsize
    refine ⟨payoff, ?_, by simp⟩
    rw [Arena.stoppedHistoryFrom_eq_self_of_terminal
      policy ⟨.Leaf payoff, subhistory⟩
      (toExtensiveGame_isTerminal_leaf root payoff) subfuel]
  · intro mover head tail ih subhistory subfuel hsubsize
    cases subfuel with
    | zero =>
        have hpositive := size_pos (.Node mover head tail)
        omega
    | succ subfuel =>
        have hnonterminal :=
          toExtensiveGame_not_isTerminal_node root mover head tail
        rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
          policy ⟨.Node mover head tail, subhistory⟩
          subfuel hnonterminal]
        rw [hpolicy mover head tail subhistory hnonterminal]
        have hchildSize :
            (σ mover head tail).1.size ≤ subfuel := by
          have hlt := size_mem_children_lt mover head tail
            (by simpa [children] using (σ mover head tail).2)
          omega
        rcases ih (σ mover head tail).1
            (by simpa [children] using (σ mover head tail).2)
            (subhistory.snoc (σ mover head tail)) subfuel hchildSize with
          ⟨payoff, hendpoint, hpayoff⟩
        refine ⟨payoff, hendpoint, ?_⟩
        simpa using hpayoff
  · exact hsize

/-- Stopped execution of a translated global strategy reaches the same leaf
payoff as `GameTree.outcome`. -/
theorem stoppedHistory_strategy_reaches_outcome
    (root : GameTree N U) (σ : Strategy N U) :
    ∃ payoff : N → U,
      ((toExtensiveGame root).toArena.stoppedHistory
        (strategyHistoryPolicy root σ) root.size).1 = .Leaf payoff ∧
      payoff = outcome σ root := by
  simpa [Arena.stoppedHistory] using
    stoppedHistoryFrom_policy_reaches_outcome root σ
      (strategyHistoryPolicy root σ)
      (strategyHistoryPolicy_node root σ)
      root (Arena.History.nil) root.size (Nat.le_refl _)

/-- The stopped payoff of a translated global strategy is exactly the old
`GameTree.outcome`. -/
theorem stoppedPayoff_strategy_eq_outcome
    (root : GameTree N U) (σ : Strategy N U) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        (strategyToObservedProfile root σ)
        (toExtensiveGame_noChanceOnHistories root) root.size =
      some (outcome σ root) := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistory_strategy_reaches_outcome root σ
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toExtensiveGame root).toArena.stoppedHistory
          (strategyHistoryPolicy root σ) root.size).1 := by
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).stoppedPayoff
        (strategyHistoryPolicy root σ) root.size =
      some (outcome σ root)
  rw [ExtensiveGame.stoppedPayoff_eq_some_of_terminal
    (toExtensiveGame root) (strategyHistoryPolicy root σ)
    root.size hterminal]
  apply congrArg some
  calc
    (toExtensiveGame root).payoff
        ((toExtensiveGame root).toArena.stoppedHistory
          (strategyHistoryPolicy root σ) root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = outcome σ root := hpayoff

/-- Stopped execution of a translated strategic-form player profile agrees
with the outcome of `GameTree.profileStrategy`. -/
theorem stoppedPayoff_playerProfile_eq_outcome
    (root : GameTree N U) (σ : N → PlayerStrategy N U) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        (playerProfileToObservedProfile root σ)
        (toExtensiveGame_noChanceOnHistories root) root.size =
      some (outcome (profileStrategy σ) root) := by
  have hreaches :
      ∃ payoff : N → U,
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 =
            .Leaf payoff ∧
        payoff = outcome (profileStrategy σ) root := by
    simpa [Arena.stoppedHistory] using
      stoppedHistoryFrom_policy_reaches_outcome root (profileStrategy σ)
        (playerProfileHistoryPolicy root σ)
        (playerProfileHistoryPolicy_node root σ)
        root (Arena.History.nil) root.size (Nat.le_refl _)
  obtain ⟨payoff, hendpoint, hpayoff⟩ := hreaches
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 := by
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).stoppedPayoff
        (playerProfileHistoryPolicy root σ) root.size =
      some (outcome (profileStrategy σ) root)
  rw [ExtensiveGame.stoppedPayoff_eq_some_of_terminal
    (toExtensiveGame root) (playerProfileHistoryPolicy root σ)
    root.size hterminal]
  apply congrArg some
  calc
    (toExtensiveGame root).payoff
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = outcome (profileStrategy σ) root := hpayoff

/-! ### Structural and observed game forms -/

/-- The existing `GameTree` strategic semantics as a deterministic
strategy/outcome game form. -/
def toGameForm (root : GameTree N U) : GameForm N where
  Strategy := fun _ => PlayerStrategy N U
  Outcome := N → U
  outcome σ := outcome (profileStrategy σ) root

/-- The concrete child selected by an observed profile at a represented node
history.  The complete history is supplied as runtime data, so no decision of
whether the endpoint information is represented is needed. -/
def observedActionAtNode (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node mover head tail)) :
    (toExtensiveGame root).Action (.Node mover head tail) :=
  profile.actionAt (toObservedGame root)
    ⟨.Node mover head tail, history⟩ mover rfl
    ⟨⟨head, List.mem_cons_self⟩⟩

/-- Evaluate an endpoint-observed profile from a supplied concrete history.

Execution follows the selected child structurally.  In particular, this does
not extend the profile to information coordinates that do not occur below the
compiled root. -/
def observedOutcomeFrom (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile) :
    (current : (toExtensiveGame root).toArena.HistoryFrom root) → N → U
  | ⟨.Leaf payoff, _⟩ => payoff
  | ⟨.Node mover head tail, history⟩ =>
      let action :=
        observedActionAtNode root profile mover head tail history
      observedOutcomeFrom root profile
        ⟨action.1, history.snoc action⟩
termination_by current => current.1.size
decreasing_by
  exact size_mem_children_lt mover head tail action.2

@[simp]
theorem observedOutcomeFrom_leaf
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (payoff : N → U)
    (history :
      (toExtensiveGame root).toArena.History root (.Leaf payoff)) :
    observedOutcomeFrom root profile ⟨.Leaf payoff, history⟩ = payoff := by
  rw [observedOutcomeFrom]

/-- If a supplied history endpoint is propositionally a leaf, direct observed
evaluation returns that leaf payoff.  This form is convenient when the
endpoint is carried by a dependent history package. -/
theorem observedOutcomeFrom_eq_of_endpoint_leaf
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current : (toExtensiveGame root).toArena.HistoryFrom root)
    (payoff : N → U) (hendpoint : current.1 = .Leaf payoff) :
    observedOutcomeFrom root profile current = payoff := by
  rcases current with ⟨state, history⟩
  simp only at hendpoint
  subst state
  exact observedOutcomeFrom_leaf root profile payoff history

@[simp]
theorem observedOutcomeFrom_node
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node mover head tail)) :
    observedOutcomeFrom root profile
        ⟨.Node mover head tail, history⟩ =
      observedOutcomeFrom root profile
        ⟨(observedActionAtNode root profile mover head tail history).1,
          history.snoc
            (observedActionAtNode root profile mover head tail history)⟩ :=
  by rw [observedOutcomeFrom]

/-! ### Termination-certified continuation semantics -/

/-- From any accumulated compiled history, an arbitrary observed pure profile
reaches the leaf computed by `observedOutcomeFrom` whenever the fuel dominates
the current subtree size. -/
theorem stoppedHistoryFrom_observedProfile_reaches_outcome
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) (hsize : current.1.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toObservedGame root).stoppedHistoryFrom profile
        (toExtensiveGame_noChanceOnHistories root) current fuel).1 =
          GameTree.Leaf payoff ∧
      payoff = observedOutcomeFrom root profile current := by
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ (history :
        (toExtensiveGame root).toArena.History root subtree)
      (remaining : ℕ), subtree.size ≤ remaining →
      ∃ payoff : N → U,
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChanceOnHistories root)
          ⟨subtree, history⟩ remaining).1 = .Leaf payoff ∧
        payoff = observedOutcomeFrom root profile ⟨subtree, history⟩
  apply GameTree.strong_induction (motive := motive)
  · intro payoff history remaining _hremaining
    refine ⟨payoff, ?_, (observedOutcomeFrom_leaf root profile payoff history).symm⟩
    change
      ((toExtensiveGame root).toArena.stoppedHistoryFrom
        (profile.toHistoryPolicy (toObservedGame root)
          (toExtensiveGame_noChanceOnHistories root))
        ⟨.Leaf payoff, history⟩ remaining).1 = .Leaf payoff
    rw [Arena.stoppedHistoryFrom_eq_self_of_terminal _ _
      (toExtensiveGame_isTerminal_leaf root payoff) remaining]
  · intro mover head tail ih history remaining hremaining
    cases remaining with
    | zero =>
        have hpositive := size_pos (.Node mover head tail)
        omega
    | succ remaining =>
        have hnonterminal :=
          toExtensiveGame_not_isTerminal_node root mover head tail
        let action :=
          observedActionAtNode root profile mover head tail history
        have hpolicyAction :
            profile.toHistoryPolicy (toObservedGame root)
                (toExtensiveGame_noChanceOnHistories root)
                ⟨.Node mover head tail, history⟩ hnonterminal =
              action := by
          rw [ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
            (toObservedGame root) profile
            (toExtensiveGame_noChanceOnHistories root)
            ⟨.Node mover head tail, history⟩ hnonterminal mover rfl]
          rfl
        have hchildSize : action.1.size ≤ remaining := by
          have hlt :=
            size_mem_children_lt mover head tail action.2
          omega
        obtain ⟨payoff, hendpoint, hpayoff⟩ :=
          ih action.1 action.2 (history.snoc action)
            remaining hchildSize
        refine ⟨payoff, ?_, ?_⟩
        · change
            ((toExtensiveGame root).toArena.stoppedHistoryFrom
              (profile.toHistoryPolicy (toObservedGame root)
                (toExtensiveGame_noChanceOnHistories root))
              ⟨.Node mover head tail, history⟩ (Nat.succ remaining)).1 =
                .Leaf payoff
          rw [Arena.stoppedHistoryFrom_succ_of_not_terminal _ _ _
            hnonterminal]
          simpa only [hpolicyAction, toExtensiveGame, treeArena, arenaNext]
            using hendpoint
        · rw [observedOutcomeFrom_node]
          exact hpayoff
  · exact hsize

/-- The finite compiled `GameTree` terminates under every pure profile from
every admissible history root. -/
def toObservedGame_pureTerminationPlanOnAllContinuations
    (root : GameTree N U) :
    ∀ current,
      (ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
        (toObservedGame root).base).IsRoot current →
      (toObservedGame root).PureTerminationPlanAt
        (toExtensiveGame_noChanceOnHistories root) current := by
  intro current _hroot
  refine
    { fuel := fun _profile => root.size
      terminal := ?_ }
  intro profile
  obtain ⟨payoff, hendpoint, _⟩ :=
    stoppedHistoryFrom_observedProfile_reaches_outcome
      root profile current root.size
        (arenaHistory_subtree current.2).size_le
  change
    (toExtensiveGame root).isTerminal
      ((toObservedGame root).stoppedHistoryFrom profile
        (toExtensiveGame_noChanceOnHistories root) current root.size).1
  rw [hendpoint]
  exact toExtensiveGame_isTerminal_leaf root payoff

/-- The total termination-certified payoff from an arbitrary compiled history
is the directly executable observed outcome from that history. -/
theorem terminalPayoffFrom_observedProfile_eq_outcome
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ)
    (hselectedTerminal :
      (toObservedGame root).PureTerminatesAtFuel profile
        (toExtensiveGame_noChanceOnHistories root) current fuel) :
    (toObservedGame root).terminalPayoffFrom profile
        (toExtensiveGame_noChanceOnHistories root) current fuel
          hselectedTerminal =
      observedOutcomeFrom root profile current := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistoryFrom_observedProfile_reaches_outcome
      root profile current root.size
        (arenaHistory_subtree current.2).size_le
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChanceOnHistories root) current root.size).1 := by
    change
      (toExtensiveGame root).isTerminal
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChanceOnHistories root) current root.size).1
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).payoff
        ((toObservedGame root).toControlledObservedGame.terminalHistoryFrom
          profile (toExtensiveGame_noChanceOnHistories root) current
          fuel).1 =
      observedOutcomeFrom root profile current
  rw [
    (toObservedGame root).toControlledObservedGame
      |>.terminalHistoryFrom_eq_of_terminal
        profile (toExtensiveGame_noChanceOnHistories root) current
        fuel hselectedTerminal root.size hterminal]
  calc
    (toExtensiveGame root).payoff
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChanceOnHistories root) current root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = observedOutcomeFrom root profile current := hpayoff

/-- The observed compilation's deterministic game form.

Its total outcome evaluator is justified operationally by
`stoppedPayoff_observedProfile_eq_gameFormOutcome` below. -/
def observedToGameForm (root : GameTree N U) : GameForm N where
  Strategy := (toObservedGame root).PureStrategy
  Outcome := N → U
  outcome σ := observedOutcomeFrom root σ
    ⟨root, Arena.History.nil⟩

/-- The observed game-form evaluator is exactly the payoff produced by
terminal-aware stopped execution. -/
theorem stoppedPayoff_observedProfile_eq_gameFormOutcome
    (root : GameTree N U)
    (σ : (toObservedGame root).PureProfile) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        σ (toExtensiveGame_noChanceOnHistories root) root.size =
      some ((observedToGameForm root).outcome σ) := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistoryFrom_observedProfile_reaches_outcome
      root σ ⟨root, Arena.History.nil⟩ root.size (Nat.le_refl _)
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toObservedGame root).stoppedHistoryFrom σ
          (toExtensiveGame_noChanceOnHistories root)
          ⟨root, Arena.History.nil⟩ root.size).1 := by
    exact hendpoint.symm ▸ toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).stoppedPayoff
        (σ.toHistoryPolicy (toObservedGame root)
          (toExtensiveGame_noChanceOnHistories root)) root.size =
      some (observedOutcomeFrom root σ
        ⟨root, Arena.History.nil⟩)
  rw [ExtensiveGame.stoppedPayoff_eq_some_of_terminal _ _ _ hterminal]
  apply congrArg some
  calc
    (toExtensiveGame root).payoff
        ((toObservedGame root).stoppedHistoryFrom σ
          (toExtensiveGame_noChanceOnHistories root)
          ⟨root, Arena.History.nil⟩ root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = observedOutcomeFrom root σ
          ⟨root, Arena.History.nil⟩ := hpayoff

/-- The `GameTree` game-form Nash predicate is definitionally the existing
strategic-form Nash predicate. -/
theorem toGameForm_isNash_iff_toStrategicGame
    [DecidableEq N] [Preorder U]
    (root : GameTree N U) (σ : (toGameForm root).Profile) :
    (toGameForm root).IsNash
        (fun payoff : N → U => payoff) σ ↔
      _root_.IsNashEquilibrium (GameTree.toStrategicGame root) σ :=
  Iff.rfl

end GameTree
