/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Logical determinacy interfaces

Determinacy is a solution concept, not a property of a winning-set family by
definition. This module therefore keeps `IsTotal`, `IsTwoPlayerZeroSum`, and
`IsTwoPlayerDetermined` separate. For arbitrary player types, the weaker
descriptive predicate is named `HasSomePathwiseWinningStrategy`; calling it
determinacy would blur the standard two-player logical-game meaning.

`FiniteTwoPlayerHypotheses` records the structural assumptions for finite
backward determinacy without baking them into `ObservedGame` or
`WinningCondition`. `WellFoundedTwoPlayerHypotheses` isolates the structural
assumptions; the recursive theorem additionally requires `BackwardInductionData`
with complete finite action lists, terminality decisions, certified terminal
winners, and represented-coordinate representatives. The theorem constructs
an information-consistent strategy; it does not replace observed strategies
by history-indexed policies.

The payoff-free carrier owns the logical predicates. This module proves both
the exclusivity boundary (two robust winners cannot coexist) and genuine
finite and well-founded perfect-information determinacy with that explicit
data by backward recursion. The finite result constructs the data and
specializes the recursive theorem. Open/closed
Gale--Stewart and Borel determinacy remain separate theorem tracks; existence
is never inferred from totality alone.

The finite precedent is [Zermelo 1913]; [Gale--Stewart 1953] marks the
distinct infinite-game source boundary. The implemented well-founded theorem
uses `WellFounded.fix` and finite action search. The finite specialization
supplies the data using classical choice. General well-founded determinacy
with arbitrary branching remains unimplemented; no descriptive-set theory or
external determinacy axiom is used here.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*} {G : ControlledObservedGame N}

/-- Pathwise winning strategies for one player in a payoff-free observed
game, bundled with their robust winning proof. -/
abbrev PathwiseWinningStrategies
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition)
    (i : N) :=
  {strategy : G.PureStrategy i //
    G.HasPathwiseWinningStrategy W i strategy}

/-- Some player has a robust pure pathwise winning strategy. -/
def HasSomePathwiseWinningStrategy
    (G : ControlledObservedGame N)
    (W : G.base.WinningCondition) : Prop :=
  ∃ (i : N) (strategy : G.PureStrategy i),
    G.HasPathwiseWinningStrategy W i strategy

/-- Constructive two-player determinacy on the payoff-free carrier. -/
def IsTwoPlayerDetermined
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Prop :=
  (∃ strategy : G.PureStrategy 0,
      G.HasPathwiseWinningStrategy W 0 strategy) ∨
    (∃ strategy : G.PureStrategy 1,
      G.HasPathwiseWinningStrategy W 1 strategy)

/-- For two players, existence of some pathwise winner is the explicit
determinacy disjunction. -/
theorem hasSomePathwiseWinningStrategy_iff_isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition} :
    G.HasSomePathwiseWinningStrategy W ↔
      G.IsTwoPlayerDetermined W := by
  constructor
  · rintro ⟨i, strategy, hwinning⟩
    fin_cases i
    · exact Or.inl ⟨strategy, hwinning⟩
    · exact Or.inr ⟨strategy, hwinning⟩
  · rintro (hzero | hone)
    · rcases hzero with ⟨strategy, hwinning⟩
      exact ⟨0, strategy, hwinning⟩
    · rcases hone with ⟨strategy, hwinning⟩
      exact ⟨1, strategy, hwinning⟩

/-- Structural assumptions for finite perfect-information payoff-free
determinacy. -/
structure FiniteTwoPlayerHypotheses
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- The reachable complete-history unfolding is uniformly finite. -/
  finiteEFG : G.FiniteEFGHypotheses
  /-- Every nonterminal history is player controlled. -/
  noChance : G.base.NoChanceOnHistories
  /-- Decision information determines the complete history. -/
  perfectInformation : G.PerfectInformation
  /-- Exactly one player wins each complete play. -/
  zeroSum : W.IsTwoPlayerZeroSum

/-! ### Well-founded perfect-information backward induction -/

/-- Minimal structural package consumed by well-founded backward induction.

Unlike `FiniteTwoPlayerHypotheses`, this package does not require a uniform
history-length bound or finite action/information carriers. Strategies are
indexed by represented decisions, so no separate raw-information availability
or terminal-mover normalization field is needed. The determinacy theorem also
requires `BackwardInductionData`, whose complete finite action lists exclude
infinite branching even though this structural package permits it. -/
structure WellFoundedTwoPlayerHypotheses
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- The legal complete-history child relation is well founded. -/
  wellFounded :
    G.base.toArena.IsWellFoundedFrom G.base.init
  /-- Every nonterminal history is player controlled. -/
  noChance : G.base.NoChanceOnHistories
  /-- Decision information determines the complete history. -/
  perfectInformation : G.PerfectInformation
  /-- Exactly one player wins each complete play. -/
  zeroSum : W.IsTwoPlayerZeroSum

/-- The canonical root play obtained by replaying one terminal complete
history and then stuttering forever. -/
def terminalReplay
    (G : ControlledObservedGame (Fin 2))
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    G.base.CompletePlay :=
  Arena.CompletePlayFromHistory.prependHistory history.2
    (Arena.CompletePlayFromHistory.stutter history hterminal)

/-- Explicit runtime data used by executable well-founded backward induction.

The action lists are ordered, complete enumerations.  Terminal objectives may
be arbitrary predicates, so their winner and a representative of each
represented information coordinate are supplied together with correctness
proofs instead of being extracted from propositional existence. -/
structure BackwardInductionData
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- Executable terminality test on reachable endpoints. -/
  terminalDecidable :
    (state : G.base.State) → Decidable (G.base.isTerminal state)
  /-- Winner assigned to a certified terminal history. -/
  terminalWinner :
    (history : G.base.History) →
      G.base.isTerminal history.1 → Fin 2
  /-- The assigned terminal winner satisfies the path objective. -/
  terminalWinner_mem :
    ∀ (history : G.base.History)
      (hterminal : G.base.isTerminal history.1),
      terminalReplay G history hterminal ∈
        W (terminalWinner history hterminal)
  /-- Stable traversal order for every concrete action fiber. -/
  actions :
    (history : G.base.History) → List (G.base.Action history.1)
  /-- The action traversal contains every legal action. -/
  actions_complete :
    ∀ (history : G.base.History) (action : G.base.Action history.1),
      action ∈ actions history
  /-- Concrete occurrence used for each represented information coordinate. -/
  representative :
    ∀ (i : Fin 2) (information : G.RepresentedInfo i),
      G.DecisionInfoWitness i information.1

/-- A finite perfect-information package specializes to the strictly weaker
well-founded backward-induction package. -/
def FiniteTwoPlayerHypotheses.toWellFounded
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.WellFoundedTwoPlayerHypotheses W where
  wellFounded := h.finiteEFG.isWellFoundedFrom
  noChance := h.noChance
  perfectInformation := h.perfectInformation
  zeroSum := h.zeroSum

/-! ### Finite perfect-information backward induction -/

/-- The other member of `Fin 2`. -/
def otherPlayer (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

@[simp]
theorem otherPlayer_zero : otherPlayer 0 = 1 := by
  simp [otherPlayer]

@[simp]
theorem otherPlayer_one : otherPlayer 1 = 0 := by
  simp [otherPlayer]

theorem otherPlayer_ne (i : Fin 2) :
    otherPlayer i ≠ i := by
  fin_cases i <;> simp

theorem eq_otherPlayer_of_ne {i j : Fin 2}
    (hne : j ≠ i) :
    j = otherPlayer i := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- Read the explicitly supplied winner of a canonical terminal replay. -/
def terminalWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    Fin 2 :=
  data.terminalWinner history hterminal

/-- The terminal winner really wins the canonical replay used to define it.
-/
theorem terminalReplay_mem_terminalWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    terminalReplay G history hterminal ∈
      W (terminalWinner data history hterminal) :=
  data.terminalWinner_mem history hterminal

/-- Backward-induction winner of every complete history.

At a decision history, the mover wins exactly when some child is winning for
that mover; otherwise the other player wins. At terminal histories the winner
is read from the arbitrary path objective on the canonical terminal replay.
-/
def backwardWinner
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W) :
    G.base.History → Fin 2 :=
  @WellFounded.fix G.base.History (fun _ => Fin 2)
    (G.base.toArena.IsChildFrom
      (start := G.base.init))
    h.wellFounded.wellFounded_isChildFrom
    (fun history recurse =>
      letI := data.terminalDecidable history.1
      if hterminal : G.base.isTerminal history.1 then
        terminalWinner data history hterminal
      else
        let mover := G.playerAt h.noChance history hterminal
        if ∃ action ∈ data.actions history,
            recurse
                ⟨G.base.next history.1 action,
                  history.2.snoc action⟩
                (Arena.IsChildFrom.snoc history action) =
              mover then
          mover
        else
          otherPlayer mover)

/-! ### Correctness of the executable winner and action selection -/

/-- Unfold one step of the backward-winner recursion. -/
theorem backwardWinner_eq
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History) :
    backwardWinner h data history =
      (by
        letI := data.terminalDecidable history.1
        exact
          if hterminal : G.base.isTerminal history.1 then
            terminalWinner data history hterminal
          else
            let mover := G.playerAt h.noChance history hterminal
            if ∃ action ∈ data.actions history,
                backwardWinner h data
                    ⟨G.base.next history.1 action,
                      history.2.snoc action⟩ = mover then
              mover
            else
              otherPlayer mover) := by
  unfold backwardWinner
  rw [WellFounded.fix_eq]

/-- At a terminal history, backward induction agrees with the supplied
terminal winner. -/
theorem backwardWinner_eq_of_terminal
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hterminal : G.base.isTerminal history.1) :
    backwardWinner h data history =
      terminalWinner data history hterminal := by
  rw [backwardWinner_eq h data]
  simp [hterminal]

/-- When the current mover is the backward winner, some listed legal action
keeps the same backward winner at the child. -/
theorem exists_action_backwardWinner_eq
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h data history))
    (hdecision : G.base.toArena.IsDecision history.1) :
    ∃ action : G.base.Action history.1,
      backwardWinner h data
          ⟨G.base.next history.1 action,
            history.2.snoc action⟩ =
        backwardWinner h data history := by
  have hnonterminal : ¬ G.base.isTerminal history.1 := by
    intro hterminal
    exact (not_nonempty_iff.mpr hterminal) hdecision
  let mover := G.playerAt h.noChance history hnonterminal
  have hmoverChosen : G.base.mover history.1 = some mover :=
    G.mover_playerAt h.noChance history hnonterminal
  have hmover_eq : mover = backwardWinner h data history :=
    Option.some.inj (hmoverChosen.symm.trans hmover)
  have hexists :
      ∃ action ∈ data.actions history,
        backwardWinner h data
            ⟨G.base.next history.1 action,
              history.2.snoc action⟩ = mover := by
    by_contra hnone
    have hwinner := backwardWinner_eq h data history
    simp [hnonterminal, mover, hnone] at hwinner
    exact (otherPlayer_ne mover) ((hmover_eq.trans hwinner).symm)
  rcases hexists with ⟨action, _hlisted, haction⟩
  exact ⟨action, haction.trans hmover_eq⟩

/-- At a node controlled by the player other than its backward winner, every
legal action keeps the same backward winner. -/
theorem backwardWinner_child_eq_of_ne
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (i : Fin 2)
    (hmover : G.base.mover history.1 = some i)
    (hne : i ≠ backwardWinner h data history)
    (action : G.base.Action history.1) :
    backwardWinner h data
        ⟨G.base.next history.1 action,
          history.2.snoc action⟩ =
      backwardWinner h data history := by
  have hnonterminal : ¬ G.base.isTerminal history.1 :=
    fun hterminal => hterminal.false action
  let mover := G.playerAt h.noChance history hnonterminal
  have hmoverChosen : G.base.mover history.1 = some mover :=
    G.mover_playerAt h.noChance history hnonterminal
  have hmover_eq : mover = i :=
    Option.some.inj (hmoverChosen.symm.trans hmover)
  by_cases hexists :
      ∃ nextAction ∈ data.actions history,
        backwardWinner h data
            ⟨G.base.next history.1 nextAction,
              history.2.snoc nextAction⟩ = mover
  · have hwinner := backwardWinner_eq h data history
    simp [hnonterminal, mover, hexists] at hwinner
    exact (hne (hmover_eq.symm.trans hwinner.symm)).elim
  · have hchild_ne :
        backwardWinner h data
            ⟨G.base.next history.1 action,
              history.2.snoc action⟩ ≠ mover := by
      intro heq
      exact hexists
        ⟨action, data.actions_complete history action, heq⟩
    have hchild_other := eq_otherPlayer_of_ne hchild_ne
    have hwinner := backwardWinner_eq h data history
    simp [hnonterminal, mover, hexists] at hwinner
    exact hchild_other.trans hwinner.symm

/-- The first winner-preserving action in the supplied traversal order. -/
def backwardAction
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h data history))
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.base.Action history.1 :=
  let candidates :=
    (data.actions history).filter fun action =>
      backwardWinner h data
          ⟨G.base.next history.1 action,
            history.2.snoc action⟩ =
        backwardWinner h data history
  candidates.head (by
    obtain ⟨action, haction⟩ :=
      exists_action_backwardWinner_eq h data history hmover hdecision
    exact List.ne_nil_of_mem
      (List.mem_filter.mpr
        ⟨data.actions_complete history action,
          decide_eq_true haction⟩))

/-- The selected backward action preserves the winner. -/
theorem backwardWinner_backwardAction
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some (backwardWinner h data history))
    (hdecision : G.base.toArena.IsDecision history.1) :
    backwardWinner h data
        ⟨G.base.next history.1
            (backwardAction h data history hmover hdecision),
          history.2.snoc
            (backwardAction h data history hmover hdecision)⟩ =
      backwardWinner h data history := by
  have hmem := List.head_mem
    (l := (data.actions history).filter fun action =>
      backwardWinner h data
          ⟨G.base.next history.1 action,
            history.2.snoc action⟩ =
        backwardWinner h data history)
    (by
      obtain ⟨action, haction⟩ :=
        exists_action_backwardWinner_eq h data history hmover hdecision
      exact List.ne_nil_of_mem
        (List.mem_filter.mpr
          ⟨data.actions_complete history action,
            decide_eq_true haction⟩))
  exact of_decide_eq_true (List.mem_filter.mp hmem).2

/-- Transporting an abstract action from an equal representative history and
then realizing it returns the representative's concrete action, up to the
dependent action-fiber equality induced by the history equality. -/
theorem actionEquiv_transport_symm_heq
    {G : ControlledObservedGame (Fin 2)}
    {i : Fin 2}
    (first second : G.base.History)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_nonterminal : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_nonterminal : G.base.toArena.IsDecision second.1)
    (hhistory : first = second)
    (hinfo :
      G.infoAt second i hsecond hsecond_nonterminal =
        G.infoAt first i hfirst hfirst_nonterminal)
    (action : G.base.Action second.1) :
    HEq
      (G.actionEquiv first i hfirst hfirst_nonterminal
        (hinfo ▸
          (G.actionEquiv second i hsecond
            hsecond_nonterminal).symm action))
      action := by
  subst second
  simp

/-- Equal complete histories and heterogeneously equal concrete actions
produce equal one-step child histories. -/
theorem childHistory_eq_of_heq
    {G : ControlledObservedGame (Fin 2)}
    (first second : G.base.History)
    (hhistory : first = second)
    (firstAction : G.base.Action first.1)
    (secondAction : G.base.Action second.1)
    (haction : HEq firstAction secondAction) :
    (⟨G.base.next first.1 firstAction,
        first.2.snoc firstAction⟩ :
        G.base.History) =
      ⟨G.base.next second.1 secondAction,
        second.2.snoc secondAction⟩ := by
  subst second
  have heq : firstAction = secondAction :=
    eq_of_heq haction
  subst secondAction
  rfl

/-- The first legal action in the supplied traversal order at a decision. -/
private def firstBackwardAction
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.base.Action history.1 :=
  (data.actions history).head (by
    obtain ⟨action⟩ := hdecision
    exact List.ne_nil_of_mem (data.actions_complete history action))

/-- Read the supplied concrete representative of a represented information
state. -/
def backwardRepresentative
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (data : G.BackwardInductionData W)
    (i : Fin 2) (information : G.RepresentedInfo i) :
    G.DecisionInfoWitness i information.1 :=
  data.representative i information

/-- The information-consistent pure strategy extracted by backward induction.

At information states in the winning region it transports the selected
concrete backward action through `actionEquiv`. Off the winning region its
value is arbitrary; those coordinates cannot be reached while the invariant
that the root winner is preserved holds. -/
def backwardStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W) :
    G.PureStrategy
      (backwardWinner h data
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init)) :=
  by
    let rootWinner :=
      backwardWinner h data
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init)
    intro information
    let witness :=
      backwardRepresentative data rootWinner information
    if hinvariant :
        backwardWinner h data witness.history = rootWinner then
      change G.InfoAction rootWinner information.1
      exact
        witness.infoAt_eq ▸
          (G.actionEquiv witness.history rootWinner
              witness.mover witness.decision).symm
            (backwardAction h data witness.history
              (witness.mover.trans
                (congrArg some hinvariant.symm))
              witness.decision)
    else
      change G.InfoAction rootWinner information.1
      exact
        witness.infoAt_eq ▸
          (G.actionEquiv witness.history rootWinner
              witness.mover witness.decision).symm
            (firstBackwardAction data witness.history witness.decision)

/-- Along the root winner's extracted strategy, a decision by that player
keeps the backward winner invariant. Singleton information is the step that
turns the representative-indexed action into the action at the actual
history. -/
theorem backwardWinner_child_of_backwardStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (history : G.base.History)
    (hmover :
      G.base.mover history.1 =
        some
          (backwardWinner h data
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)))
    (hnonterminal : ¬ G.base.isTerminal history.1)
    (hinvariant :
      backwardWinner h data history =
        backwardWinner h data
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)) :
    backwardWinner h data
        ⟨G.base.next history.1
            ((backwardStrategy h data).actionAt
              G history hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal)),
          history.2.snoc
            ((backwardStrategy h data).actionAt
              G history hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal))⟩ =
      backwardWinner h data
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init) := by
  classical
  let rootWinner :=
    backwardWinner h data
      (Arena.HistoryFrom.nil
        G.base.toArena G.base.init)
  let hdecision :=
    G.base.toArena.isDecision_of_not_isTerminal
      history.1 hnonterminal
  let information :=
    G.representedInfoAt history rootWinner hmover hdecision
  let witness :=
    backwardRepresentative data rootWinner information
  have hhistory : history = witness.history := by
    apply h.perfectInformation rootWinner
      history witness.history hmover hdecision
      witness.mover witness.decision
    exact witness.infoAt_eq.symm
  have hwitness :
      backwardWinner h data witness.history = rootWinner := by
    rw [← hhistory]
    simpa [rootWinner] using hinvariant
  let witnessWinnerMover :
      G.base.mover witness.history.1 =
        some (backwardWinner h data witness.history) :=
    witness.mover.trans
      (congrArg some hwitness.symm)
  have hstrategyInformation :
      backwardStrategy h data information =
        (witness.infoAt_eq ▸
          (G.actionEquiv witness.history rootWinner
              witness.mover witness.decision).symm
            (backwardAction h data witness.history
              (witness.mover.trans
                (congrArg some hwitness.symm))
              witness.decision)) := by
    simp [backwardStrategy, rootWinner, information,
      witness, hwitness]
  have hinfo :
      G.infoAt witness.history rootWinner witness.mover
          witness.decision =
        G.infoAt history rootWinner hmover hdecision := by
    simpa [information] using witness.infoAt_eq
  have haction :
      HEq
        ((backwardStrategy h data).actionAt
          G history hmover hdecision)
        (backwardAction h data witness.history
          witnessWinnerMover witness.decision) := by
    change
      HEq
        (G.actionEquiv history rootWinner hmover hdecision
          (backwardStrategy h data information))
        (backwardAction h data witness.history
          witnessWinnerMover witness.decision)
    rw [hstrategyInformation]
    exact actionEquiv_transport_symm_heq
      history witness.history hmover hdecision
        witness.mover witness.decision
        hhistory hinfo
        (backwardAction h data witness.history
          witnessWinnerMover witness.decision)
  have hchild :
      (⟨G.base.next history.1
            ((backwardStrategy h data).actionAt
              G history hmover hdecision),
          history.2.snoc
            ((backwardStrategy h data).actionAt
              G history hmover hdecision)⟩ :
          G.base.History) =
        ⟨G.base.next witness.history.1
            (backwardAction h data witness.history
              witnessWinnerMover witness.decision),
          witness.history.2.snoc
            (backwardAction h data witness.history
              witnessWinnerMover witness.decision)⟩ :=
    childHistory_eq_of_heq
      history witness.history hhistory
      ((backwardStrategy h data).actionAt
        G history hmover hdecision)
      (backwardAction h data witness.history
        witnessWinnerMover witness.decision)
      haction
  rw [hchild]
  have hselected :=
    backwardWinner_backwardAction
      h data witness.history witnessWinnerMover witness.decision
  exact hselected.trans hwitness

/-- Every play compatible with the extracted strategy stays inside the root
winner's backward-winning region at every coordinate. -/
theorem backwardWinner_historyAt_eq_root
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W)
    (play : G.base.CompletePlay)
    (hcompatible :
      G.IsCompatibleWithPlayerStrategy
        (backwardWinner h data
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init))
        (backwardStrategy h data) play) :
    ∀ n,
      backwardWinner h data (play.historyAt n) =
        backwardWinner h data
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init)
  | 0 => by
      rw [play.historyAt_zero]
  | n + 1 => by
      have ih :=
        backwardWinner_historyAt_eq_root
          h data play hcompatible n
      by_cases hterminal :
          G.base.isTerminal (play.historyAt n).1
      · rw [play.at_succ_eq_of_terminal n hterminal]
        exact ih
      · rcases
          h.noChance (play.historyAt n) hterminal with
        ⟨i, hmover⟩
        by_cases hi :
            i =
              backwardWinner h data
                (Arena.HistoryFrom.nil
                  G.base.toArena G.base.init)
        · subst i
          rw [hcompatible n hterminal hmover]
          exact
            backwardWinner_child_of_backwardStrategy
              h data (play.historyAt n) hmover hterminal ih
        · have hne :
              i ≠ backwardWinner h data (play.historyAt n) := by
            intro heq
            exact hi (heq.trans ih)
          rcases
              play.isChild_at_succ_of_not_terminal
                n hterminal with
            ⟨action, hnext⟩
          rw [hnext]
          exact
            (backwardWinner_child_eq_of_ne
              h data (play.historyAt n) i hmover hne
                action).trans ih

/-- The backward-induction strategy is pathwise winning for the winner of the
root history. -/
theorem backwardStrategy_hasPathwiseWinningStrategy
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W) :
    G.HasPathwiseWinningStrategy W
      (backwardWinner h data
        (Arena.HistoryFrom.nil
          G.base.toArena G.base.init))
      (backwardStrategy h data) := by
  intro play hcompatible
  rcases h.wellFounded.eventuallyTerminates play with
    ⟨bound, hterminal⟩
  have hinvariant :
      backwardWinner h data (play.historyAt bound) =
        backwardWinner h data
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init) :=
    backwardWinner_historyAt_eq_root
      h data play hcompatible bound
  have hterminalWinner :
      terminalWinner data
          (play.historyAt bound) hterminal =
        backwardWinner h data
          (Arena.HistoryFrom.nil
            G.base.toArena G.base.init) :=
    (backwardWinner_eq_of_terminal
      h data (play.historyAt bound) hterminal).symm.trans
        hinvariant
  have hwins :=
    terminalReplay_mem_terminalWinner
      data (play.historyAt bound) hterminal
  have hreplay :
      terminalReplay G (play.historyAt bound) hterminal =
        play := by
    exact
      play.prependHistory_stutter_eq_of_terminal
        bound hterminal
  rw [hreplay, hterminalWinner] at hwins
  exact hwins

/-- Well-founded, no-chance, perfect-information, two-player zero-sum observed
games equipped with explicit terminal, action-order, and representative data
are determined by the executable information-consistent strategy above. -/
theorem WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedTwoPlayerHypotheses W)
    (data : G.BackwardInductionData W) :
    G.IsTwoPlayerDetermined W := by
  let rootWinner :=
    backwardWinner h data
      (Arena.HistoryFrom.nil
        G.base.toArena G.base.init)
  have hwinning :
      G.HasPathwiseWinningStrategy W rootWinner
        (backwardStrategy h data) :=
    backwardStrategy_hasPathwiseWinningStrategy h data
  have hpackage :
      ∃ strategy : G.PureStrategy rootWinner,
        G.HasPathwiseWinningStrategy W
          rootWinner strategy :=
    ⟨backwardStrategy h data, hwinning⟩
  by_cases hzero : rootWinner = 0
  · exact Or.inl (hzero ▸ hpackage)
  · have hone : rootWinner = 1 :=
      Fin.eq_one_of_ne_zero rootWinner hzero
    exact Or.inr (hone ▸ hpackage)

/-- The established finite determinacy theorem is a specialization of
well-founded backward determinacy. -/
theorem FiniteTwoPlayerHypotheses.isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.FiniteTwoPlayerHypotheses W) :
    G.IsTwoPlayerDetermined W := by
  classical
  let data : G.BackwardInductionData W :=
    { terminalDecidable := fun state => Classical.dec _
      terminalWinner := fun history hterminal =>
        Classical.choose
          (h.zeroSum.isTotal (terminalReplay G history hterminal))
      terminalWinner_mem := fun history hterminal =>
        Classical.choose_spec
          (h.zeroSum.isTotal (terminalReplay G history hterminal))
      actions := fun history => by
        letI := h.finiteEFG.finiteAction history
        exact Finset.univ.toList
      actions_complete := by
        intro history action
        letI := h.finiteEFG.finiteAction history
        simp
      representative := fun _ information =>
        Classical.choice information.2 }
  exact h.toWellFounded.isTwoPlayerDetermined data

/-- Structural assumptions for well-founded prefix determinacy on the
payoff-free carrier. -/
structure WellFoundedPrefixHypotheses
    (G : ControlledObservedGame (Fin 2))
    (W : G.base.WinningCondition) : Type _ where
  /-- Every legal history branch is structurally well founded. -/
  wellFounded :
    G.base.toArena.IsWellFoundedFrom G.base.init
  /-- Every nonterminal history is player controlled. -/
  noChance : G.base.NoChanceOnHistories
  /-- Decision information determines the complete history. -/
  perfectInformation : G.PerfectInformation
  /-- Exactly one player wins each complete play. -/
  zeroSum : W.IsTwoPlayerZeroSum
  /-- Every play reaches a persistent finite decision prefix. -/
  prefixDecision :
    Arena.WinningConditionFrom.PrefixDecision W

/-- Forget the prefix certificate and retain the hypotheses used by
well-founded backward induction. -/
def WellFoundedPrefixHypotheses.toWellFounded
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedPrefixHypotheses W) :
    G.WellFoundedTwoPlayerHypotheses W where
  wellFounded := h.wellFounded
  noChance := h.noChance
  perfectInformation := h.perfectInformation
  zeroSum := h.zeroSum

/-- Well-founded prefix games satisfying the no-chance, perfect-information,
and zero-sum hypotheses, and equipped with `BackwardInductionData` including
complete finite action lists, are determined.

The prefix-decision certificate is retained because it exposes the objective
as a clopen/prefix-decidable game for later topological comparison. The
backward proof uses the stronger structural fact that well-foundedness forces
every complete play to terminate. -/
theorem WellFoundedPrefixHypotheses.isTwoPlayerDetermined
    {G : ControlledObservedGame (Fin 2)}
    {W : G.base.WinningCondition}
    (h : G.WellFoundedPrefixHypotheses W)
    (data : G.BackwardInductionData W) :
    G.IsTwoPlayerDetermined W :=
  h.toWellFounded.isTwoPlayerDetermined data

/-- In a payoff-free no-chance game with exclusive objectives, the two
players cannot both have robust pathwise winning strategies. -/
theorem not_both_havePathwiseWinningStrategy
    {G : ControlledObservedGame (Fin 2)}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    {W : G.base.WinningCondition}
    (hNoChance : G.base.NoChanceOnHistories)
    (hexclusive : W.IsExclusive) :
    ¬ ((∃ strategy : G.PureStrategy 0,
          G.HasPathwiseWinningStrategy W 0 strategy) ∧
        (∃ strategy : G.PureStrategy 1,
          G.HasPathwiseWinningStrategy W 1 strategy)) := by
  rintro ⟨⟨strategyZero, hwinningZero⟩,
    ⟨strategyOne, hwinningOne⟩⟩
  let profile : G.PureProfile := fun i =>
    if hzero : i = 0 then
      hzero ▸ strategyZero
    else
      (Fin.eq_one_of_ne_zero i hzero) ▸ strategyOne
  have hprofileZero : profile 0 = strategyZero := by
    simp [profile]
  have hprofileOne : profile 1 = strategyOne := by
    simp [profile]
  let play : G.base.CompletePlay :=
    (profile.toHistoryPolicy hNoChance).completePlay
  have hcompatibleZero :
      G.IsCompatibleWithPlayerStrategy
        0 strategyZero play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy
        hNoChance 0
    simpa [play, hprofileZero] using hprofile
  have hcompatibleOne :
      G.IsCompatibleWithPlayerStrategy
        1 strategyOne play := by
    have hprofile :=
      profile.completePlay_isCompatibleWithPlayerStrategy
        hNoChance 1
    simpa [play, hprofileOne] using hprofile
  have hwinsZero : play ∈ W 0 :=
    hwinningZero play hcompatibleZero
  have hwinsOne : play ∈ W 1 :=
    hwinningOne play hcompatibleOne
  exact Fin.zero_ne_one
    (hexclusive play hwinsZero hwinsOne)

end ExtensiveGame.ControlledObservedGame
