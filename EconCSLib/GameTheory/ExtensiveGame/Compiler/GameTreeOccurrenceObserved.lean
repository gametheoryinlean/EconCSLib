/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination

/-!
# EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved

An occurrence-sensitive observed-EFG compiler for `GameTree`.

`GameTree.toObservedGame` deliberately reuses the historical
`GameTree.PlayerStrategy` interface: its observations and information states
depend only on the endpoint subtree or node context.  Equal subtree values
appearing at different occurrences are therefore identified.

This module provides a second, genuinely perfect-information representation.
Every private/public observation is the complete typed history occurrence, and
a decision information state is a complete history together with evidence
that the corresponding player moves there.  Consequently, equal information
states imply equal history occurrences, and the compiled EFG has perfect
information and perfect recall.

The occurrence-sensitive game refines the endpoint compiler rather than being
strictly isomorphic to it.  Explicit forgetting maps erase the occurrence and
retain the endpoint subtree/node context.  Conversely, every endpoint-indexed
pure strategy lifts canonically to an occurrence strategy, and the lifted
profile generates exactly the same concrete history policy and bounded
outcome.

## Main definitions

* `GameTree.OccurrenceInfo` — a player-controlled complete history occurrence.
* `GameTree.toOccurrenceObservedGame` — the occurrence-sensitive observed EFG.
* `GameTree.forgetOccurrenceObservation` and `forgetOccurrenceInfo` — the
  concrete information-forgetting maps.
* `GameTree.liftEndpointPureStrategy` and `liftEndpointPureProfile` — strategy
  lifting from the endpoint compiler to the finer occurrence compiler.
* `GameTree.endpointBehavioralInformationRefinement` — the same compiler
  relation with exact behavioral/chance semantics.

## Main results

* `toOccurrenceObservedGame_perfectInformation` and
  `toOccurrenceObservedGame_perfectRecall`.
* `forgetOccurrenceInfo_observe` and
  `forgetOccurrenceInfoActionEquiv_at`.
* `liftEndpointPureProfile_toHistoryPolicy`,
  `stoppedHistoryFrom_liftEndpointPureProfile`, and
  `stoppedPayoffFrom_liftEndpointPureProfile`.
* `occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect` and
  `Kuhn_exists_occurrencePureSPE` — canonical root-bound standard SPE against
  all occurrence-dependent unilateral deviations.
* `behavioralStoppedPayoffLawFrom_liftEndpoint` and
  `isEndpointBehavioralNashOnAllContinuationsAtFuel_of_occurrenceLift`.
-/

namespace GameTree

variable {N U : Type*}

/-- A complete history occurrence at which player `i` moves. -/
abbrev OccurrenceInfo (root : GameTree N U) (i : N) :=
  { history :
      (toExtensiveGame root).toArena.HistoryFrom root //
    (toExtensiveGame root).mover history.1 = some i ∧
      (toExtensiveGame root).toArena.IsDecision history.1 }

namespace OccurrenceInfo

/-- The legal action type at an occurrence information state. -/
abbrev Action {root : GameTree N U} {i : N}
    (information : OccurrenceInfo root i) :=
  (toExtensiveGame root).Action information.1.1

end OccurrenceInfo

/-- Compile a `GameTree` to an occurrence-sensitive perfect-information
observed EFG.

Only player-controlled histories inhabit `InfoState`, so pure and behavioral
strategies are never forced to choose an action at terminal histories. -/
def toOccurrenceObservedGame (root : GameTree N U) :
    ExtensiveGame.ObservedGame N U where
  base := toExtensiveGame root
  Observation := fun _ =>
    (toExtensiveGame root).toArena.HistoryFrom root
  PublicObservation :=
    (toExtensiveGame root).toArena.HistoryFrom root
  observe := fun _ history => history
  publicObserve := fun history => history
  publicOf := fun _ observation => observation
  observe_public := by
    intro i history
    rfl
  InfoState := fun i => OccurrenceInfo root i
  infoObserve := fun _ information => information.1
  infoAt := fun history _ hmover hnonterminal =>
    ⟨history, hmover, hnonterminal⟩
  infoAt_observe := by
    intro history i hmover hnonterminal
    rfl
  InfoAction := fun _ information => information.Action
  actionEquiv := fun _ _ _ _ => Equiv.refl _

instance toOccurrenceObservedGame.instTerminalDecidable
    (root : GameTree N U) :
    (state : (toOccurrenceObservedGame root).base.State) →
      Decidable
        ((toOccurrenceObservedGame root).base.isTerminal state) :=
  toExtensiveGame_terminalDecidable root

/-- Occurrence information is singleton information for every player. -/
theorem toOccurrenceObservedGame_hasSingletonInformation
    (root : GameTree N U) (i : N) :
    (toOccurrenceObservedGame root).HasSingletonInformation i := by
  intro first second hfirst hfirst_nonterminal hsecond
    hsecond_nonterminal hsame
  exact congrArg Subtype.val hsame

/-- The occurrence-sensitive compiler has perfect information. -/
theorem toOccurrenceObservedGame_perfectInformation
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).PerfectInformation :=
  fun i =>
    toOccurrenceObservedGame_hasSingletonInformation root i

/-- The occurrence-sensitive compiler has perfect recall. -/
theorem toOccurrenceObservedGame_perfectRecall
    [DecidableEq N]
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).PerfectRecall :=
  (toOccurrenceObservedGame_perfectInformation root).perfectRecall

/-! ### Termination under occurrence-dependent strategies -/

/-- Every terminal-aware history policy reaches a leaf once the supplied fuel
dominates the current subtree size.

Unlike the endpoint compiler's outcome theorem, this statement makes no
assumption that choices at equal endpoint subtrees agree. It therefore applies
to genuinely occurrence-dependent strategies. -/
theorem stoppedHistoryFrom_policy_reaches_leaf
    (root : GameTree N U)
    (policy :
      (toExtensiveGame root).toArena.HistoryPolicy root)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ)
    (hsize : current.1.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toExtensiveGame root).toArena.stoppedHistoryFrom
        policy current fuel).1 =
        .Leaf payoff := by
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ (history :
        (toExtensiveGame root).toArena.History
          root subtree)
      (remaining : ℕ),
      subtree.size ≤ remaining →
        ∃ payoff : N → U,
          ((toExtensiveGame root).toArena.stoppedHistoryFrom
            policy ⟨subtree, history⟩ remaining).1 =
            .Leaf payoff
  apply GameTree.strong_induction (motive := motive)
  · intro payoff history remaining hremaining
    refine ⟨payoff, ?_⟩
    rw [Arena.stoppedHistoryFrom_eq_self_of_terminal
      policy ⟨.Leaf payoff, history⟩
      (toExtensiveGame_isTerminal_leaf root payoff)
      remaining]
  · intro mover head tail ih history remaining hremaining
    cases remaining with
    | zero =>
        have hpositive :=
          size_pos (.Node mover head tail)
        omega
    | succ remaining =>
        have hnonterminal :=
          toExtensiveGame_not_isTerminal_node
            root mover head tail
        rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
          policy
          ⟨.Node mover head tail, history⟩
          remaining hnonterminal]
        let action :=
          policy
            ⟨.Node mover head tail, history⟩
            hnonterminal
        have hchildSize :
            action.1.size ≤ remaining := by
          have hlt :=
            size_mem_children_lt mover head tail
              (by
                simpa [children] using action.2)
          omega
        exact
          ih action.1
            (by simpa [children] using action.2)
            (history.snoc action)
            remaining hchildSize
  · exact hsize

/-- The occurrence-sensitive compiler terminates under every pure profile,
including profiles that condition on the complete path. -/
def toOccurrenceObservedGame_pureTerminationPlanOnAllContinuations
    (root : GameTree N U) :
    ∀ current,
      (ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
        (toOccurrenceObservedGame root).base).IsRoot current →
      (toOccurrenceObservedGame root).PureTerminationPlanAt
        (toExtensiveGame_noChanceOnHistories root) current := by
  intro current _hroot
  refine
    { fuel := fun _profile => root.size
      terminal := ?_ }
  intro profile
  obtain ⟨payoff, hendpoint⟩ :=
    stoppedHistoryFrom_policy_reaches_leaf
      root
      (ExtensiveGame.ControlledObservedGame.PureProfile.toHistoryPolicy
        (G := (toOccurrenceObservedGame root).toControlledObservedGame)
        profile (toExtensiveGame_noChanceOnHistories root))
      current root.size
      (arenaHistory_subtree current.2).size_le
  change
    (toExtensiveGame root).isTerminal
      ((toOccurrenceObservedGame root).stoppedHistoryFrom
        profile (toExtensiveGame_noChanceOnHistories root)
        current root.size).1
  rw [show
    ((toOccurrenceObservedGame root).stoppedHistoryFrom
      profile (toExtensiveGame_noChanceOnHistories root)
      current root.size).1 = .Leaf payoff by
        simpa [ExtensiveGame.ObservedGame.stoppedHistoryFrom] using
          hendpoint]
  exact
    toExtensiveGame_isTerminal_leaf root payoff

/-! ### Lawful subgames and occurrence-sensitive backward induction -/

/-- In the occurrence compiler, every complete history is a lawful subgame
root.  Singleton information makes root information sets trivial, and it
also makes information-set closure under continuations immediate. -/
def occurrenceSubgameSystem (root : GameTree N U) :
    (toOccurrenceObservedGame root).SubgameSystem where
  IsRoot := fun _ => True
  init_isRoot := trivial
  lawful := by
    intro subroot _hroot
    constructor
    · intro _hproper i hmover hnonterminal other hother
        hother_nonterminal hsame
      exact (congrArg Subtype.val hsame).symm
    · intro current hcurrent i hmover hnonterminal other hother
        hother_nonterminal hsame
      have hotherCurrent : other = current :=
        ((toOccurrenceObservedGame_hasSingletonInformation root i)
          current other hmover hnonterminal hother
            hother_nonterminal hsame).symm
      simpa [hotherCurrent] using hcurrent

/-- The all-history occurrence system is complete: every structurally lawful
root is already selected because every complete history is selected. -/
def occurrenceCompleteSubgameSystem (root : GameTree N U) :
    (toOccurrenceObservedGame root).CompleteSubgameSystem where
  toSubgameSystem := occurrenceSubgameSystem root
  complete := fun _root _hlawful => trivial

/-- The occurrence compiler terminates on its lawful all-history subgame
system. -/
def toOccurrenceObservedGame_pureTerminationPlanOn
    (root : GameTree N U) :
    ∀ current, (occurrenceSubgameSystem root).IsRoot current →
      (toOccurrenceObservedGame root).PureTerminationPlanAt
        (toExtensiveGame_noChanceOnHistories root) current :=
  fun current _hroot =>
    toOccurrenceObservedGame_pureTerminationPlanOnAllContinuations
      root current trivial

/-- The terminal payoff generated by a genuinely occurrence-dependent pure
profile from one endpoint subtree and its concrete occurrence history. -/
def occurrenceOutcomeFrom
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile) :
    (subtree : GameTree N U) →
      (toExtensiveGame root).toArena.History root subtree →
        (N → U)
  | .Leaf payoff, _history => payoff
  | .Node mover head tail, history =>
      let hnonterminal :=
        toExtensiveGame_not_isTerminal_node
          root mover head tail
      let action :=
        profile.toHistoryPolicy
          (toOccurrenceObservedGame root)
          (toExtensiveGame_noChanceOnHistories root)
          ⟨.Node mover head tail, history⟩ hnonterminal
      occurrenceOutcomeFrom root profile
        action.1 (history.snoc action)
termination_by subtree => subtree.size
decreasing_by
  exact
    size_mem_children_lt mover head tail
      (by simpa [children] using action.2)

/-- The structural occurrence outcome, packaged on a complete typed history. -/
def occurrenceOutcome
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    N → U :=
  occurrenceOutcomeFrom root profile current.1 current.2

@[simp]
theorem occurrenceOutcome_leaf
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (payoff : N → U)
    (history :
      (toExtensiveGame root).toArena.History root (.Leaf payoff)) :
    occurrenceOutcome root profile ⟨.Leaf payoff, history⟩ =
      payoff := by
  rw [occurrenceOutcome, occurrenceOutcomeFrom]

@[simp]
theorem occurrenceOutcome_node
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (mover : N) (head : GameTree N U)
    (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node mover head tail)) :
    occurrenceOutcome root profile
        ⟨.Node mover head tail, history⟩ =
      occurrenceOutcome root profile
        ⟨(profile.toHistoryPolicy
            (toOccurrenceObservedGame root)
            (toExtensiveGame_noChanceOnHistories root)
            ⟨.Node mover head tail, history⟩
            (toExtensiveGame_not_isTerminal_node
              root mover head tail)).1,
          history.snoc
            (profile.toHistoryPolicy
              (toOccurrenceObservedGame root)
              (toExtensiveGame_noChanceOnHistories root)
              ⟨.Node mover head tail, history⟩
              (toExtensiveGame_not_isTerminal_node
                root mover head tail))⟩ := by
  change
    occurrenceOutcomeFrom root profile
        (.Node mover head tail) history =
      occurrenceOutcomeFrom root profile _ _
  rw [occurrenceOutcomeFrom]

/-- Finite stopped execution of an occurrence profile reaches the leaf
described by `occurrenceOutcome` once fuel dominates the current subtree. -/
theorem stoppedHistoryFrom_reaches_occurrenceOutcome
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ)
    (hsize : current.1.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toOccurrenceObservedGame root).stoppedHistoryFrom
        profile (toExtensiveGame_noChanceOnHistories root)
        current fuel).1 =
          .Leaf payoff ∧
      payoff = occurrenceOutcome root profile current := by
  let policy :
      (toExtensiveGame root).toArena.HistoryPolicy root :=
    profile.toHistoryPolicy
      (toOccurrenceObservedGame root)
      (toExtensiveGame_noChanceOnHistories root)
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ (history :
        (toExtensiveGame root).toArena.History root subtree)
      (remaining : ℕ),
      subtree.size ≤ remaining →
        ∃ payoff : N → U,
          ((toExtensiveGame root).toArena.stoppedHistoryFrom
            policy ⟨subtree, history⟩ remaining).1 =
              .Leaf payoff ∧
          payoff =
            occurrenceOutcome root profile
              ⟨subtree, history⟩
  exact
    (GameTree.strong_induction (motive := motive)
      (by
        intro payoff history remaining hremaining
        refine ⟨payoff, ?_, by simp⟩
        rw [Arena.stoppedHistoryFrom_eq_self_of_terminal
          policy ⟨.Leaf payoff, history⟩
          (toExtensiveGame_isTerminal_leaf root payoff)
          remaining])
      (by
        intro mover head tail ih history remaining hremaining
        cases remaining with
        | zero =>
            have hpositive :=
              size_pos (.Node mover head tail)
            omega
        | succ remaining =>
            have hnonterminal :=
              toExtensiveGame_not_isTerminal_node
                root mover head tail
            rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
              policy
              ⟨.Node mover head tail, history⟩
              remaining hnonterminal]
            let action :=
              policy
                ⟨.Node mover head tail, history⟩
                hnonterminal
            have hchildSize :
                action.1.size ≤ remaining := by
              have hlt :=
                size_mem_children_lt mover head tail
                  (by
                    simpa [children] using action.2)
              omega
            rcases ih action.1
                (by simpa [children] using action.2)
                (history.snoc action)
                remaining hchildSize with
              ⟨payoff, hendpoint, hpayoff⟩
            refine ⟨payoff, hendpoint, ?_⟩
            simpa [policy, action] using hpayoff)
      current.1) current.2 fuel hsize

/-- Total terminal continuation payoff agrees with the structural
occurrence outcome. -/
theorem terminalPayoffFrom_eq_occurrenceOutcome
    (root : GameTree N U)
    (profile : (toOccurrenceObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ)
    (hselectedTerminal :
      (toOccurrenceObservedGame root).PureTerminatesAtFuel
        profile (toExtensiveGame_noChanceOnHistories root) current fuel) :
    (toOccurrenceObservedGame root).terminalPayoffFrom
        profile (toExtensiveGame_noChanceOnHistories root)
        current fuel hselectedTerminal =
      occurrenceOutcome root profile current := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistoryFrom_reaches_occurrenceOutcome
      root profile current root.size
      (arenaHistory_subtree current.2).size_le
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toOccurrenceObservedGame root).stoppedHistoryFrom
          profile (toExtensiveGame_noChanceOnHistories root)
          current root.size).1 := by
    change
      (toExtensiveGame root).isTerminal
        ((toOccurrenceObservedGame root).stoppedHistoryFrom
          profile (toExtensiveGame_noChanceOnHistories root)
          current root.size).1
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).payoff
        ((toOccurrenceObservedGame root).toControlledObservedGame
          |>.terminalHistoryFrom
            profile (toExtensiveGame_noChanceOnHistories root)
            current fuel).1 =
      occurrenceOutcome root profile current
  rw [
    (toOccurrenceObservedGame root).toControlledObservedGame
      |>.terminalHistoryFrom_eq_of_terminal
        profile (toExtensiveGame_noChanceOnHistories root)
        current fuel hselectedTerminal root.size hterminal]
  calc
    (toExtensiveGame root).payoff
        ((toOccurrenceObservedGame root).stoppedHistoryFrom
          profile (toExtensiveGame_noChanceOnHistories root)
          current root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = occurrenceOutcome root profile current := hpayoff

/-! ### Forgetting occurrences to endpoint information -/

/-- Forget a private occurrence observation and retain its endpoint subtree. -/
def forgetOccurrenceObservation
    (root : GameTree N U) (i : N)
    (history :
      (toOccurrenceObservedGame root).Observation i) :
    (toObservedGame root).Observation i :=
  history.1

/-- Forget a public occurrence observation and retain its endpoint subtree. -/
def forgetOccurrencePublicObservation
    (root : GameTree N U)
    (history :
      (toOccurrenceObservedGame root).PublicObservation) :
    (toObservedGame root).PublicObservation :=
  history.1

/-- Forget a decision occurrence and retain the endpoint node context used by
the historical `GameTree.PlayerStrategy` compiler. -/
def forgetOccurrenceInfo
    (root : GameTree N U) (i : N)
    (information :
      (toOccurrenceObservedGame root).InfoState i) :
    (toObservedGame root).InfoState i :=
  nodeInfoAt root information.1.1 i information.2.1

/-- Occurrence forgetting identifies player decision histories that have the
same endpoint node. -/
theorem forgetOccurrenceInfo_eq_of_endpoint_eq
    (root : GameTree N U) (i : N)
    (first second :
      (toOccurrenceObservedGame root).InfoState i)
    (hsame : first.1.1 = second.1.1) :
    forgetOccurrenceInfo root i first =
      forgetOccurrenceInfo root i second := by
  rcases first with
    ⟨⟨firstEndpoint, firstPath⟩,
      ⟨firstMover, firstNonterminal⟩⟩
  rcases second with
    ⟨⟨secondEndpoint, secondPath⟩,
      ⟨secondMover, secondNonterminal⟩⟩
  change firstEndpoint = secondEndpoint at hsame
  change
    nodeInfoAt root firstEndpoint i firstMover =
      nodeInfoAt root secondEndpoint i secondMover
  subst secondEndpoint
  rfl

/-- A merged decision endpoint is a concrete obstruction to using occurrence
forgetting as the information-state component of a strict isomorphism. -/
theorem not_injective_forgetOccurrenceInfo_of_merged_histories
    (root : GameTree N U) (i : N)
    (first second :
      (toOccurrenceObservedGame root).InfoState i)
    (hdifferent : first ≠ second)
    (hsame : first.1.1 = second.1.1) :
    ¬ Function.Injective (forgetOccurrenceInfo root i) := by
  intro hinjective
  exact hdifferent
    (hinjective
      (forgetOccurrenceInfo_eq_of_endpoint_eq
        root i first second hsame))

/-- Forgetting a private occurrence observation gives the endpoint
compiler's observation at the same history. -/
@[simp]
theorem forgetOccurrenceObservation_observe
    (root : GameTree N U) (i : N)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    forgetOccurrenceObservation root i
        ((toOccurrenceObservedGame root).observe i history) =
      (toObservedGame root).observe i history :=
  rfl

/-- Forgetting a public occurrence observation gives the endpoint compiler's
public observation at the same history. -/
@[simp]
theorem forgetOccurrencePublicObservation_publicObserve
    (root : GameTree N U)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    forgetOccurrencePublicObservation root
        ((toOccurrenceObservedGame root).publicObserve history) =
      (toObservedGame root).publicObserve history :=
  rfl

/-- Private-to-public projection commutes with occurrence forgetting. -/
@[simp]
theorem forgetOccurrence_publicOf
    (root : GameTree N U) (i : N)
    (observation :
      (toOccurrenceObservedGame root).Observation i) :
    forgetOccurrencePublicObservation root
        ((toOccurrenceObservedGame root).publicOf i observation) =
      (toObservedGame root).publicOf i
        (forgetOccurrenceObservation root i observation) :=
  rfl

/-- Forgetting an occurrence information state's represented observation gives
the endpoint node information's represented subtree. -/
@[simp]
theorem forgetOccurrenceInfo_observe
    (root : GameTree N U) (i : N)
    (information :
      (toOccurrenceObservedGame root).InfoState i) :
    (toObservedGame root).infoObserve i
        (forgetOccurrenceInfo root i information) =
      forgetOccurrenceObservation root i
        ((toOccurrenceObservedGame root).infoObserve
          i information) := by
  exact
    nodeInfoAt_tree root information.1.1 i information.2.1

/-- Forgetting the occurrence information state at a concrete player history
gives exactly the endpoint compiler's node information state. -/
@[simp]
theorem forgetOccurrenceInfo_infoAt
    (root : GameTree N U)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (i : N)
    (hmover :
      (toExtensiveGame root).mover history.1 = some i)
    (hnonterminal :
      (toExtensiveGame root).toArena.IsDecision history.1) :
    forgetOccurrenceInfo root i
        ((toOccurrenceObservedGame root).infoAt
          history i hmover hnonterminal) =
      (toObservedGame root).infoAt history i hmover
        hnonterminal :=
  rfl

/-- Endpoint abstract actions and occurrence abstract actions are equivalent at
every occurrence information state. -/
def forgetOccurrenceInfoActionEquiv
    (root : GameTree N U) (i : N)
    (information :
      (toOccurrenceObservedGame root).InfoState i) :
    (toObservedGame root).InfoAction i
        (forgetOccurrenceInfo root i information) ≃
      (toOccurrenceObservedGame root).InfoAction i
        information :=
  nodeActionEquiv root information.1.1 i information.2.1

/-- The endpoint and occurrence action realizations commute exactly with the
information-action equivalence. -/
@[simp]
theorem forgetOccurrenceInfoActionEquiv_at
    (root : GameTree N U)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (i : N)
    (hmover :
      (toExtensiveGame root).mover history.1 = some i)
    (hnonterminal :
      (toExtensiveGame root).toArena.IsDecision history.1)
    (action :
      (toObservedGame root).InfoAction i
        ((toObservedGame root).infoAt history i hmover
          hnonterminal)) :
    (toOccurrenceObservedGame root).actionEquiv
        history i hmover hnonterminal
        (forgetOccurrenceInfoActionEquiv root i
          ((toOccurrenceObservedGame root).infoAt
            history i hmover hnonterminal)
          action) =
      (toObservedGame root).actionEquiv
        history i hmover hnonterminal action :=
  rfl

/-! ### Information-refinement package -/

/-- The endpoint/`NodeInfo` compiler is the information-coarsened source and
the occurrence-sensitive compiler is its refinement.

The complete-history dynamics are identical. Private observations, public
observations, and decision information forget from complete occurrences to
endpoint data, while endpoint abstract actions lift equivalently at every
occurrence. -/
def endpointInformationRefinement
    (root : GameTree N U) :
    (toObservedGame root).InformationRefinement
      (toOccurrenceObservedGame root) where
  historyIso :=
    Arena.Iso.refl
      (toExtensiveGame root).unfold.toArena
  map_init := rfl
  map_mover := by
    intro history
    rfl
  map_payoff := by
    intro history _
    rfl
  forgetObservation :=
    forgetOccurrenceObservation root
  forget_observe := by
    intro i history
    rfl
  forgetPublic :=
    forgetOccurrencePublicObservation root
  forget_publicObserve := by
    intro history
    rfl
  forget_publicOf := by
    intro i observation
    rfl
  forgetInfo :=
    forgetOccurrenceInfo root
  forget_infoObserve := by
    intro i information
    exact
      (forgetOccurrenceInfo_observe
        root i information).symm
  infoActionEquiv :=
    forgetOccurrenceInfoActionEquiv root
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    exact
      (forgetOccurrenceInfo_infoAt
        root history i hsource hsource_nonterminal).symm
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    rfl

/-- The endpoint compiler's explicit all-continuations analysis roots. -/
def endpointAllContinuationRoots
    (root : GameTree N U) :
    (toObservedGame root).RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
    (toObservedGame root).base

/-- The occurrence compiler's explicit all-continuations analysis roots. -/
def occurrenceAllContinuationRoots
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
    (toOccurrenceObservedGame root).base

/-- The endpoint-to-occurrence refinement preserves the explicitly selected
all-continuations root presentations exactly. -/
theorem endpointInformationRefinement_preservesAllContinuationRoots
    (root : GameTree N U) :
    (endpointInformationRefinement root).PreservesRootPresentations
      (endpointAllContinuationRoots root)
      (occurrenceAllContinuationRoots root) := by
  intro _history
  exact iff_of_true trivial trivial

/-! ### Behavioral/chance-aware refinement -/

/-- The endpoint compiler, viewed through the chance-aware behavioral API.
The compiled tree has no chance histories, so its chance kernel is vacuous. -/
def toObservedChanceGame (root : GameTree N U) :
    ExtensiveGame.ObservedChanceGame N U :=
  ExtensiveGame.ObservedChanceGame.ofNoChance
    (toObservedGame root)
    (toExtensiveGame_noChanceOnHistories root)

/-- The occurrence-sensitive compiler, viewed through the chance-aware
behavioral API. -/
def toOccurrenceObservedChanceGame
    (root : GameTree N U) :
    ExtensiveGame.ObservedChanceGame N U :=
  ExtensiveGame.ObservedChanceGame.ofNoChance
    (toOccurrenceObservedGame root)
    (toExtensiveGame_noChanceOnHistories root)

instance toObservedChanceGame.instTerminalDecidable
    (root : GameTree N U) :
    (state :
      (toObservedChanceGame root).observed.base.State) →
      Decidable
        ((toObservedChanceGame root
          ).observed.base.isTerminal state) :=
  toExtensiveGame_terminalDecidable root

instance toOccurrenceObservedChanceGame.instTerminalDecidable
    (root : GameTree N U) :
    (state :
      (toOccurrenceObservedChanceGame root
        ).observed.base.State) →
      Decidable
        ((toOccurrenceObservedChanceGame root
          ).observed.base.isTerminal state) :=
  toExtensiveGame_terminalDecidable root

/-- The endpoint-to-occurrence information refinement also preserves the
complete behavioral stochastic semantics exactly.  Chance naturality is
vacuous because compiled `GameTree`s have no chance histories. -/
def endpointBehavioralInformationRefinement
    (root : GameTree N U) :
    (toObservedChanceGame root).InformationRefinement
      (toOccurrenceObservedChanceGame root) where
  observedRefinement :=
    endpointInformationRefinement root
  map_chanceKernel := by
    intro history hchance
    have himpossible : False := by
      obtain ⟨i, hmover⟩ :=
        toExtensiveGame_noChanceOnHistories root
          history hchance.2
      exact
        (Option.some_ne_none i)
          (hmover.symm.trans hchance.1)
    exact himpossible.elim

/-- Lifting an endpoint behavioral profile to occurrence information
preserves the complete bounded optional-terminal-payoff law. -/
theorem behavioralStoppedPayoffLawFrom_liftEndpoint
    (root : GameTree N U)
    (profile :
      (toObservedGame root).BehavioralProfile)
    (current :
      (toObservedGame root).base.toArena.HistoryFrom
        (toObservedGame root).base.init)
    (fuel : ℕ) :
    (toOccurrenceObservedChanceGame root
      ).behavioralStoppedPayoffLawFrom
        ((endpointInformationRefinement root
          ).mapBehavioralProfile profile)
        ((endpointInformationRefinement root
          ).historyIso.stateEquiv current)
        fuel =
      (toObservedChanceGame root
        ).behavioralStoppedPayoffLawFrom
          profile current fuel := by
  exact
    (endpointBehavioralInformationRefinement root
      ).map_behavioralStoppedPayoffLawFrom
        profile current fuel

/-- Behavioral Nash on every explicit all-continuations root of the
lifted occurrence-sensitive profile reflects to the endpoint profile.  The
reverse direction is intentionally not claimed: occurrence-dependent
deviations need not descend to endpoint-indexed strategies. -/
theorem isEndpointBehavioralNashOnAllContinuationsAtFuel_of_occurrenceLift
    {V : Type*} [DecidableEq N] [Preorder V]
    (root : GameTree N U)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile :
      (toObservedGame root).BehavioralProfile)
    (fuel : ℕ)
    (hSPE :
      (toOccurrenceObservedChanceGame root
        ).IsBehavioralNashOnRootsAtFuel
          (occurrenceAllContinuationRoots root) utility
          ((endpointInformationRefinement root
            ).mapBehavioralProfile profile)
          fuel) :
    (toObservedChanceGame root
      ).IsBehavioralNashOnRootsAtFuel
        (endpointAllContinuationRoots root) utility profile fuel := by
  exact
    (endpointBehavioralInformationRefinement root
      ).isBehavioralNashOnRootsAtFuel_of_map
        (endpointAllContinuationRoots root)
        (occurrenceAllContinuationRoots root)
        (fun history =>
          (endpointInformationRefinement_preservesAllContinuationRoots
            root history).mp)
        utility profile fuel hSPE

/-! ### Strategy lifting and exact operational semantics -/

/-- Lift an endpoint/node-indexed pure strategy to the finer
occurrence-sensitive information structure. -/
def liftEndpointPureStrategy
    (root : GameTree N U) (i : N)
    (strategy : (toObservedGame root).PureStrategy i) :
    (toOccurrenceObservedGame root).PureStrategy i :=
  fun information =>
    forgetOccurrenceInfoActionEquiv root i information.1
      (strategy
        ((toObservedGame root).representedInfoAt
          information.1.1 i information.1.2.1 information.1.2.2))

/-- Lift a complete endpoint-indexed pure profile occurrence by occurrence. -/
def liftEndpointPureProfile
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile) :
    (toOccurrenceObservedGame root).PureProfile :=
  fun i => liftEndpointPureStrategy root i (profile i)

/-- The reusable information-refinement lift specializes definitionally to the
endpoint strategy lift. -/
theorem endpointInformationRefinement_mapStrategy
    (root : GameTree N U) (i : N)
    (strategy : (toObservedGame root).PureStrategy i) :
    (endpointInformationRefinement root).mapStrategy
        i strategy =
      liftEndpointPureStrategy root i strategy :=
  rfl

/-- The reusable information-refinement profile map specializes
definitionally to the endpoint profile lift. -/
theorem endpointInformationRefinement_mapProfile
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile) :
    (endpointInformationRefinement root).mapProfile
        profile =
      liftEndpointPureProfile root profile :=
  rfl

/-- Lifted and endpoint strategies realize exactly the same concrete action at
every player-controlled history. -/
theorem liftEndpointPureStrategy_actionAt
    (root : GameTree N U) (i : N)
    (strategy : (toObservedGame root).PureStrategy i)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (hmover :
      (toExtensiveGame root).mover history.1 = some i)
    (hnonterminal :
      (toExtensiveGame root).toArena.IsDecision history.1) :
    (liftEndpointPureStrategy root i strategy).actionAt
        (toOccurrenceObservedGame root)
        history hmover hnonterminal =
      strategy.actionAt
        (toObservedGame root)
        history hmover hnonterminal :=
  rfl

/-- Lifted and endpoint profiles realize exactly the same concrete action at
every player-controlled history. -/
theorem liftEndpointPureProfile_actionAt
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (i : N)
    (hmover :
      (toExtensiveGame root).mover history.1 = some i)
    (hnonterminal :
      (toExtensiveGame root).toArena.IsDecision history.1) :
    (liftEndpointPureProfile root profile).actionAt
        (toOccurrenceObservedGame root)
        history i hmover hnonterminal =
      profile.actionAt
        (toObservedGame root)
        history i hmover hnonterminal :=
  rfl

/-- Strategy lifting preserves the complete terminal-aware history policy
definitionally at every nonterminal history. -/
theorem liftEndpointPureProfile_toHistoryPolicy
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile) :
    (liftEndpointPureProfile root profile).toHistoryPolicy
        (toOccurrenceObservedGame root)
        (toExtensiveGame_noChanceOnHistories root) =
      profile.toHistoryPolicy
        (toObservedGame root)
        (toExtensiveGame_noChanceOnHistories root) := by
  funext history hnonterminal
  exact
    liftEndpointPureProfile_actionAt
      root profile history
      ((toObservedGame root).playerAt
        (toExtensiveGame_noChanceOnHistories root)
        history hnonterminal)
      ((toObservedGame root).mover_playerAt
        (toExtensiveGame_noChanceOnHistories root)
        history hnonterminal)
      ((toExtensiveGame root).toArena.isDecision_of_not_isTerminal
        _ hnonterminal)

/-! ### Canonical occurrence-sensitive SPE -/

/-- The backward-induction endpoint plan, lifted to a root-bound
occurrence-sensitive pure profile.

The lift supplies the equilibrium candidate; equilibrium is proved below
against the strictly larger space of genuinely path-dependent deviations. -/
def occurrenceBackwardInductionProfile
    [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).PureProfile :=
  liftEndpointPureProfile root
    (strategyToObservedProfile root
      (optStrategy : Strategy N U))

/-- At every concrete node occurrence, the lifted backward-induction profile
chooses the backward-induction child. -/
theorem occurrenceBackwardInductionProfile_toHistoryPolicy_node
    [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U)
    (mover : N) (head : GameTree N U)
    (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node mover head tail))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal
        (.Node mover head tail)) :
    (occurrenceBackwardInductionProfile root).toHistoryPolicy
        (toOccurrenceObservedGame root)
        (toExtensiveGame_noChanceOnHistories root)
        ⟨.Node mover head tail, history⟩
        hnonterminal =
      (optStrategy : Strategy N U) mover head tail := by
  rw [occurrenceBackwardInductionProfile,
    liftEndpointPureProfile_toHistoryPolicy]
  exact
    strategyHistoryPolicy_node root
      (optStrategy : Strategy N U)
      mover head tail history hnonterminal

/-- The occurrence outcome of the canonical profile equals the
backward-induction value at every concrete history occurrence. -/
theorem occurrenceOutcome_backwardInduction_eq_value
    [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    occurrenceOutcome root
        (occurrenceBackwardInductionProfile root) current =
      value current.1 := by
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ history :
        (toExtensiveGame root).toArena.History root subtree,
      occurrenceOutcome root
          (occurrenceBackwardInductionProfile root)
          ⟨subtree, history⟩ =
        value subtree
  exact
    (GameTree.strong_induction (motive := motive)
      (by
        intro payoff history
        simp)
      (by
        intro mover head tail ih history
        have hnonterminal :=
          toExtensiveGame_not_isTerminal_node
            root mover head tail
        rw [occurrenceOutcome_node,
          occurrenceBackwardInductionProfile_toHistoryPolicy_node
            root mover head tail history hnonterminal]
        rw [ih _ (optStrategy mover head tail).2]
        exact value_optStrategy_eq mover head tail)
      current.1) current.2

/-- Any unilateral occurrence-dependent deviation from backward induction
achieves at most the backward-induction value from every concrete history.

The proof is structural.  At a node owned by the deviator, the chosen child is
bounded by the mover's backward-induction maximum.  At every other node,
`Function.update` leaves the canonical choice unchanged. -/
theorem occurrenceOutcome_deviate_le_value
    [DecidableEq N] [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (i : N)
    (strategy :
      (toOccurrenceObservedGame root).PureStrategy i) :
    occurrenceOutcome root
        (Function.update
          (occurrenceBackwardInductionProfile root)
          i strategy)
        current i ≤
      value current.1 i := by
  let deviated :
      (toOccurrenceObservedGame root).PureProfile :=
    Function.update
      (occurrenceBackwardInductionProfile root)
      i strategy
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ history :
        (toExtensiveGame root).toArena.History root subtree,
      occurrenceOutcome root deviated
          ⟨subtree, history⟩ i ≤
        value subtree i
  suffices hcurrent : motive current.1 by
    simpa [deviated] using hcurrent current.2
  apply GameTree.strong_induction (motive := motive)
  · intro payoff history
    simp
  · intro mover head tail ih history
    have hnonterminal :=
      toExtensiveGame_not_isTerminal_node
        root mover head tail
    let action :=
      deviated.toHistoryPolicy
        (toOccurrenceObservedGame root)
        (toExtensiveGame_noChanceOnHistories root)
        ⟨.Node mover head tail, history⟩
        hnonterminal
    have hmem : action.1 ∈ head :: tail := action.2
    have hchild :=
      ih action.1 hmem (history.snoc action)
    rw [occurrenceOutcome_node]
    change
      occurrenceOutcome root deviated
          ⟨action.1, history.snoc action⟩ i ≤
        value (.Node mover head tail) i
    by_cases hmover : mover = i
    · subst mover
      exact hchild.trans
        (value_Node_ge i head tail action.1 hmem)
    · have haction :
          action =
            (optStrategy : Strategy N U)
              mover head tail := by
        dsimp [action]
        rw [ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
          (toOccurrenceObservedGame root) _ _ _ _ mover rfl]
        have hcanonicalAction :
            (occurrenceBackwardInductionProfile root).actionAt
                (toOccurrenceObservedGame root)
                ⟨.Node mover head tail, history⟩ mover rfl
                ((toExtensiveGame root).toArena
                  |>.isDecision_of_not_isTerminal _ hnonterminal) =
              (optStrategy : Strategy N U)
                mover head tail := by
          rw [←
            ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
              (toOccurrenceObservedGame root)
              (occurrenceBackwardInductionProfile root)
              (toExtensiveGame_noChanceOnHistories root)
              ⟨.Node mover head tail, history⟩
              hnonterminal mover rfl]
          exact
            occurrenceBackwardInductionProfile_toHistoryPolicy_node
              root mover head tail history hnonterminal
        simpa only [deviated,
          ExtensiveGame.ObservedGame.PureProfile.actionAt,
          ExtensiveGame.ObservedGame.PureStrategy.actionAt,
          Function.update_of_ne hmover] using
            hcanonicalAction
      rw [haction] at hchild ⊢
      exact hchild.trans_eq
        (congrArg (fun payoff => payoff i)
          (value_optStrategy_eq mover head tail))

/-- Backward induction is pure subgame-perfect on the all-history lawful
system of the root-bound, occurrence-sensitive compiler.

The theorem quantifies over the lawful all-history subgame system and over all
occurrence-dependent unilateral strategies, not merely endpoint-indexed
plans. -/
theorem occurrenceBackwardInductionProfile_isPureSubgamePerfectOn
    [DecidableEq N] [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).IsPureSubgamePerfectOn
      (toExtensiveGame_noChanceOnHistories root)
      (occurrenceSubgameSystem root)
      (toOccurrenceObservedGame_pureTerminationPlanOn root)
      (fun payoff => payoff)
      (occurrenceBackwardInductionProfile root) := by
  intro current _hroot i strategy
  let termination :=
    toOccurrenceObservedGame_pureTerminationPlanOn root current _hroot
  change
    ((toOccurrenceObservedGame root).terminalPayoffFrom
      (Function.update
        (occurrenceBackwardInductionProfile root)
        i strategy)
      (toExtensiveGame_noChanceOnHistories root)
      current
      (termination.fuel
        (Function.update
          (occurrenceBackwardInductionProfile root) i strategy))
      (termination.terminal
        (Function.update
          (occurrenceBackwardInductionProfile root) i strategy))) i ≤
    ((toOccurrenceObservedGame root).terminalPayoffFrom
      (occurrenceBackwardInductionProfile root)
      (toExtensiveGame_noChanceOnHistories root)
      current
      (termination.fuel (occurrenceBackwardInductionProfile root))
      (termination.terminal
        (occurrenceBackwardInductionProfile root))) i
  rw [terminalPayoffFrom_eq_occurrenceOutcome,
    terminalPayoffFrom_eq_occurrenceOutcome]
  exact
    (occurrenceOutcome_deviate_le_value
      root current i strategy).trans_eq
      (congrArg (fun payoff => payoff i)
        (occurrenceOutcome_backwardInduction_eq_value
          root current).symm)

/-- Backward induction is standard pure SPE on the complete all-history
subgame system of the occurrence compiler. -/
theorem occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect
    [DecidableEq N] [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U) :
    (toOccurrenceObservedGame root).IsPureStandardSubgamePerfect
      (toExtensiveGame_noChanceOnHistories root)
      (occurrenceCompleteSubgameSystem root)
      (toOccurrenceObservedGame_pureTerminationPlanOn root)
      (fun payoff => payoff)
      (occurrenceBackwardInductionProfile root) :=
  occurrenceBackwardInductionProfile_isPureSubgamePerfectOn root

/-- Canonical standard-SPE existence for every finite root-bound
occurrence-sensitive `GameTree` EFG. -/
theorem Kuhn_exists_occurrencePureSPE
    [DecidableEq N] [TotalPreorder U] [DecidableLE U]
    (root : GameTree N U) :
    ∃ profile : (toOccurrenceObservedGame root).PureProfile,
      (toOccurrenceObservedGame root).IsPureStandardSubgamePerfect
        (toExtensiveGame_noChanceOnHistories root)
        (occurrenceCompleteSubgameSystem root)
        (toOccurrenceObservedGame_pureTerminationPlanOn root)
        (fun payoff => payoff)
        profile :=
  ⟨occurrenceBackwardInductionProfile root,
    occurrenceBackwardInductionProfile_isPureStandardSubgamePerfect root⟩

/-- Lifted occurrence profiles and endpoint profiles have exactly the same
bounded stopped history from every continuation. -/
theorem stoppedHistoryFrom_liftEndpointPureProfile
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) :
    (toOccurrenceObservedGame root).stoppedHistoryFrom
        (liftEndpointPureProfile root profile)
        (toExtensiveGame_noChanceOnHistories root)
        current fuel =
      (toObservedGame root).stoppedHistoryFrom
        profile
        (toExtensiveGame_noChanceOnHistories root)
        current fuel := by
  unfold ExtensiveGame.ObservedGame.stoppedHistoryFrom
  rw [liftEndpointPureProfile_toHistoryPolicy]
  rfl

/-- Lifted occurrence profiles and endpoint profiles have exactly the same
bounded optional terminal payoff from every continuation. -/
theorem stoppedPayoffFrom_liftEndpointPureProfile
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) :
    (toOccurrenceObservedGame root).stoppedPayoffFrom
        (liftEndpointPureProfile root profile)
        (toExtensiveGame_noChanceOnHistories root)
        current fuel =
      (toObservedGame root).stoppedPayoffFrom
        profile
        (toExtensiveGame_noChanceOnHistories root)
        current fuel := by
  unfold ExtensiveGame.ObservedGame.stoppedPayoffFrom
  rw [stoppedHistoryFrom_liftEndpointPureProfile]
  rfl

/-- If the lifted occurrence profile is bounded pure Nash on every explicit
all-continuations root
continuation against the finer path-contingent deviation space, then its
endpoint source profile has the corresponding designated-continuation
property. -/
theorem endpoint_isPureNashOnAllContinuationsAtFuel_of_occurrence_lift
    {V : Type*} [DecidableEq N] [Preorder V]
    (root : GameTree N U)
    (utility : Option (N → U) → N → V)
    (profile : (toObservedGame root).PureProfile)
    (fuel : ℕ)
    (hSPE :
      (toOccurrenceObservedGame root).IsPureNashOnRootsAtFuel
        (toExtensiveGame_noChanceOnHistories root)
        (occurrenceAllContinuationRoots root)
        utility
        (liftEndpointPureProfile root profile)
        fuel) :
    (toObservedGame root).IsPureNashOnRootsAtFuel
      (toExtensiveGame_noChanceOnHistories root)
      (endpointAllContinuationRoots root)
      utility profile fuel := by
  exact
    (endpointInformationRefinement root).isPureNashOnRootsAtFuel_of_map
        (toExtensiveGame_noChanceOnHistories root)
        (toExtensiveGame_noChanceOnHistories root)
        (endpointAllContinuationRoots root)
        (occurrenceAllContinuationRoots root)
        (fun history =>
          (endpointInformationRefinement_preservesAllContinuationRoots
            root history).mp)
        utility profile fuel hSPE

/-- If the lifted occurrence profile is Nash on every designated
continuation against every path-contingent fine deviation, then the endpoint
source profile has the corresponding designated-continuation property. -/
theorem endpoint_isPureNashOnAllContinuations_of_occurrence_lift
    {V : Type*} [DecidableEq N] [Preorder V]
    (root : GameTree N U)
    (utility : (N → U) → N → V)
    (profile : (toObservedGame root).PureProfile)
    (hSPE :
      (toOccurrenceObservedGame root).IsPureNashOnRoots
        (toExtensiveGame_noChanceOnHistories root)
        (occurrenceAllContinuationRoots root)
        (toOccurrenceObservedGame_pureTerminationPlanOnAllContinuations root)
        utility
        (liftEndpointPureProfile root profile)) :
    (toObservedGame root).IsPureNashOnRoots
      (toExtensiveGame_noChanceOnHistories root)
      (endpointAllContinuationRoots root)
      (toObservedGame_pureTerminationPlanOnAllContinuations root)
      utility profile := by
  simpa only [
    endpointInformationRefinement_mapProfile] using
      (endpointInformationRefinement root
        ).isPureNashOnRoots_of_map
          (toExtensiveGame_noChanceOnHistories root)
          (toExtensiveGame_noChanceOnHistories root)
          (endpointAllContinuationRoots root)
          (occurrenceAllContinuationRoots root)
          (fun history =>
            (endpointInformationRefinement_preservesAllContinuationRoots
              root history).mp)
          (toObservedGame_pureTerminationPlanOnAllContinuations root)
          (toOccurrenceObservedGame_pureTerminationPlanOnAllContinuations root)
          utility profile hSPE

end GameTree
