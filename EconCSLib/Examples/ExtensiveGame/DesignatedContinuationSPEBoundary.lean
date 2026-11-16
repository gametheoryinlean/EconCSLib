/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved
import Mathlib.Tactic.FinCases

/-!
# EconCSLib.Examples.ExtensiveGame.DesignatedContinuationSPEBoundary

A finite regression separating Nash equilibrium on presentation-designated
continuations from standard subgame-perfect equilibrium.

Player `0` may quit for payoff `(0, 0)` or enter a player-`1` continuation.
The baseline profile quits and carries the incredible threat that player `1`
would choose `(−1, 0)` instead of `(1, 1)`.  It is Nash at the initial root,
but not Nash in the off-path continuation.

`rootOnlyObserved` deliberately designates only the initial history.  The
baseline therefore satisfies
`IsPureNashOnRoots`. A lawful `SubgameSystem`, however, is
structural and may include the off-path root independently of that presentation
metadata. The same endpoint plan lifted to the canonical occurrence compiler
is proved not to satisfy its complete all-history
`IsPureStandardSubgamePerfect` predicate. The occurrence presentation with
only the initial designated root separately proves that a canonical complete
system still exists but is not presentation-visible.
-/

namespace Examples.DesignatedContinuationSPEBoundary

open GameTree

/-- Two strategic players. -/
abbrev Player := Fin 2

def quitPayoff : Player → ℤ
  | 0 => 0
  | 1 => 0

def punishPayoff : Player → ℤ
  | 0 => -1
  | 1 => 0

def rewardPayoff : Player → ℤ
  | 0 => 1
  | 1 => 1

/-- The off-path player-`1` continuation. -/
def continuation : GameTree Player ℤ :=
  .Node 1 (.Leaf punishPayoff) [.Leaf rewardPayoff]

/-- Player `0` may quit immediately or enter `continuation`. -/
def root : GameTree Player ℤ :=
  .Node 0 (.Leaf quitPayoff) [continuation]

/-- The incredible-threat plan always chooses the head child. -/
def threat : Strategy Player ℤ :=
  fun _ head _ => ⟨head, List.mem_cons_self⟩

/-- A deviation which chooses the first tail child at player-`1` nodes and
otherwise chooses the head child. -/
def rewardDeviation : Strategy Player ℤ :=
  fun mover head tail =>
    if _hmover : mover = (1 : Player) then
      match tail with
      | [] => ⟨head, List.mem_cons_self⟩
      | child :: _rest =>
          ⟨child,
            List.mem_cons_of_mem head
              (List.mem_cons_self)⟩
    else
      ⟨head, List.mem_cons_self⟩

theorem rewardDeviation_variant :
    IVariant (1 : Player) threat rewardDeviation := by
  intro mover head tail hmover
  simp [threat, rewardDeviation, hmover]

/-- The threat profile is Nash at the whole-game root. -/
theorem threat_isNashAt_root :
    IsNashAt threat root := by
  intro i deviation hvariant
  fin_cases i
  · change
      outcome deviation
          (.Node (0 : Player) (.Leaf quitPayoff)
            [continuation]) 0 ≤
        outcome threat
          (.Node (0 : Player) (.Leaf quitPayoff)
            [continuation]) 0
    rw [outcome_Node, outcome_Node]
    let choice :=
      deviation (0 : Player) (.Leaf quitPayoff) [continuation]
    have hchoice :
        choice.1 = .Leaf quitPayoff ∨
          choice.1 = continuation := by
      simpa [choice] using choice.2
    rcases hchoice with hquit | hcontinue
    · simp [threat, choice, hquit]
    · have hplayerOne :
          deviation (1 : Player)
              (.Leaf punishPayoff) [.Leaf rewardPayoff] =
            threat (1 : Player)
              (.Leaf punishPayoff) [.Leaf rewardPayoff] :=
        (hvariant 1 (.Leaf punishPayoff) [.Leaf rewardPayoff]
          (by decide)).symm
      change
        outcome deviation choice.1 0 ≤
          outcome threat (.Leaf quitPayoff) 0
      rw [hcontinue]
      change
        outcome deviation
            (.Node (1 : Player) (.Leaf punishPayoff)
              [.Leaf rewardPayoff]) 0 ≤
          outcome threat (.Leaf quitPayoff) 0
      rw [outcome_Node, hplayerOne]
      simp [threat, punishPayoff, quitPayoff]
  · have hrootChoice :
        deviation (0 : Player)
            (.Leaf quitPayoff) [continuation] =
          threat (0 : Player)
            (.Leaf quitPayoff) [continuation] :=
      (hvariant 0 (.Leaf quitPayoff) [continuation]
        (by decide)).symm
    simp [root, outcome_Node, hrootChoice, threat, quitPayoff]

/-- The same profile is not Nash in the off-path continuation: player `1`
strictly benefits by replacing the threat with `rewardDeviation`. -/
theorem threat_not_isNashAt_continuation :
    ¬ IsNashAt threat continuation := by
  intro hnash
  have hbound :=
    hnash (1 : Player) rewardDeviation rewardDeviation_variant
  norm_num [continuation, outcome_Node, threat, rewardDeviation,
    punishPayoff, rewardPayoff] at hbound
  omega

/-- The empty complete history. -/
def initial :
    (toExtensiveGame root).toArena.HistoryFrom root :=
  Arena.HistoryFrom.nil (toExtensiveGame root).toArena root

/-- The concrete action entering the off-path continuation. -/
def enter :
    (toExtensiveGame root).Action root :=
  ⟨continuation,
    List.mem_cons_of_mem (GameTree.Leaf quitPayoff)
      List.mem_cons_self⟩

/-- The off-path continuation as a complete history occurrence. -/
def offPath :
    (toExtensiveGame root).toArena.HistoryFrom root :=
  ⟨continuation, by
    simpa [enter, root, toExtensiveGame, treeArena, arenaNext] using
      (Arena.History.nil.snoc enter)⟩

/-- A finite `GameTree` history ending back at the original root is
heterogeneously equal to the empty history: every selected child has strictly
smaller structural size. -/
theorem rootHistory_heq_nil :
    ∀ {finish : GameTree Player ℤ}
      (history : (toExtensiveGame root).toArena.History root finish),
      finish = root →
        HEq history
          (Arena.History.nil :
            (toExtensiveGame root).toArena.History root root)
  | _, .nil, _ => HEq.rfl
  | _, @Arena.History.snoc _ _ current history action, hfinish => by
      have hcurrent : Subtree current root :=
        arenaHistory_subtree history
      have hle : current.size ≤ root.size :=
        hcurrent.size_le
      cases current with
      | Leaf payoff =>
          exact nomatch action
      | Node mover head tail =>
          have hlt :
              (arenaNext (.Node mover head tail) action).size <
                (GameTree.Node mover head tail).size := by
            simpa [arenaNext] using
              (size_mem_children_lt mover head tail
                (c := action.1) (by
                  simpa [GameTree.children] using action.2))
          have :
              root.size <
                (GameTree.Node mover head tail).size := by
            simpa [toExtensiveGame, treeArena] using
              hfinish ▸ hlt
          omega

/-- A finite `GameTree` history cannot leave the root and later return to the
same root tree value. -/
theorem rootHistory_eq_nil
    (history : (toExtensiveGame root).toArena.History root root) :
    history = Arena.History.nil :=
  eq_of_heq (rootHistory_heq_nil history rfl)

/-- A complete history whose endpoint is the original finite-tree root is the
empty history occurrence. -/
theorem history_eq_initial_of_endpoint_eq
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (hendpoint : history.1 = root) :
    history = initial := by
  rcases history with ⟨state, path⟩
  simp only at hendpoint
  subst state
  rw [rootHistory_eq_nil path]
  rfl

/-- An endpoint-observed presentation which designates only the whole-game
root as a continuation root. -/
def rootOnlyObserved : ExtensiveGame.ObservedGame Player ℤ :=
  toObservedGame root

/-- Initial-only analysis roots, external to the observed-game identity. -/
def rootOnlyRoots : rootOnlyObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.initialOnly
    rootOnlyObserved.base

/-- The contrasting external presentation that exposes every complete
history without changing the observed-game carrier. -/
def allHistoryRoots : rootOnlyObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
    rootOnlyObserved.base

/-- The off-path continuation is absent from the initial-only domain. -/
theorem offPath_not_rootOnlyRoot :
    ¬ rootOnlyRoots.IsRoot offPath := by
  intro hroot
  have heq :
      offPath =
        Arena.HistoryFrom.nil
          rootOnlyObserved.base.toArena
          rootOnlyObserved.base.init := by
    simpa [rootOnlyRoots] using hroot
  have hendpoint :=
    congrArg (fun history => history.1) heq
  change continuation = root at hendpoint
  simp [continuation, root] at hendpoint

/-- The same off-path continuation belongs to the all-history domain. -/
theorem offPath_allHistoryRoot :
    allHistoryRoots.IsRoot offPath :=
  trivial

/-- `initialOnly` and `allHistories` have observably different continuation
domains on the same observed game. -/
theorem initialOnly_and_allHistories_differ :
    ∃ history,
      ¬ rootOnlyRoots.IsRoot history ∧
        allHistoryRoots.IsRoot history :=
  ⟨offPath, offPath_not_rootOnlyRoot, offPath_allHistoryRoot⟩

instance :
    (state : rootOnlyObserved.base.State) →
      Decidable (rootOnlyObserved.base.isTerminal state) :=
  toExtensiveGame_terminalDecidable root

theorem rootOnly_noChance :
    rootOnlyObserved.base.NoChanceOnHistories := by
  simpa [rootOnlyObserved] using
    toExtensiveGame_noChanceOnHistories root

def rootOnly_pureTerminationPlan :
    ∀ current, rootOnlyRoots.IsRoot current →
      rootOnlyObserved.PureTerminationPlanAt rootOnly_noChance current := by
  intro current hroot
  have hcurrent : current = initial := by
    simpa [rootOnlyObserved] using hroot
  subst current
  simpa [rootOnlyObserved, rootOnly_noChance] using
    (toObservedGame_pureTerminationPlanOnAllContinuations
      root initial trivial)

/-- The initial-only presentation still admits a nonempty lawful subgame
system. It is deliberately conservative: its only root is the whole game. -/
def rootOnlySubgameSystem : rootOnlyObserved.SubgameSystem where
  IsRoot := fun current => current = initial
  init_isRoot := rfl
  lawful := by
    intro subroot hroot
    subst subroot
    simpa [rootOnlyObserved, initial] using
      rootOnlyObserved.init_isLawfulSubgameRoot

/-- The strategic threat profile translated to the root-only presentation. -/
def threatProfile : rootOnlyObserved.PureProfile :=
  playerProfileToObservedProfile root (fun _ => threat)

/-- The same endpoint-indexed threat profile in the ordinary all-history
compiler. -/
def endpointThreatProfile : (toObservedGame root).PureProfile :=
  playerProfileToObservedProfile root (fun _ => threat)

/-- The represented root decision coordinate. -/
def rootInformation : (toObservedGame root).RepresentedInfo (0 : Player) :=
  ⟨⟨0, .Leaf quitPayoff, [continuation]⟩, ⟨{
    history := initial
    mover := rfl
    decision :=
      (toExtensiveGame root).toArena.isDecision_of_not_isTerminal _
        (toExtensiveGame_not_isTerminal_node root 0
          (.Leaf quitPayoff) [continuation])
    infoAt_eq := rfl
  }⟩⟩

/-- The represented off-path player-`1` decision coordinate. -/
def continuationInformation :
    (toObservedGame root).RepresentedInfo (1 : Player) :=
  ⟨⟨1, .Leaf punishPayoff, [.Leaf rewardPayoff]⟩, ⟨{
    history := offPath
    mover := rfl
    decision :=
      (toExtensiveGame root).toArena.isDecision_of_not_isTerminal _
        (toExtensiveGame_not_isTerminal_node root 1
          (.Leaf punishPayoff) [.Leaf rewardPayoff])
    infoAt_eq := rfl
  }⟩⟩

/-- Direct observed execution at the root uses the represented root
coordinate, independently of the proof object carried by the history. -/
theorem observedActionAtNode_root_choice
    (profile : (toObservedGame root).PureProfile)
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node (0 : Player) (.Leaf quitPayoff) [continuation])) :
    observedActionAtNode root profile 0 (.Leaf quitPayoff) [continuation]
        history =
      profile 0 rootInformation := by
  rfl

/-- Direct observed execution at the off-path node uses its represented
continuation coordinate for every concrete occurrence history. -/
theorem observedActionAtNode_continuation_choice
    (profile : (toObservedGame root).PureProfile)
    (history :
      (toExtensiveGame root).toArena.History root
        (.Node (1 : Player) (.Leaf punishPayoff)
          [.Leaf rewardPayoff])) :
    observedActionAtNode root profile 1 (.Leaf punishPayoff)
        [.Leaf rewardPayoff] history =
      profile 1 continuationInformation := by
  rfl

/-- A profile choosing the punishment child at the continuation evaluates to
the punishment payoff from every concrete history ending there. -/
theorem observedOutcomeFrom_continuation_eq_punish
    (profile : (toObservedGame root).PureProfile)
    (current : (toExtensiveGame root).toArena.HistoryFrom root)
    (hcurrent : current.1 = continuation)
    (hchoice :
      profile 1 continuationInformation =
        (⟨.Leaf punishPayoff, List.mem_cons_self⟩ :
          (toObservedGame root).InfoAction 1
            continuationInformation.1)) :
    observedOutcomeFrom root profile current = punishPayoff := by
  rcases current with ⟨state, history⟩
  simp only at hcurrent
  subst state
  change
    observedOutcomeFrom root profile
      ⟨.Node (1 : Player) (.Leaf punishPayoff) [.Leaf rewardPayoff],
        history⟩ = punishPayoff
  rw [observedOutcomeFrom_node,
    observedActionAtNode_continuation_choice, hchoice]
  apply observedOutcomeFrom_eq_of_endpoint_leaf
  rfl

@[simp]
theorem threatProfile_root_apply :
    threatProfile 0 rootInformation =
      (⟨.Leaf quitPayoff, List.mem_cons_self⟩ :
        (toObservedGame root).InfoAction 0 rootInformation.1) :=
  rfl

@[simp]
theorem threatProfile_continuation_apply :
    threatProfile 1 continuationInformation =
      (⟨.Leaf punishPayoff, List.mem_cons_self⟩ :
        (toObservedGame root).InfoAction 1
          continuationInformation.1) :=
  rfl

@[simp]
theorem endpointThreatProfile_continuation_apply :
    endpointThreatProfile 1 continuationInformation =
      (⟨.Leaf punishPayoff, List.mem_cons_self⟩ :
        (toObservedGame root).InfoAction 1
          continuationInformation.1) :=
  rfl

/-- Executable regression: compiling and evaluating the endpoint threat
profile reaches the immediate-quit payoff. -/
example :
    (observedToGameForm root).outcome endpointThreatProfile 0 = 0 ∧
      (observedToGameForm root).outcome endpointThreatProfile 1 = 0 := by
  native_decide

@[simp]
theorem rewardObserved_continuation_apply :
    playerStrategyToObservedStrategy root 1 rewardDeviation
        continuationInformation =
      (⟨.Leaf rewardPayoff,
        List.mem_cons_of_mem (GameTree.Leaf punishPayoff)
          List.mem_cons_self⟩ :
        (toObservedGame root).InfoAction 1
          continuationInformation.1) := by
  simp [playerStrategyToObservedStrategy, rewardDeviation,
    continuationInformation]

/-- The endpoint threat lifted into the occurrence-sensitive strategy
space. -/
def occurrenceThreatProfile :
    (toOccurrenceObservedGame root).PureProfile :=
  liftEndpointPureProfile root endpointThreatProfile

example : occurrenceOutcome root occurrenceThreatProfile
    ⟨root, Arena.History.nil⟩ 0 = 0 := by
  native_decide

/-- The incredible-threat profile passes the deliberately weak
designated-continuation predicate because only the initial root is checked. -/
theorem threat_isNashOnInitialRoot :
    rootOnlyObserved.IsPureNashOnRoots
      rootOnly_noChance rootOnlyRoots rootOnly_pureTerminationPlan
      (fun payoff => payoff) threatProfile := by
  intro current hroot
  have hcurrent : current = initial := by
    simpa [rootOnlyObserved] using hroot
  subst current
  intro i deviation
  let termination := rootOnly_pureTerminationPlan initial
    (by simpa [rootOnlyRoots, rootOnlyObserved, initial])
  change
    (toObservedGame root).terminalPayoffFrom
        (Function.update threatProfile i deviation)
        (toExtensiveGame_noChanceOnHistories root) initial
        (termination.fuel (Function.update threatProfile i deviation))
        (termination.terminal
          (Function.update threatProfile i deviation)) i ≤
      (toObservedGame root).terminalPayoffFrom
        threatProfile (toExtensiveGame_noChanceOnHistories root) initial
        (termination.fuel threatProfile)
        (termination.terminal threatProfile) i
  rw [terminalPayoffFrom_observedProfile_eq_outcome root,
    terminalPayoffFrom_observedProfile_eq_outcome root]
  fin_cases i
  · change
      observedOutcomeFrom root
          (Function.update threatProfile 0 deviation) initial 0 ≤
        observedOutcomeFrom root threatProfile initial 0
    simp only [initial, Arena.HistoryFrom.nil]
    change
      observedOutcomeFrom root
          (Function.update threatProfile 0 deviation)
          ⟨.Node (0 : Player) (.Leaf quitPayoff) [continuation],
            Arena.History.nil⟩ 0 ≤
        observedOutcomeFrom root threatProfile
          ⟨.Node (0 : Player) (.Leaf quitPayoff) [continuation],
            Arena.History.nil⟩ 0
    rw [observedOutcomeFrom_node, observedOutcomeFrom_node]
    rw [observedActionAtNode_root_choice,
      observedActionAtNode_root_choice]
    rw [Function.update_self, threatProfile_root_apply]
    have hchoice :
        (deviation rootInformation).1 = .Leaf quitPayoff ∨
          (deviation rootInformation).1 = continuation := by
      simpa [rootInformation] using (deviation rootInformation).2
    rcases hchoice with hquit | hcontinue
    · rw [observedOutcomeFrom_eq_of_endpoint_leaf root _ _
          quitPayoff hquit,
        observedOutcomeFrom_eq_of_endpoint_leaf root _ _
          quitPayoff rfl]
    · have hupdatedChoice :
          (Function.update threatProfile 0 deviation)
              1 continuationInformation =
            (⟨.Leaf punishPayoff, List.mem_cons_self⟩ :
              (toObservedGame root).InfoAction 1
                continuationInformation.1) := by
        rw [Function.update_of_ne (by decide)]
        exact threatProfile_continuation_apply
      rw [observedOutcomeFrom_continuation_eq_punish
          (Function.update threatProfile 0 deviation) _ hcontinue
          hupdatedChoice,
        observedOutcomeFrom_eq_of_endpoint_leaf root _ _
          quitPayoff rfl]
      simp [punishPayoff, quitPayoff]
  · change
      observedOutcomeFrom root
          (Function.update threatProfile 1 deviation) initial 1 ≤
        observedOutcomeFrom root threatProfile initial 1
    simp only [initial, Arena.HistoryFrom.nil]
    change
      observedOutcomeFrom root
          (Function.update threatProfile 1 deviation)
          ⟨.Node (0 : Player) (.Leaf quitPayoff) [continuation],
            Arena.History.nil⟩ 1 ≤
        observedOutcomeFrom root threatProfile
          ⟨.Node (0 : Player) (.Leaf quitPayoff) [continuation],
            Arena.History.nil⟩ 1
    rw [observedOutcomeFrom_node, observedOutcomeFrom_node]
    rw [observedActionAtNode_root_choice,
      observedActionAtNode_root_choice]
    rw [Function.update_of_ne (by decide)]
    rw [threatProfile_root_apply]
    simp [quitPayoff]

/-- Relative to the explicit conservative initial-only lawful system, the
threat satisfies subgame perfection *on that system* exactly because its sole
tested subgame is the whole game. The `On` suffix keeps this weaker coverage
visible and makes no complete standard-SPE claim. -/
theorem threat_isPureSubgamePerfectOn_rootOnly :
    rootOnlyObserved.IsPureSubgamePerfectOn
      rootOnly_noChance rootOnlySubgameSystem
      (fun current hroot =>
        rootOnly_pureTerminationPlan current
          (by simpa [rootOnlyRoots, rootOnlySubgameSystem] using hroot))
      (fun payoff => payoff) threatProfile := by
  intro current hroot
  exact
    threat_isNashOnInitialRoot current
      (by simpa [rootOnlyRoots, rootOnlySubgameSystem] using hroot)

/-- The off-path continuation fails the corresponding local Nash test in the
ordinary all-history endpoint compiler. -/
theorem threat_fails_offPath_continuation :
    ¬ ((toObservedGame root).terminalContinuationGameForm
        (toExtensiveGame_noChanceOnHistories root) offPath
        ((toObservedGame_pureTerminationPlanOnAllContinuations root)
          offPath trivial)).IsNash
      (fun payoff : Player → ℤ => payoff)
      (playerProfileToObservedProfile root
        (fun _ => threat)) := by
  intro hnash
  have hbound :=
    hnash (1 : Player)
      (playerStrategyToObservedStrategy root 1 rewardDeviation)
  let termination :=
    toObservedGame_pureTerminationPlanOnAllContinuations
      root offPath trivial
  change
    (toObservedGame root).terminalPayoffFrom
        (Function.update endpointThreatProfile 1
          (playerStrategyToObservedStrategy root 1 rewardDeviation))
        (toExtensiveGame_noChanceOnHistories root) offPath
        (termination.fuel
          (Function.update endpointThreatProfile 1
            (playerStrategyToObservedStrategy root 1 rewardDeviation)))
        (termination.terminal
          (Function.update endpointThreatProfile 1
            (playerStrategyToObservedStrategy root 1 rewardDeviation))) 1 ≤
      (toObservedGame root).terminalPayoffFrom
        endpointThreatProfile
        (toExtensiveGame_noChanceOnHistories root) offPath
        (termination.fuel endpointThreatProfile)
        (termination.terminal endpointThreatProfile) 1
    at hbound
  rw [terminalPayoffFrom_observedProfile_eq_outcome root,
    terminalPayoffFrom_observedProfile_eq_outcome root] at hbound
  change
    observedOutcomeFrom root
        (Function.update endpointThreatProfile 1
          (playerStrategyToObservedStrategy root 1 rewardDeviation))
        offPath 1 ≤
      observedOutcomeFrom root endpointThreatProfile offPath 1
    at hbound
  simp only [offPath, continuation, observedOutcomeFrom_node] at hbound
  rw [observedActionAtNode_continuation_choice,
    observedActionAtNode_continuation_choice,
    Function.update_self,
    rewardObserved_continuation_apply] at hbound
  rw [endpointThreatProfile_continuation_apply] at hbound
  rw [observedOutcomeFrom_eq_of_endpoint_leaf root _ _ rewardPayoff rfl,
    observedOutcomeFrom_eq_of_endpoint_leaf root _ _ punishPayoff rfl]
    at hbound
  norm_num [rewardPayoff, punishPayoff] at hbound
  omega

/-- The lifted threat fails standard all-history SPE in the canonical
occurrence-sensitive compiler.

If it were standard SPE, its Nash property at every lawful occurrence root
would reflect along the endpoint-information quotient.  In particular the
off-path endpoint continuation would be Nash, contradicting the explicit
profitable player-`1` deviation above. -/
theorem occurrenceThreat_not_isPureStandardSubgamePerfect :
    ¬ (toOccurrenceObservedGame root).IsPureStandardSubgamePerfect
      (toExtensiveGame_noChanceOnHistories root)
      (occurrenceCompleteSubgameSystem root)
      (toOccurrenceObservedGame_pureTerminationPlanOn root)
      (fun payoff : Player → ℤ => payoff)
      occurrenceThreatProfile := by
  intro hspe
  have hOccurrenceAllContinuations :
      (toOccurrenceObservedGame root).IsPureNashOnRoots
          (toExtensiveGame_noChanceOnHistories root)
          (occurrenceAllContinuationRoots root)
          (toOccurrenceObservedGame_pureTerminationPlanOnAllContinuations root)
          (fun payoff : Player → ℤ => payoff)
          occurrenceThreatProfile := by
    intro current _hroot
    exact hspe current trivial
  have hEndpointAllContinuations :
      (toObservedGame root).IsPureNashOnRoots
        (toExtensiveGame_noChanceOnHistories root)
        (endpointAllContinuationRoots root)
        (toObservedGame_pureTerminationPlanOnAllContinuations root)
        (fun payoff : Player → ℤ => payoff)
        endpointThreatProfile :=
    endpoint_isPureNashOnAllContinuations_of_occurrence_lift
      root (fun payoff : Player → ℤ => payoff)
      endpointThreatProfile hOccurrenceAllContinuations
  exact
    threat_fails_offPath_continuation
      (hEndpointAllContinuations offPath trivial)

/-- The occurrence presentation with the same dynamics and information but
only the initial designated root. This isolates root-coverage metadata from
the endpoint/occurrence strategy distinction. -/
def rootOnlyOccurrenceObserved : ExtensiveGame.ObservedGame Player ℤ :=
  toOccurrenceObservedGame root

/-- Initial-only analysis roots for the occurrence presentation. -/
def rootOnlyOccurrenceRoots :
    rootOnlyOccurrenceObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.initialOnly
    rootOnlyOccurrenceObserved.base

/-- The off-path history is structurally lawful independently of whether the
presentation chose to designate it. -/
theorem rootOnlyOccurrence_offPath_isLawful :
    rootOnlyOccurrenceObserved.IsLawfulSubgameRoot offPath := by
  constructor
  · intro _hproper i hmover hnonterminal other hother
      hother_nonterminal hsame
    exact (congrArg Subtype.val hsame).symm
  · intro current hcurrent i hmover hnonterminal other hother
      hother_nonterminal hsame
    have hotherCurrent : other = current :=
      (congrArg Subtype.val hsame).symm
    simpa [hotherCurrent] using hcurrent

/-- A complete standard-subgame system exists independently of designated
continuation metadata. -/
theorem rootOnlyOccurrence_completeSubgameSystem_exists :
    Nonempty rootOnlyOccurrenceObserved.CompleteSubgameSystem :=
  ⟨ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
    rootOnlyOccurrenceObserved⟩

/-- The canonical complete system includes the structurally lawful off-path
root even though the presentation does not designate it. -/
theorem rootOnlyOccurrence_canonical_admits_offPath :
    (ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
      rootOnlyOccurrenceObserved).toSubgameSystem.IsRoot offPath :=
  rootOnlyOccurrence_offPath_isLawful

/-- Designated-root metadata remains genuinely weaker: the canonical complete
system for the initial-only presentation is not presentation-visible. -/
theorem rootOnlyOccurrence_canonical_not_presentationVisible :
    ¬ (ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
        rootOnlyOccurrenceObserved
      ).toSubgameSystem.IsVisibleIn rootOnlyOccurrenceRoots := by
  intro hvisible
  have hdesignated :=
    hvisible offPath
      rootOnlyOccurrence_canonical_admits_offPath
  have heq : offPath = initial := by
    simpa [rootOnlyOccurrenceRoots, rootOnlyOccurrenceObserved] using
      hdesignated
  have hlength :
      offPath.2.length = initial.2.length :=
    congrArg (fun history => history.2.length) heq
  change 1 = 0 at hlength
  omega

end Examples.DesignatedContinuationSPEBoundary
