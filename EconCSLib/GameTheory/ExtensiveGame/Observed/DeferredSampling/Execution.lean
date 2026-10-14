/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Core

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution

Fresh-query compilation and exact presampled/on-demand execution laws.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- Bounded complete-history law of a mixed contingent-plan profile. -/
def mixedStoppedHistoryLawFrom
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    FiniteLaw
      (G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :=
  (profile.pureProfileLaw G.observed).bind
    fun pureProfile =>
      G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          (pureProfile.toBehavioral G.observed))
        current fuel

/-- Mixed payoff execution is the pushforward of mixed complete-history
execution by the terminal-payoff observer. -/
theorem mixedStoppedPayoffLawFrom_eq_map_history
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedPayoffLawFrom
        profile current fuel =
      (G.mixedStoppedHistoryLawFrom
        profile current fuel).map
          G.stoppedPayoffAtHistory := by
  unfold mixedStoppedPayoffLawFrom
    mixedStoppedHistoryLawFrom
    behavioralStoppedPayoffLawFrom
  rw [FiniteLaw.map_bind]

/-- Compile bounded observed chance-EFG execution into a fresh-query tree.

Player decisions query abstract information actions; chance decisions retain
the declared concrete-action kernel. -/
def boundedHistoryTree
    (G : ObservedChanceGame N U)
    [LinearOrder G.observed.DecisionKey]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (hnoAbsent : G.observed.NoAbsentMindedness)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (remaining :
      Finset G.observed.DecisionKey)
    (havailable :
      G.observed.FutureDecisionKeysAvailable
        current remaining) :
    (fuel : ℕ) →
      FiniteLaw.FreshQueryTree
        G.observed.DecisionValue
        (G.observed.base.toArena.HistoryFrom
          G.observed.base.init)
        remaining
  | 0 =>
      .done current
  | fuel + 1 =>
      if hterminal :
          G.observed.base.isTerminal current.1 then
        .done current
      else
        match hmover :
            G.observed.base.mover current.1 with
        | some i =>
            let key : G.observed.DecisionKey :=
              ⟨i,
                G.observed.representedInfoAt current i hmover
                  (G.observed.base.toArena.isDecision_of_not_isTerminal _
                    hterminal)⟩
            let selected : ↥remaining :=
              ⟨key,
                havailable.current i hmover hterminal⟩
            .query selected fun abstractAction =>
              let action :=
                G.observed.actionEquiv
                  current i hmover
                    (G.observed.base.toArena.isDecision_of_not_isTerminal _
                      hterminal)
                  abstractAction
              G.boundedHistoryTree
                hnoAbsent
                ⟨G.observed.base.next
                    current.1 action,
                  current.2.snoc action⟩
                (remaining.erase key)
                (havailable.afterPlayer
                  hnoAbsent i hmover hterminal action)
                fuel
        | none =>
            .chance
              (G.chanceKernel current
                ⟨hmover, hterminal⟩)
              fun action =>
                G.boundedHistoryTree
                  hnoAbsent
                  ⟨G.observed.base.next
                      current.1 action,
                    current.2.snoc action⟩
                  remaining
                  (havailable.afterChance action)
                  fuel

/-- On-demand execution of the compiled fresh-query tree is exactly the
ordinary bounded behavioral history law. -/
theorem boundedHistoryTree_runOnDemand
    (G : ObservedChanceGame N U)
    [LinearOrder G.observed.DecisionKey]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    (hnoAbsent : G.observed.NoAbsentMindedness)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (remaining :
      Finset G.observed.DecisionKey)
    (havailable :
      G.observed.FutureDecisionKeysAvailable
        current remaining) :
    ∀ fuel : ℕ,
      FiniteLaw.FreshQueryTree.runOnDemand
          (profile.decisionLaw G.observed)
          (G.boundedHistoryTree
            hnoAbsent current remaining
            havailable fuel) =
        G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel := by
  intro fuel
  induction fuel generalizing current remaining with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simp [boundedHistoryTree, hterminal,
          FiniteLaw.FreshQueryTree.runOnDemand]
      · rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
            (BehavioralProfile.toHistoryPolicy G profile)
            current fuel hterminal]
        rw [boundedHistoryTree, dif_neg hterminal]
        split
        · rename_i i hmover
          let hdecision :=
            G.observed.base.toArena.isDecision_of_not_isTerminal
              current.1 hterminal
          rw [BehavioralProfile.toHistoryPolicy_of_mover
            G profile current hterminal i hmover]
          unfold ObservedGame.BehavioralProfile.actionLawAt
            ObservedGame.BehavioralStrategy.actionLawAt
            ControlledObservedGame.BehavioralStrategy.actionLawAt
          dsimp only
          rw [FiniteLaw.bind_map]
          change
            (profile i
                (G.observed.representedInfoAt
                  current i hmover hdecision)).bind
                (fun abstractAction =>
                  FiniteLaw.FreshQueryTree.runOnDemand
                    (profile.decisionLaw G.observed)
                    (G.boundedHistoryTree
                      hnoAbsent
                      ⟨G.observed.base.next current.1
                          (G.observed.actionEquiv
                            current i hmover hdecision
                            abstractAction),
                        current.2.snoc
                          (G.observed.actionEquiv
                            current i hmover hdecision
                            abstractAction)⟩
                      (remaining.erase
                        (⟨i,
                          G.observed.representedInfoAt
                            current i hmover hdecision⟩ :
                          G.observed.DecisionKey))
                      (havailable.afterPlayer
                        hnoAbsent i hmover hterminal
                        (G.observed.actionEquiv
                          current i hmover hdecision
                          abstractAction))
                      fuel)) =
              (profile i
                (G.observed.representedInfoAt
                  current i hmover hdecision)).bind
                (fun abstractAction =>
                  G.observed.base.toArena.stochasticHistoryLawFrom
                      (BehavioralProfile.toHistoryPolicy
                        G profile)
                      ⟨G.observed.base.next current.1
                          (G.observed.actionEquiv
                            current i hmover hdecision
                            abstractAction),
                        current.2.snoc
                          (G.observed.actionEquiv
                            current i hmover hdecision
                            abstractAction)⟩
                      fuel)
          apply congrArg (fun continuation =>
            (profile i
              (G.observed.representedInfoAt
                current i hmover hdecision)).bind continuation)
          funext abstractAction
          exact
            ih
              ⟨G.observed.base.next current.1
                  (G.observed.actionEquiv
                    current i hmover hdecision abstractAction),
                current.2.snoc
                  (G.observed.actionEquiv
                    current i hmover hdecision abstractAction)⟩
              (remaining.erase
                (⟨i,
                  G.observed.representedInfoAt current i hmover
                    hdecision⟩ :
                  G.observed.DecisionKey))
              (havailable.afterPlayer
                hnoAbsent i hmover hterminal
                (G.observed.actionEquiv
                  current i hmover hdecision abstractAction))
        · rename_i hmover
          rw [BehavioralProfile.toHistoryPolicy_of_chance
            G profile current hterminal hmover]
          change
            (G.chanceKernel current
              ⟨hmover, hterminal⟩).bind
                (fun action =>
                  FiniteLaw.FreshQueryTree.runOnDemand
                    (profile.decisionLaw G.observed)
                    (G.boundedHistoryTree
                      hnoAbsent
                      ⟨G.observed.base.next
                          current.1 action,
                        current.2.snoc action⟩
                      remaining
                      (havailable.afterChance action)
                      fuel)) =
              (G.chanceKernel current
                ⟨hmover, hterminal⟩).bind
                  (fun action =>
                    G.observed.base.toArena.stochasticHistoryLawFrom
                        (BehavioralProfile.toHistoryPolicy
                          G profile)
                        ⟨G.observed.base.next
                            current.1 action,
                          current.2.snoc action⟩
                        fuel)
          apply congrArg (fun continuation =>
            (G.chanceKernel current
              ⟨hmover, hterminal⟩).bind continuation)
          funext action
          exact
            ih
              ⟨G.observed.base.next current.1 action,
                current.2.snoc action⟩
              remaining
              (havailable.afterChance action)

/-- Looking up a fixed complete decision table in the compiled tree is
exactly behavioral execution of the corresponding pure contingent-plan
profile. -/
theorem boundedHistoryTree_runWithTable
    (G : ObservedChanceGame N U)
    [LinearOrder G.observed.DecisionKey]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (hnoAbsent : G.observed.NoAbsentMindedness)
    (fullTable :
      (key : G.observed.DecisionKey) →
        G.observed.DecisionValue key)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (remaining :
      Finset G.observed.DecisionKey)
    (havailable :
      G.observed.FutureDecisionKeysAvailable
        current remaining)
    (table :
      (key : ↥remaining) →
        G.observed.DecisionValue key.1)
    (hagrees :
      ∀ key : ↥remaining,
        table key = fullTable key.1) :
    ∀ fuel : ℕ,
      FiniteLaw.FreshQueryTree.runWithTable
          (G.boundedHistoryTree
            hnoAbsent current remaining
            havailable fuel)
          table =
        G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G
            ((G.observed.decisionTableEquiv
              fullTable).toBehavioral G.observed))
          current fuel := by
  intro fuel
  induction fuel generalizing current remaining with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simp [boundedHistoryTree, hterminal,
          FiniteLaw.FreshQueryTree.runWithTable]
      · rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
            (BehavioralProfile.toHistoryPolicy G
              ((G.observed.decisionTableEquiv
                fullTable).toBehavioral G.observed))
            current fuel hterminal]
        rw [boundedHistoryTree, dif_neg hterminal]
        split
        · rename_i i hmover
          let hdecision :=
            G.observed.base.toArena.isDecision_of_not_isTerminal
              current.1 hterminal
          rw [G.pureProfile_toBehavioral_toHistoryPolicy_of_mover
            (G.observed.decisionTableEquiv fullTable)
            current hterminal i hmover]
          rw [FiniteLaw.pure_bind]
          unfold ObservedGame.PureProfile.actionAt
            ObservedGame.PureStrategy.actionAt
            ControlledObservedGame.PureStrategy.actionAt
          change
            FiniteLaw.FreshQueryTree.runWithTable
                (G.boundedHistoryTree
                  hnoAbsent
                  ⟨G.observed.base.next current.1
                      (G.observed.actionEquiv
                        current i hmover hdecision
                        (table
                          ⟨⟨i,
                            G.observed.representedInfoAt
                              current i hmover hdecision⟩,
                            havailable.current i hmover hterminal⟩)),
                    current.2.snoc
                      (G.observed.actionEquiv
                        current i hmover hdecision
                        (table
                          ⟨⟨i,
                            G.observed.representedInfoAt
                              current i hmover hdecision⟩,
                            havailable.current i hmover hterminal⟩))⟩
                  (remaining.erase
                    (⟨i,
                      G.observed.representedInfoAt current i hmover
                        hdecision⟩ :
                      G.observed.DecisionKey))
                  (havailable.afterPlayer
                    hnoAbsent i hmover hterminal
                    (G.observed.actionEquiv
                      current i hmover hdecision
                      (table
                        ⟨⟨i,
                          G.observed.representedInfoAt
                            current i hmover hdecision⟩,
                          havailable.current i hmover hterminal⟩)))
                  fuel)
                (FiniteLaw.FreshQueryTree.eraseTable
                  ⟨⟨i,
                    G.observed.representedInfoAt current i hmover
                      hdecision⟩,
                    havailable.current i hmover hterminal⟩
                  table) =
              G.observed.base.toArena.stochasticHistoryLawFrom
                (BehavioralProfile.toHistoryPolicy G
                  ((G.observed.decisionTableEquiv
                    fullTable).toBehavioral
                      G.observed))
                ⟨G.observed.base.next current.1
                    (G.observed.actionEquiv
                      current i hmover hdecision
                      (fullTable
                      ⟨i,
                          G.observed.representedInfoAt
                            current i hmover hdecision⟩)),
                  current.2.snoc
                    (G.observed.actionEquiv
                      current i hmover hdecision
                      (fullTable
                      ⟨i,
                          G.observed.representedInfoAt
                            current i hmover hdecision⟩))⟩
                fuel
          rw [hagrees
            ⟨⟨i,
              G.observed.representedInfoAt current i hmover
                hdecision⟩,
              havailable.current i hmover hterminal⟩]
          apply
            ih
              ⟨G.observed.base.next current.1
                  (G.observed.actionEquiv
                    current i hmover hdecision
                    (fullTable
                      ⟨i,
                        G.observed.representedInfoAt
                          current i hmover hdecision⟩)),
                current.2.snoc
                  (G.observed.actionEquiv
                    current i hmover hdecision
                    (fullTable
                      ⟨i,
                        G.observed.representedInfoAt
                          current i hmover hdecision⟩))⟩
              (remaining.erase
                (⟨i,
                  G.observed.representedInfoAt current i hmover
                    hdecision⟩ :
                  G.observed.DecisionKey))
              (havailable.afterPlayer
                hnoAbsent i hmover hterminal
                (G.observed.actionEquiv
                  current i hmover hdecision
                  (fullTable
                    ⟨i,
                      G.observed.representedInfoAt
                        current i hmover hdecision⟩)))
              (FiniteLaw.FreshQueryTree.eraseTable
                ⟨⟨i,
                  G.observed.representedInfoAt current i hmover
                    hdecision⟩,
                  havailable.current i hmover hterminal⟩
                table)
          intro key
          exact
            hagrees
              ⟨key.1,
                (Finset.mem_erase.mp key.2).2⟩
        · rename_i hmover
          rw [BehavioralProfile.toHistoryPolicy_of_chance
            G
            ((G.observed.decisionTableEquiv
              fullTable).toBehavioral G.observed)
            current hterminal hmover]
          apply congrArg (fun continuation =>
            (G.chanceKernel current
              ⟨hmover, hterminal⟩).bind continuation)
          funext action
          exact
            ih
              ⟨G.observed.base.next current.1 action,
                current.2.snoc action⟩
              remaining
              (havailable.afterChance action)
              table
              hagrees

/-- The presampled fresh-query execution is the mixed complete-history law
generated by the flat product over all global decision keys. -/
theorem boundedHistoryTree_runPresampled_eq_flatMixed
    (G : ObservedChanceGame N U)
    [Fintype G.observed.DecisionKey]
    [LinearOrder G.observed.DecisionKey]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    (hnoAbsent : G.observed.NoAbsentMindedness)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    FiniteLaw.FreshQueryTree.runPresampled
        (profile.decisionLaw G.observed)
        (G.boundedHistoryTree
          hnoAbsent current Finset.univ
          (ObservedGame.FutureDecisionKeysAvailable.univ
            current)
          fuel) |>.Equivalent
      (((FiniteLaw.fintypePi
        (profile.decisionLaw G.observed)).map
          G.observed.decisionTableEquiv).bind
        (fun pureProfile =>
          G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              (pureProfile.toBehavioral G.observed))
            current fuel)) := by
  let e :
      ↥(Finset.univ :
        Finset G.observed.DecisionKey) ≃
        G.observed.DecisionKey :=
    Equiv.subtypeUnivEquiv (by simp)
  let reindex :
      ((key :
          ↥(Finset.univ :
            Finset G.observed.DecisionKey)) →
        G.observed.DecisionValue key.1) ≃
        ((key : G.observed.DecisionKey) →
          G.observed.DecisionValue key) :=
    e.piCongr fun _ => Equiv.refl _
  let restrictedLaw :=
    FiniteLaw.fintypePi
      (fun key :
        ↥(Finset.univ :
          Finset G.observed.DecisionKey) =>
        profile.decisionLaw G.observed key.1)
  let fullLaw :=
    FiniteLaw.fintypePi
      (profile.decisionLaw G.observed)
  let tree :=
    G.boundedHistoryTree
      hnoAbsent current Finset.univ
      (ObservedGame.FutureDecisionKeysAvailable.univ
        current)
      fuel
  apply FiniteLaw.Equivalent.trans
    (second :=
      restrictedLaw.bind
        (FiniteLaw.FreshQueryTree.runWithTable tree))
  · exact FiniteLaw.Equivalent.of_eq rfl
  apply FiniteLaw.Equivalent.trans
    (second :=
      (restrictedLaw.map reindex).bind
        (fun fullTable =>
          FiniteLaw.FreshQueryTree.runWithTable
            tree (reindex.symm fullTable)))
  · apply FiniteLaw.Equivalent.of_eq
    rw [FiniteLaw.bind_map]
    apply congrArg (fun continuation =>
      restrictedLaw.bind continuation)
    funext table
    change
      FiniteLaw.FreshQueryTree.runWithTable tree table =
        FiniteLaw.FreshQueryTree.runWithTable tree
          (reindex.symm (reindex table))
    rw [reindex.symm_apply_apply]
  apply FiniteLaw.Equivalent.trans
    (second :=
      fullLaw.bind
        (fun fullTable =>
          FiniteLaw.FreshQueryTree.runWithTable
            tree (reindex.symm fullTable)))
  · have hLaw :
        (restrictedLaw.map reindex).Equivalent fullLaw := by
      dsimp [restrictedLaw, fullLaw, reindex, e]
      exact
        FiniteLaw.fintypePi_reindex
          (Equiv.subtypeUnivEquiv (by simp))
          (profile.decisionLaw G.observed)
    exact hLaw.bind (fun _ => FiniteLaw.Equivalent.refl _)
  apply FiniteLaw.Equivalent.trans
    (second :=
      fullLaw.bind
        (fun fullTable =>
          G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              ((G.observed.decisionTableEquiv
                fullTable).toBehavioral G.observed))
            current fuel))
  · apply (FiniteLaw.Equivalent.refl fullLaw).bind
    intro fullTable
    apply FiniteLaw.Equivalent.of_eq
    apply G.boundedHistoryTree_runWithTable
      hnoAbsent fullTable current Finset.univ
      (ObservedGame.FutureDecisionKeysAvailable.univ current)
      (reindex.symm fullTable)
    intro key
    change
      (Equiv.refl (G.observed.DecisionValue key.1))
          (fullTable key.1) = fullTable key.1
    rfl
  · apply FiniteLaw.Equivalent.of_eq
    rw [FiniteLaw.bind_map]
    rfl

/-- Pre-sampling the complete flat decision table gives the same bounded
history law as local behavioral sampling. -/
theorem boundedHistoryTree_runPresampled
    (G : ObservedChanceGame N U)
    [Fintype G.observed.DecisionKey]
    [LinearOrder G.observed.DecisionKey]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    (hnoAbsent : G.observed.NoAbsentMindedness)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    FiniteLaw.FreshQueryTree.runPresampled
        (profile.decisionLaw G.observed)
        (G.boundedHistoryTree
          hnoAbsent current Finset.univ
          (ObservedGame.FutureDecisionKeysAvailable.univ
            current)
          fuel) |>.Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G profile)
        current fuel) := by
  exact
    (FiniteLaw.FreshQueryTree.runPresampled_eq_runOnDemand
      (profile.decisionLaw G.observed) _).trans
        (FiniteLaw.Equivalent.of_eq
          (G.boundedHistoryTree_runOnDemand
            profile hnoAbsent current Finset.univ
            (ObservedGame.FutureDecisionKeysAvailable.univ current)
            fuel))


end ExtensiveGame.ObservedChanceGame
