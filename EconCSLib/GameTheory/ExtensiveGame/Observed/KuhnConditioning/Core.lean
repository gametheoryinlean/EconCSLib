/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core

Mixed-profile posterior products and perfect-recall conditioning identities.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

namespace MixedProfile

/-- Update every player's mixed plan to the sequential posterior induced by
the supplied own-decision sequence.  Each component remains partial because a
zero-mass decision history has no posterior. -/
def posteriorAfterDecisions
    [∀ (i : N) (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (profile : G.MixedProfile)
    (decisions : G.PersonalDecisionHistories) :
    (i : N) → Option (G.MixedStrategy i) :=
  fun i =>
    (profile i).posteriorAfterDecisions
      G (decisions i)

@[simp]
theorem posteriorAfterDecisions_apply
    [∀ (i : N) (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (profile : G.MixedProfile)
    (decisions : G.PersonalDecisionHistories)
    (i : N) :
    profile.posteriorAfterDecisions
        G decisions i =
      (profile i).posteriorAfterDecisions
        G (decisions i) :=
  rfl

/-- At the continuation root, all playerwise posteriors are the original
mixed plans. -/
@[simp]
theorem posteriorAfterDecisions_empty
    [∀ (i : N) (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (profile : G.MixedProfile) :
    profile.posteriorAfterDecisions
        G (fun _ => []) =
      fun i => some (profile i) := by
  funext i
  rfl

/-- After a represented player action, the continuation-relative posterior
profile updates exactly the acting player's plan law on the observed abstract
action fiber. -/
theorem posteriorAfterDecisions_relative_snoc_of_mover
    [DecidableEq N]
    [∀ (j : N) (information : G.RepresentedInfo j),
      DecidableEq (G.InfoAction j information.1)]
    (profile : G.MixedProfile)
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (i : N)
    (hmover :
      G.base.mover state = some i)
    (hdecision :
      G.base.toArena.IsDecision state)
    (abstractAction :
      G.InfoAction i
        (G.infoAt
          ⟨state, root.2.append suffix⟩
          i hmover hdecision)) :
    ∀ j,
    (profile.posteriorAfterDecisions
        G
        (G.relativeOwnDecisionHistories
          root
          ⟨G.base.next state
              (G.actionEquiv
                ⟨state, root.2.append suffix⟩
                i hmover hdecision abstractAction),
            root.2.append
              (suffix.snoc
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hdecision abstractAction))⟩) j) =
      Function.update
          (profile.posteriorAfterDecisions
            G
            (G.relativeOwnDecisionHistories
              root
              ⟨state, root.2.append suffix⟩))
          i
          ((profile i).posteriorAfterDecisions
              G
              (G.relativeOwnDecisionHistories
                root
                ⟨state, root.2.append suffix⟩
                i) |>.bind (fun posterior =>
              posterior.conditionOnFiber
                (fun pureStrategy =>
                  pureStrategy
                    (G.representedInfoAt
                      ⟨state, root.2.append suffix⟩
                      i hmover hdecision))
                abstractAction))
        j := by
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update]
    change
      (profile i).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨G.base.next state
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hdecision abstractAction),
              root.2.append
                (suffix.snoc
                  (G.actionEquiv
                    ⟨state, root.2.append suffix⟩
                    i hmover hdecision abstractAction))⟩
            i) =
        ((profile i).posteriorAfterDecisions
            G
            (G.relativeOwnDecisionHistories
              root
              ⟨state, root.2.append suffix⟩
              i) |>.bind (fun posterior =>
          posterior.conditionOnFiber
            (fun pureStrategy =>
              pureStrategy
                (G.representedInfoAt
                  ⟨state, root.2.append suffix⟩
                  i hmover hdecision))
            abstractAction))
    rw [G.relativeOwnDecisionHistories_snoc_of_mover
      root suffix
      (G.actionEquiv
        ⟨state, root.2.append suffix⟩
        i hmover hdecision abstractAction)
      i hmover]
    rw [G.personalDecisionAt_actionEquiv
      i ⟨state, root.2.append suffix⟩
      hmover hdecision abstractAction]
    exact
      MixedStrategy.posteriorAfterDecisions_append_singleton
        G (profile i)
        (G.relativeOwnDecisionHistories root
          ⟨state, root.2.append suffix⟩ i)
        ⟨G.representedInfoAt ⟨state, root.2.append suffix⟩
            i hmover hdecision,
          abstractAction⟩
  · simp only [Function.update, hji]
    change
      (profile j).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨G.base.next state
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hdecision abstractAction),
              root.2.append
                (suffix.snoc
                  (G.actionEquiv
                    ⟨state, root.2.append suffix⟩
                    i hmover hdecision abstractAction))⟩
            j) =
        (profile j).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨state, root.2.append suffix⟩
            j)
    apply congrArg
      ((profile j).posteriorAfterDecisions G)
    apply G.relativeOwnDecisionHistories_snoc_of_not_mover
    intro hwrong
    exact hji (Option.some.inj (hwrong.symm.trans hmover))

end MixedProfile

namespace RecallCertificate

variable [DecidableEq N]

/-- Personal decisions remembered at an information state after removing the
part that occurred before `current`.

For information states not reachable from `current`, `drop` still makes this a
total definition.  Those values do not affect execution from the selected
root. -/
def rememberedFrom
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (information : G.RepresentedInfo i) :
    List (G.PersonalDecision i) :=
  (certificate.remembered i information).drop
    (G.ownDecisionHistory i current).length

/-- At a player-controlled continuation root, no continuation-local decision
has yet occurred. -/
@[simp]
theorem rememberedFrom_infoAt_current
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover current.1 = some i)
    (hdecision :
      G.base.toArena.IsDecision current.1) :
    certificate.rememberedFrom
        G current i
        (G.representedInfoAt current i hmover hdecision) =
      [] := by
  simp [rememberedFrom,
    certificate.remembered_infoAt _ _ _ hdecision]

/-- At a represented decision reachable from `current`, the relative
remembered sequence is the suffix of the extracted own-decision history after
the root prefix. -/
theorem rememberedFrom_infoAt_append
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hdecision :
      G.base.toArena.IsDecision finish) :
    certificate.rememberedFrom
        G current i
        (G.representedInfoAt
          ⟨finish, current.2.append suffix⟩
          i hmover hdecision) =
      (G.ownDecisionHistory i
        ⟨finish, current.2.append suffix⟩).drop
          (G.ownDecisionHistory i current).length := by
  rw [rememberedFrom,
    certificate.remembered_infoAt _ _ _ hdecision]

/-- At a reachable continuation decision, the pre-root personal history
followed by the relative remembered suffix reconstructs the complete personal
history. -/
theorem ownDecisionHistory_append_rememberedFrom_infoAt
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hdecision :
      G.base.toArena.IsDecision finish) :
    G.ownDecisionHistory i current ++
        certificate.rememberedFrom
          G current i
          (G.representedInfoAt
            ⟨finish, current.2.append suffix⟩
            i hmover hdecision) =
      G.ownDecisionHistory i
        ⟨finish, current.2.append suffix⟩ := by
  rw [certificate.rememberedFrom_infoAt_append
    G current suffix i hmover hdecision]
  exact
    (List.prefix_append_drop
      (G.ownDecisionHistory_prefix_append
        i current.2 suffix)).symm

/-- Behavioralize one arbitrary mixed plan from a selected continuation root
by conditioning only on the player's own decisions made since that root.
When the remembered sequence has zero mass, use exactly the behavioral
assessment supplied by the caller. -/
def behavioralizeMixedFrom
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    [∀ (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (strategy : G.MixedStrategy i)
    (offPath : G.BehavioralStrategy i) :
    G.BehavioralStrategy i :=
  fun information =>
    (strategy.sequentialConditionalActionLaw
        G
        (certificate.rememberedFrom
          G current i information)
        information).getD (offPath information)

/-- At a player-controlled continuation root, root-scoped
behavioralization uses exactly the unconditional mixed action marginal. -/
theorem behavioralizeMixedFrom_at_root
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    [∀ (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (hmover :
      G.base.mover current.1 = some i)
    (hdecision :
      G.base.toArena.IsDecision current.1)
    (strategy : G.MixedStrategy i)
    (offPath : G.BehavioralStrategy i) :
    certificate.behavioralizeMixedFrom
        G current i strategy offPath
        (G.representedInfoAt current i hmover hdecision) =
      strategy.map
        (fun pureStrategy =>
          pureStrategy
            (G.representedInfoAt current i hmover hdecision)) := by
  unfold behavioralizeMixedFrom
  rw [certificate.rememberedFrom_infoAt_current
    G current i hmover hdecision]
  simp [MixedStrategy.sequentialConditionalActionLaw,
    MixedStrategy.posteriorAfterDecisions]

/-- At a represented continuation decision, root-scoped behavioralization is
the mixed action law conditioned on exactly the own-decision suffix accumulated
since the selected root. -/
theorem behavioralizeMixedFrom_at_append
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    [∀ (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (hmover :
      G.base.mover finish = some i)
    (hdecision :
      G.base.toArena.IsDecision finish)
    (strategy : G.MixedStrategy i)
    (offPath : G.BehavioralStrategy i) :
    certificate.behavioralizeMixedFrom
        G current i strategy offPath
        (G.representedInfoAt
          ⟨finish, current.2.append suffix⟩
          i hmover hdecision) =
      (strategy.sequentialConditionalActionLaw
          G
          ((G.ownDecisionHistory i
            ⟨finish, current.2.append suffix⟩).drop
              (G.ownDecisionHistory i current).length)
          (G.representedInfoAt
            ⟨finish, current.2.append suffix⟩
            i hmover hdecision)).getD
        (offPath
          (G.representedInfoAt
            ⟨finish, current.2.append suffix⟩
            i hmover hdecision)) := by
  unfold behavioralizeMixedFrom
  rw [certificate.rememberedFrom_infoAt_append
    G current suffix i hmover hdecision]

/-- The concrete root action law of root-scoped behavioralization is exactly
the concrete action marginal of the source mixed plan. -/
theorem behavioralizeMixedFrom_actionLawAt_root
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    [∀ (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (hmover :
      G.base.mover current.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal current.1)
    (strategy : G.MixedStrategy i)
    (offPath : G.BehavioralStrategy i) :
    (certificate.behavioralizeMixedFrom
        G current i strategy offPath).actionLawAt
          G current hmover hnonterminal =
      strategy.map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G current hmover
              (G.base.toArena.isDecision_of_not_isTerminal
                current.1 hnonterminal)) := by
  let hdecision :=
    G.base.toArena.isDecision_of_not_isTerminal
      current.1 hnonterminal
  unfold BehavioralStrategy.actionLawAt
    ControlledObservedGame.BehavioralStrategy.actionLawAt
  dsimp only
  rw [certificate.behavioralizeMixedFrom_at_root
    G current i hmover hdecision strategy offPath]
  simpa [PureStrategy.actionAt,
    Function.comp_def] using
      FiniteLaw.map_comp
        (fun pureStrategy =>
          pureStrategy
            (G.representedInfoAt current i hmover hdecision))
        strategy
        (G.actionEquiv current i hmover hdecision)

/-- Behavioralize every component of a mixed profile from the same
continuation root, using the caller's profile only at zero-mass histories. -/
def behavioralizeMixedProfileFrom
    [∀ (i : N) (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile)
    (offPath : G.BehavioralProfile) :
    G.BehavioralProfile :=
  fun i =>
    certificate.behavioralizeMixedFrom
      G current i (profile i) (offPath i)

@[simp]
theorem behavioralizeMixedProfileFrom_apply
    [∀ (i : N) (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile)
    (offPath : G.BehavioralProfile)
    (i : N) :
    certificate.behavioralizeMixedProfileFrom
        G current profile offPath i =
      certificate.behavioralizeMixedFrom
        G current i (profile i) (offPath i) :=
  rfl

end RecallCertificate

namespace FiniteKuhnHypotheses

variable [DecidableEq N]

/-- Root-scoped conditional behavioralization from the certificate stored in
the finite Kuhn hypotheses, with an explicit caller-supplied off-path
assessment. -/
def mixedToBehavioralProfileAt
    (h : G.FiniteKuhnHypotheses)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile)
    (offPath : G.BehavioralProfile) :
    G.BehavioralProfile :=
  letI (i : N) (information : G.RepresentedInfo i) :
      DecidableEq (G.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  h.recallCertificate.behavioralizeMixedProfileFrom
    G current profile offPath

/-- At every decision reachable from the selected continuation root,
root-scoped behavioralization of an independently sampled behavioral table
recovers the source behavioral action law exactly. -/
theorem behavioralize_behavioralToMixed_at_append
    (h : G.FiniteKuhnHypotheses)
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History root.1 finish)
    (i : N)
    [∀ (information : G.RepresentedInfo i),
      DecidableEq (G.InfoAction i information.1)]
    (hmover :
      G.base.mover finish = some i)
    (hnonterminal :
      ¬ G.base.isTerminal finish)
    (strategy : G.BehavioralStrategy i) :
    (h.recallCertificate.behavioralizeMixedFrom
        G root i
        (h.behavioralToMixedStrategy
          i strategy)
        strategy
        (G.representedInfoAt
          ⟨finish, root.2.append suffix⟩
          i hmover
            (G.base.toArena.isDecision_of_not_isTerminal
              finish hnonterminal))).Equivalent
      (strategy
        (G.representedInfoAt
          ⟨finish, root.2.append suffix⟩
          i hmover
            (G.base.toArena.isDecision_of_not_isTerminal
              finish hnonterminal))) := by
  classical
  let hdecision :=
    G.base.toArena.isDecision_of_not_isTerminal
      finish hnonterminal
  let presentation := (h.finiteDecisionPresentation i).1
  letI : Fintype (G.RepresentedInfo i) :=
    Fintype.ofEquiv (Fin presentation.1) presentation.2.symm
  letI : LinearOrder (G.RepresentedInfo i) :=
    LinearOrder.lift' presentation.2 presentation.2.injective
  rw [h.recallCertificate.behavioralizeMixedFrom_at_append
    G root suffix i hmover hdecision
    (h.behavioralToMixedStrategy i strategy) strategy]
  unfold MixedStrategy.sequentialConditionalActionLaw
  let decisions :=
    G.relativeOwnDecisionHistories
      root ⟨finish, root.2.append suffix⟩ i
  let information :=
    G.representedInfoAt
      ⟨finish, root.2.append suffix⟩
      i hmover hdecision
  change
    (((h.behavioralToMixedStrategy i strategy).posteriorAfterDecisions
          G decisions).map
        (fun posterior =>
          posterior.map fun pureStrategy =>
            pureStrategy information)).getD
      (strategy information) |>.Equivalent
        (strategy information)
  cases hposterior :
      ((h.behavioralToMixedStrategy i strategy).posteriorAfterDecisions
        G decisions) with
  | none => exact FiniteLaw.Equivalent.refl _
  | some posterior =>
      simp only [Option.map_some, Option.getD_some]
      apply
        strategy.toMixed_posteriorAfterDecisions_actionMarginal
          G decisions information posterior
      · simpa [FiniteKuhnHypotheses.behavioralToMixedStrategy] using
          hposterior
      · intro decision hmem
        exact
          HasNoAbsentMindedness.info_ne_of_mem_relativeOwnDecisionHistories
            (G := G) (h.noAbsentMindedness i) root
            ⟨finish, root.2.append suffix⟩
            hmover hnonterminal decision hmem

end FiniteKuhnHypotheses

end ExtensiveGame.ObservedGame
