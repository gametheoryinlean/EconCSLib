/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization

Root-scoped law morphisms, deviation coverage, and finite Kuhn transfer.

The mathematical realization target is [Kuhn 1953, §4, Thm. 4] under finite
perfect recall. This module's bounded history/payoff-law equivalences and
Nash-transfer theorems are the constructive `FiniteLaw` implementation of
that target. They do not assert equality of arbitrary infinite path measures.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP

variable {N : Type uN} {U : Type uU}
  (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)

/-- Root-scoped conditional behavioralization preserves the semantic payoff
law of every mixed profile.

This morphism already gives exact outcome-law realization.  Two-way Nash
transfer additionally needs semantic coverage of arbitrary behavioral
deviations, proved separately from the law equality. -/
theorem mixedToBehavioralLawHomAt
    [Fintype N] [LinearOrder N]
    [∀ (i : N)
      (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (offPath : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    ∀ profile,
      (G.mixedStoppedPayoffLawFrom
        profile current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        (certificate.behavioralizeMixedProfileFrom
          G.observed current profile offPath)
        current fuel) :=
  fun profile =>
    G.mixedToBehavioral_stoppedPayoffLawFrom
      certificate profile offPath current fuel

/-- Replacing one root-scoped behavioralized component by an arbitrary
behavioral strategy has the same bounded history law as replacing the source
mixed component by that strategy's independently sampled complete table.

The statement is strengthened along every suffix of the selected root so that
the proof can recurse through stochastic execution. -/
theorem behavioralDeviationHistoryLawAlong_eq
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (offPath : G.observed.BehavioralProfile)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (fuel : ℕ) :
    let sourceDeviation :
        G.observed.MixedProfile :=
      Function.update profile who
        (h.behavioralToMixedStrategy
          who target)
    let baseBehavior :
        G.observed.BehavioralProfile :=
      h.mixedToBehavioralProfileAt
        G.observed root profile offPath
    let targetBehavior :
        G.observed.BehavioralProfile :=
      Function.update baseBehavior who target
    let realizedBehavior :
        G.observed.BehavioralProfile :=
      h.mixedToBehavioralProfileAt
        G.observed root sourceDeviation
        (Function.update offPath who target)
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          targetBehavior)
        current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          realizedBehavior)
        current fuel) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  induction fuel generalizing finish with
  | zero =>
      exact FiniteLaw.Equivalent.refl _
  | succ fuel ih =>
      let sourceDeviation :
          G.observed.MixedProfile :=
        Function.update profile who
          (h.behavioralToMixedStrategy
            who target)
      let baseBehavior :
          G.observed.BehavioralProfile :=
        h.mixedToBehavioralProfileAt
          G.observed root profile offPath
      let targetBehavior :
          G.observed.BehavioralProfile :=
        Function.update baseBehavior who target
      let realizedBehavior :
          G.observed.BehavioralProfile :=
        h.mixedToBehavioralProfileAt
          G.observed root sourceDeviation
          (Function.update offPath who target)
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      change
        (G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              targetBehavior)
            current (fuel + 1)).Equivalent
          (G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              realizedBehavior)
            current (fuel + 1))
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simpa [Arena.stochasticHistoryLawFrom,
          hterminal] using
            FiniteLaw.Equivalent.refl (FiniteLaw.pure current)
      · rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            targetBehavior)
          current fuel hterminal]
        rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            realizedBehavior)
          current fuel hterminal]
        have hpolicy :
            (BehavioralProfile.toHistoryPolicy G
                targetBehavior current hterminal).Equivalent
              (BehavioralProfile.toHistoryPolicy G
                realizedBehavior current hterminal) := by
          cases hmover :
              G.observed.base.mover current.1 with
          | none =>
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G targetBehavior current
                hterminal hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G realizedBehavior current
                hterminal hmover]
              exact FiniteLaw.Equivalent.refl _
          | some mover =>
              let hdecision :=
                G.observed.base.toArena.isDecision_of_not_isTerminal
                  current.1 hterminal
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G targetBehavior current
                hterminal mover hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G realizedBehavior current
                hterminal mover hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
              apply FiniteLaw.Equivalent.map
              by_cases hmoverWho :
                  mover = who
              · subst mover
                have hmover' :
                    G.observed.base.mover finish =
                      some who := by
                  simpa [current] using hmover
                have hnonterminal' :
                    ¬ G.observed.base.isTerminal finish := by
                  simpa [current] using hterminal
                simp only [targetBehavior,
                  realizedBehavior, sourceDeviation,
                  ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update]
                change
                  (target
                      (G.observed.representedInfoAt
                        current who hmover hdecision)).Equivalent
                    (h.recallCertificate.behavioralizeMixedFrom
                      G.observed root who
                      (h.behavioralToMixedStrategy
                        who target)
                      target
                      (G.observed.representedInfoAt
                        current who hmover hdecision))
                exact
                  (h.behavioralize_behavioralToMixed_at_append
                    G.observed root suffix who hmover' hnonterminal'
                    target).symm
              · simp [targetBehavior,
                  realizedBehavior, baseBehavior,
                  sourceDeviation,
                  ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update, hmoverWho]
                exact FiniteLaw.Equivalent.refl _
        apply hpolicy.bind
        intro action
        have ihAction :=
          ih
            (suffix := suffix.snoc action)
        simpa [sourceDeviation,
          baseBehavior, targetBehavior,
          realizedBehavior, current,
          Arena.History.append_snoc] using
            ihAction

/-- Root-scoped behavioralization of an independently sampled behavioral
profile is behaviorally indistinguishable from the original profile, even
after an arbitrary unilateral behavioral deviation.

Only the non-deviating players use the table behavioralization; their local
laws agree with the source behavioral strategies at every history reachable
from the selected root. -/
theorem behavioralTableDeviationHistoryLawAlong_eq
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (fuel : ℕ) :
    let mixedProfile :=
      h.behavioralToMixedProfile profile
    let mappedProfile :=
      h.mixedToBehavioralProfileAt
        G.observed root mixedProfile profile
    let sourceDeviation :=
      Function.update profile who target
    let mappedDeviation :=
      Function.update mappedProfile who target
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          sourceDeviation)
        current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          mappedDeviation)
        current fuel) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  induction fuel generalizing finish with
  | zero =>
      exact FiniteLaw.Equivalent.refl _
  | succ fuel ih =>
      let mixedProfile :=
        h.behavioralToMixedProfile profile
      let mappedProfile :=
        h.mixedToBehavioralProfileAt
          G.observed root mixedProfile profile
      let sourceDeviation :=
        Function.update profile who target
      let mappedDeviation :=
        Function.update mappedProfile who target
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      change
        (G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              sourceDeviation)
            current (fuel + 1)).Equivalent
          (G.observed.base.toArena.stochasticHistoryLawFrom
            (BehavioralProfile.toHistoryPolicy G
              mappedDeviation)
            current (fuel + 1))
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simpa [Arena.stochasticHistoryLawFrom,
          hterminal] using
            FiniteLaw.Equivalent.refl (FiniteLaw.pure current)
      · rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            sourceDeviation)
          current fuel hterminal]
        rw [G.observed.base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            mappedDeviation)
          current fuel hterminal]
        have hpolicy :
            (BehavioralProfile.toHistoryPolicy G
                sourceDeviation current hterminal).Equivalent
              (BehavioralProfile.toHistoryPolicy G
                mappedDeviation current hterminal) := by
          cases hmover :
              G.observed.base.mover current.1 with
          | none =>
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G sourceDeviation current
                hterminal hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G mappedDeviation current
                hterminal hmover]
              exact FiniteLaw.Equivalent.refl _
          | some mover =>
              let hdecision :=
                G.observed.base.toArena.isDecision_of_not_isTerminal
                  current.1 hterminal
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G sourceDeviation current
                hterminal mover hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G mappedDeviation current
                hterminal mover hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
              apply FiniteLaw.Equivalent.map
              by_cases hmoverWho :
                  mover = who
              · subst mover
                simp [sourceDeviation,
                  mappedDeviation]
                exact FiniteLaw.Equivalent.refl _
              · have hmover' :
                    G.observed.base.mover finish =
                      some mover := by
                  simpa [current] using hmover
                have hnonterminal' :
                    ¬ G.observed.base.isTerminal finish := by
                  simpa [current] using hterminal
                simp only [sourceDeviation,
                  mappedDeviation, mappedProfile,
                  mixedProfile,
                  ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
                  ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update, hmoverWho]
                change
                  (profile mover
                      (G.observed.representedInfoAt
                        current mover hmover hdecision)).Equivalent
                    (h.recallCertificate.behavioralizeMixedFrom
                      G.observed root mover
                      (h.behavioralToMixedStrategy
                        mover (profile mover))
                      (profile mover)
                      (G.observed.representedInfoAt
                        current mover hmover hdecision))
                exact
                  (h.behavioralize_behavioralToMixed_at_append
                    G.observed root suffix mover
                    hmover' hnonterminal'
                    (profile mover)).symm
        apply hpolicy.bind
        intro action
        have ihAction :=
          ih
            (suffix := suffix.snoc action)
        simpa [mixedProfile, mappedProfile,
          sourceDeviation, mappedDeviation,
          current, Arena.History.append_snoc]
            using ihAction

/-- Payoff-law form of table behavioralization equivalence under an arbitrary
unilateral behavioral deviation. -/
theorem behavioralTableDeviationPayoffLaw_eq
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    (fuel : ℕ) :
    (G.behavioralStoppedPayoffLawFrom
        (Function.update profile who target)
        current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        (Function.update
          (h.mixedToBehavioralProfileAt
            G.observed current
            (h.behavioralToMixedProfile
              profile)
            profile)
          who target)
        current fuel) := by
  have hhistory :=
    G.behavioralTableDeviationHistoryLawAlong_eq
      h profile current who target
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      fuel
  dsimp only at hhistory
  rw [Arena.History.append_nil] at hhistory
  exact hhistory.map G.stoppedPayoffAtHistory

/-- Exact payoff-law realization of an arbitrary unilateral behavioral
deviation by independently sampling that deviating behavioral strategy's
complete contingent table. -/
theorem behavioralDeviationPayoffLaw_eq_mixed
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (offPath : G.observed.BehavioralProfile)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    (fuel : ℕ) :
    (G.behavioralStoppedPayoffLawFrom
        (Function.update
          (h.mixedToBehavioralProfileAt
            G.observed current profile offPath)
          who target)
        current fuel).Equivalent
      (G.mixedStoppedPayoffLawFrom
        (Function.update profile who
          (h.behavioralToMixedStrategy
            who target))
        current fuel) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  let sourceDeviation :
      G.observed.MixedProfile :=
    Function.update profile who
      (h.behavioralToMixedStrategy
        who target)
  let targetBehavior :
      G.observed.BehavioralProfile :=
    Function.update
      (h.mixedToBehavioralProfileAt
        G.observed current profile offPath)
      who target
  let realizedBehavior :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current sourceDeviation
      (Function.update offPath who target)
  have hhistory :=
    G.behavioralDeviationHistoryLawAlong_eq
      h profile current offPath who target
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      fuel
  dsimp only at hhistory
  rw [Arena.History.append_nil] at hhistory
  exact
    (hhistory.map G.stoppedPayoffAtHistory).trans
      (G.mixedToBehavioral_stoppedPayoffLawFrom
        h.recallCertificate sourceDeviation
        (Function.update offPath who target)
        current fuel).symm

/-- The finite perfect-recall hypotheses give root-scoped semantic
realization, including coverage of all unilateral behavioral deviations. -/
theorem finiteKuhnMixedBehavioralRealizationAt
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (offPath : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    ∀ profile : G.observed.MixedProfile,
      (G.behavioralStoppedPayoffLawFrom
        (h.mixedToBehavioralProfileAt
          G.observed current profile offPath)
        current fuel).Equivalent
        (G.mixedStoppedPayoffLawFrom profile current fuel) ∧
      ∀ (i : N) (target : G.observed.BehavioralStrategy i),
        ∃ source : G.observed.MixedStrategy i,
          (G.behavioralStoppedPayoffLawFrom
            (Function.update
              (h.mixedToBehavioralProfileAt
                G.observed current profile offPath)
              i target)
            current fuel).Equivalent
          (G.mixedStoppedPayoffLawFrom
            (Function.update profile i source)
            current fuel) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  intro profile
  constructor
  · exact (G.mixedToBehavioral_stoppedPayoffLawFrom
      h.recallCertificate profile offPath current fuel).symm
  · intro i target
    exact ⟨h.behavioralToMixedStrategy i target,
      G.behavioralDeviationPayoffLaw_eq_mixed
        h profile current offPath i target fuel⟩

/-- The behavioral-to-mixed continuation morphism has exact rootwise semantic
coverage of every arbitrary mixed deviation under finite perfect recall.

The realizing behavioral deviation is the root-scoped conditional
behavioralization of the target mixed plan.  Non-deviating independently
sampled behavioral tables are replaced by their original behavioral
strategies using the reachable-history equivalence above. -/
theorem behavioralToMixedContinuationHom_outcomeDeviationCompleteAt
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    ∀ current, roots.IsRoot current →
      ∀ (i : N) (targetMixed : G.observed.MixedStrategy i),
        ∃ sourceBehavior : G.observed.BehavioralStrategy i,
          (G.mixedStoppedPayoffLawFrom
            (Function.update
              (h.behavioralToMixedProfile profile)
              i targetMixed)
            current fuel).Equivalent
          (G.behavioralStoppedPayoffLawFrom
            (Function.update profile i sourceBehavior)
            current fuel) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  intro current _ i targetMixed
  let mixedDeviation :
      G.observed.MixedProfile :=
    Function.update
      (h.behavioralToMixedProfile profile)
      i targetMixed
  let sourceBehavior :
      G.observed.BehavioralStrategy i :=
    h.mixedToBehavioralProfileAt
      G.observed current mixedDeviation profile i
  refine ⟨sourceBehavior, ?_⟩
  let mappedBase :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current
      (h.behavioralToMixedProfile profile)
      profile
  let mappedDeviation :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current mixedDeviation profile
  have hmapped :
      mappedDeviation =
        Function.update mappedBase
          i sourceBehavior := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [mappedDeviation,
        mixedDeviation, sourceBehavior,
        ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
        Function.update]
    · simp [mappedDeviation, mappedBase,
        mixedDeviation,
        ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
        Function.update, hji]
  apply FiniteLaw.Equivalent.trans
    (second := G.behavioralStoppedPayoffLawFrom
      mappedDeviation current fuel)
  · exact G.mixedToBehavioral_stoppedPayoffLawFrom
      h.recallCertificate mixedDeviation profile current fuel
  apply FiniteLaw.Equivalent.trans
    (second := G.behavioralStoppedPayoffLawFrom
      (Function.update mappedBase i sourceBehavior)
      current fuel)
  · exact FiniteLaw.Equivalent.of_eq (congrArg
      (fun mapped => G.behavioralStoppedPayoffLawFrom
        mapped current fuel) hmapped)
  exact
    (G.behavioralTableDeviationPayoffLaw_eq
      h profile current i sourceBehavior fuel).symm

/-- Full bounded Kuhn designated-continuation theorem: under finite perfect
recall, a behavioral profile is Nash on every presentation-designated
continuation exactly when its independently sampled complete pure-plan
profile has the corresponding mixed-strategy property.

This discharges the semantic-deviation premise of the earlier conditional Nash on presentation-designated continuations
bridge; it does not claim a false root-independent strategy-space
isomorphism. -/
theorem isBehavioralNashOnRootsAtFuel_iff_mixed
    [Fintype N] [LinearOrder N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnRootsAtFuel
        roots utility profile fuel ↔
      G.IsMixedNashOnRootsAtFuel
        roots utility
        (h.behavioralToMixedProfile profile)
        fuel := by
  exact
    G.isBehavioralNashOnRootsAtFuel_iff_mixed_of_deviationComplete
      h roots utility hutility profile fuel
      (G.behavioralToMixedContinuationHom_outcomeDeviationCompleteAt
        h roots profile fuel)

/-- Constructive root-scoped Kuhn realization gives two-way Nash transfer for
every utility functional on the complete bounded payoff law. -/
theorem finiteKuhn_isNash_iff
    [Fintype N] [LinearOrder N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedLawGameForm current fuel).IsNash
        utility profile ↔
      (G.behavioralLawGameForm
        current fuel).IsNash
          utility
      (h.mixedToBehavioralProfileAt
            G.observed current profile offPath) := by
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq
        (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  let realization : G.MixedBehavioralRealizationAt
      current fuel := {
    behavioralize := fun i strategy =>
      h.recallCertificate.behavioralizeMixedFrom
        G.observed current i strategy (offPath i)
    map_payoffLaw := by
      intro sourceProfile
      exact (G.mixedToBehavioral_stoppedPayoffLawFrom
        h.recallCertificate sourceProfile offPath current fuel).symm
    realize_deviation := by
      intro sourceProfile i target
      exact ⟨h.behavioralToMixedStrategy i target,
        G.behavioralDeviationPayoffLaw_eq_mixed
          h sourceProfile current offPath i target fuel⟩ }
  simpa [realization,
    MixedBehavioralRealizationAt.mapProfile,
    ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
    ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom] using
      realization.isNash_iff utility hutility profile

/-- The finite Kuhn package specializes finite-law bounded-history
realization over arbitrary information carriers by supplying its recall certificate.

Finite information is not consumed by the law equality itself; it is needed
later for behavioral-deviation coverage and hence the two-way Nash theorem
above. -/
theorem finiteKuhn_boundedHistoryLaw_specialization
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (offPath : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    (G.mixedStoppedHistoryLawFrom profile current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G
          (h.mixedToBehavioralProfileAt
            G.observed current profile offPath))
        current fuel) :=
  by
    letI (i : N) (information : G.observed.RepresentedInfo i) :
        DecidableEq
          (G.observed.InfoAction i information.1) :=
      (h.finiteDecisionPresentation i).2 information
    simpa [ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt] using
      G.finiteLawMixedToBehavioral_boundedHistoryLaw
        h.recallCertificate profile offPath current fuel

end ExtensiveGame.ObservedChanceGame
