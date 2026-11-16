/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.SemanticMode
import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective

/-!
# Complete-history-law equivalence for observed EFGs

This module makes the strongest currently executable semantic comparison the
primary one.  Bounded execution first produces a law on complete,
occurrence-sensitive histories.  Terminal-history, outcome, payoff, and
law-utility comparisons are then pushforwards of that law.

The API deliberately calls the one-way objects `Realization`, not `Iso`.
`CompleteHistoryLawRealization` maps every source strategy and therefore every
source unilateral deviation.  The separate `TargetDeviationsCoveredAt`
predicate records the additional reverse semantic coverage needed for
two-way equilibrium transfer.

The concrete models below are discrete: chance and strategic randomization
use `FiniteLaw`.  `StrategicMode.analyticGeneral` is only a classification tag for
future measurable semantics; no analytic strategy carrier is constructed or
claimed here.

## Main definitions

* `StrategicMode` and `ChanceSemantics`.
* `BoundedCompleteHistorySemantics`.
* `CompleteHistoryLawEquivalentAt`.
* `TerminalHistoryLawEquivalentAt`.
* `OutcomeLawEquivalentAt` and `PayoffLawEquivalentAt`.
* `CompleteHistoryLawRealization`.
* `CompleteHistoryLawRealization.TargetDeviationsCoveredAt`.

## Realization results

* finite no-absent-minded behavioral play is realized by independently
  sampled mixed contingent plans;
* finite perfect-recall mixed play is realized rootwise by conditional
  behavioral play;
* both results preserve terminal-history and payoff laws by pushforward.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP uStrategy uOutcome uV

variable {N : Type uN} {U : Type uU}

/-- A bounded complete-history-law evaluator for one strategy class.

The result retains complete histories rather than endpoint states, so merged
world states do not identify distinct action occurrences. -/
structure BoundedCompleteHistorySemantics
    (G : ObservedChanceGame N U) where
  /-- One strategy carrier per player. -/
  Strategy : N → Type uStrategy
  /-- Classification of the strategy carrier. -/
  strategicMode : StrategicMode
  /-- Classification of the chance semantics. -/
  chanceSemantics : ChanceSemantics
  /-- Complete bounded law from every accumulated history. -/
  historyLaw :
    (∀ i, Strategy i) →
      G.observed.base.toArena.HistoryFrom G.observed.base.init →
      ℕ →
      FiniteLaw
        (G.observed.base.toArena.HistoryFrom
          G.observed.base.init)

namespace BoundedCompleteHistorySemantics

variable {G : ObservedChanceGame N U}

/-- Complete profiles for one history-law semantics. -/
abbrev Profile (S : G.BoundedCompleteHistorySemantics) :=
  ∀ i, S.Strategy i

/-- Equality of complete occurrence-sensitive history laws at one root and
one bounded horizon. -/
def CompleteHistoryLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  (S.historyLaw source current fuel).Equivalent
    (T.historyLaw target current fuel)

/-- Equality after observing any function of the bounded complete history. -/
def OutcomeLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    (observer :
      (G.observed.base.toArena.HistoryFrom G.observed.base.init) →
        Outcome)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  ((S.historyLaw source current fuel).map observer).Equivalent
    ((T.historyLaw target current fuel).map observer)

/-- Convert one bounded history to an optional terminal history.

`none` means the horizon ended at a nonterminal history; no artificial
terminal result is introduced. -/
def terminalHistoryAt
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    Option
      (G.observed.base.toArena.TerminalHistoryFrom
        G.observed.base.init) :=
  if hterminal :
      G.observed.base.isTerminal history.1 then
    some ⟨history, hterminal⟩
  else
    none

/-- Equality of optional terminal-history laws. -/
def TerminalHistoryLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  S.OutcomeLawEquivalentAt T
    (terminalHistoryAt G) source target current fuel

/-- Equality of the existing optional terminal-payoff laws. -/
def PayoffLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  S.OutcomeLawEquivalentAt T
    G.stoppedPayoffAtHistory source target current fuel

/-- Equality under every player-indexed utility functional of the payoff law.

This includes expected utility when `utility` is expectation, but does not
hard-code linear preferences into the EFG semantics. -/
def LawUtilityEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  ∀ i,
    utility
        ((S.historyLaw source current fuel).map
          G.stoppedPayoffAtHistory) i =
      utility
        ((T.historyLaw target current fuel).map
          G.stoppedPayoffAtHistory) i

/-- Root-presentation-wide complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentOnRoots
    (S T : G.BoundedCompleteHistorySemantics)
    (roots : G.observed.RootPresentation)
    (source : S.Profile) (target : T.Profile) : Prop :=
  ∀ current, roots.IsRoot current →
    ∀ fuel, S.CompleteHistoryLawEquivalentAt T
      source target current fuel

/-- Continuation-wide complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentOnAllContinuations
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompleteHistoryLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.allHistories
      G.observed.base)
    source target

/-- Initial-root complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentInitially
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompleteHistoryLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.initialOnly
      G.observed.base)
    source target

/-- Complete-history equality implies equality of every ordinary pushforward
outcome law. -/
theorem CompleteHistoryLawEquivalentAt.mappedOutcome
    {S T : G.BoundedCompleteHistorySemantics}
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel)
    (observer :
      (G.observed.base.toArena.HistoryFrom G.observed.base.init) →
        Outcome) :
    S.OutcomeLawEquivalentAt T observer
      source target current fuel := by
  unfold OutcomeLawEquivalentAt
  exact h.map observer

/-- Complete-history equality implies optional terminal-history-law
equality. -/
theorem CompleteHistoryLawEquivalentAt.terminalHistory
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel) :
    S.TerminalHistoryLawEquivalentAt T
      source target current fuel :=
  h.mappedOutcome (terminalHistoryAt G)

/-- Complete-history equality implies optional terminal-payoff-law equality.
-/
theorem CompleteHistoryLawEquivalentAt.payoff
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel) :
    S.PayoffLawEquivalentAt T source target current fuel :=
  h.mappedOutcome G.stoppedPayoffAtHistory

/-- Payoff-law equality implies equality under any law utility, including
expected utility where defined. -/
theorem PayoffLawEquivalentAt.utility
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.PayoffLawEquivalentAt T
      source target current fuel)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i) :
    S.LawUtilityEquivalentAt T utility
      source target current fuel := by
  intro i
  exact hutility h i

end BoundedCompleteHistorySemantics

/-- Behavioral discrete finite-law complete-history semantics. -/
def behavioralCompleteHistorySemantics
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    G.BoundedCompleteHistorySemantics where
  Strategy := G.observed.BehavioralStrategy
  strategicMode := .behavioral
  chanceSemantics := .discretePMF
  historyLaw profile current fuel :=
    G.observed.base.toArena.stochasticHistoryLawFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      current fuel

/-- Mixed discrete finite-law complete-history semantics. -/
def mixedCompleteHistorySemantics
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    G.BoundedCompleteHistorySemantics where
  Strategy := G.observed.MixedStrategy
  strategicMode := .mixed
  chanceSemantics := .discretePMF
  historyLaw := G.mixedStoppedHistoryLawFrom

namespace BoundedCompleteHistorySemantics

variable {G : ObservedChanceGame N U}

/-- One-way exact realization of all source profiles by target profiles.

Because profiles are dependent products, `mapStrategy` acts componentwise and
therefore maps every source unilateral deviation while holding the opponents'
mapped strategies fixed. -/
structure CompleteHistoryLawRealization
    (S T : G.BoundedCompleteHistorySemantics) where
  /-- Componentwise strategy realization map. -/
  mapStrategy : ∀ i, S.Strategy i → T.Strategy i
  /-- Exact complete-history law for every profile, continuation, and fuel. -/
  historyLaw_eq :
    ∀ (profile : S.Profile)
      (current :
        G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (fuel : ℕ),
      S.CompleteHistoryLawEquivalentAt T profile
        (fun i => mapStrategy i (profile i)) current fuel

namespace CompleteHistoryLawRealization

variable {S T : G.BoundedCompleteHistorySemantics}

/-- Map a complete source profile componentwise. -/
def mapProfile (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile) : T.Profile :=
  fun i => R.mapStrategy i (profile i)

/-- Componentwise realization commutes with unilateral strategy replacement.
-/
theorem mapProfile_update
    [DecidableEq N]
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile) (i : N)
    (deviation : S.Strategy i) :
    R.mapProfile (Function.update profile i deviation) =
      Function.update (R.mapProfile profile) i
        (R.mapStrategy i deviation) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [mapProfile]
  · simp [mapProfile, hji]

/-- Exact law preservation for every mapped unilateral deviation.

The quantification over `profile` includes every source opponent profile.
This is source-deviation preservation, not reverse coverage of arbitrary
target deviations. -/
theorem unilateralHistoryLaw_eq
    [DecidableEq N]
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile) (i : N)
    (deviation : S.Strategy i)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    (S.historyLaw
        (Function.update profile i deviation) current fuel).Equivalent
      (T.historyLaw
        (Function.update (R.mapProfile profile) i
          (R.mapStrategy i deviation))
        current fuel) := by
  rw [← R.mapProfile_update profile i deviation]
  exact R.historyLaw_eq
    (Function.update profile i deviation) current fuel

/-- Reverse semantic coverage of arbitrary target unilateral deviations.

This extra condition, rather than a false strategy-space isomorphism claim,
is what two-way Nash transfer must consume. -/
def TargetDeviationsCoveredAt
    [DecidableEq N]
    (R : S.CompleteHistoryLawRealization T)
    (profile : S.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  ∀ (i : N) (targetDeviation : T.Strategy i),
    ∃ sourceDeviation : S.Strategy i,
      (T.historyLaw
          (Function.update (R.mapProfile profile)
            i targetDeviation)
          current fuel).Equivalent
        (T.historyLaw
          (R.mapProfile
            (Function.update profile i sourceDeviation))
          current fuel)

end CompleteHistoryLawRealization

end BoundedCompleteHistorySemantics

/-- Under finite information and no absent-mindedness, independent
pre-sampling is a complete-history-law realization of every behavioral
profile and every source unilateral deviation.

The equal action/state universe is the existing `FreshQueryTree` execution
boundary; it is not a restriction on the general observed-game carrier. -/
theorem behavioralToMixedCompleteHistoryRealization
    (G :
      ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses) :
    ∀ (profile : G.observed.BehavioralProfile)
      (current :
        G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (fuel : ℕ),
      (G.behavioralCompleteHistorySemantics.historyLaw
        profile current fuel).Equivalent
      (G.mixedCompleteHistorySemantics.historyLaw
        (h.behavioralToMixedProfile profile) current fuel) := by
  intro profile current fuel
  exact (G.behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
    h profile current fuel).symm

/-- Perfect-recall conditional behavioralization gives root-scoped complete
history-law equivalence for every arbitrary mixed profile. -/
theorem mixedToBehavioral_completeHistoryLawEquivalentAt
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    G.mixedCompleteHistorySemantics.CompleteHistoryLawEquivalentAt
      G.behavioralCompleteHistorySemantics
      profile
      (certificate.behavioralizeMixedProfileFrom
        G.observed current profile offPath)
      current fuel :=
  G.mixedToBehavioral_stoppedHistoryLawFrom
    certificate profile offPath current fuel

/-- The mixed-to-behavioral perfect-recall realization preserves optional
terminal-history laws. -/
theorem mixedToBehavioral_terminalHistoryLawEquivalentAt
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    G.mixedCompleteHistorySemantics.TerminalHistoryLawEquivalentAt
      G.behavioralCompleteHistorySemantics
      profile
      (certificate.behavioralizeMixedProfileFrom
        G.observed current profile offPath)
      current fuel :=
  (G.mixedToBehavioral_completeHistoryLawEquivalentAt
    certificate profile offPath current fuel).terminalHistory

/-- The mixed-to-behavioral perfect-recall realization preserves optional
terminal-payoff laws as a consequence of complete-history-law equality. -/
theorem mixedToBehavioral_payoffLawEquivalentAt
    (G : ObservedChanceGame N U)
    [Fintype N] [LinearOrder N]
    [∀ (i : N) (information : G.observed.RepresentedInfo i),
      DecidableEq
        (G.observed.InfoAction i information.1)]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (offPath : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    G.mixedCompleteHistorySemantics.PayoffLawEquivalentAt
      G.behavioralCompleteHistorySemantics
      profile
      (certificate.behavioralizeMixedProfileFrom
        G.observed current profile offPath)
      current fuel :=
  (G.mixedToBehavioral_completeHistoryLawEquivalentAt
    certificate profile offPath current fuel).payoff

end ExtensiveGame.ObservedChanceGame
