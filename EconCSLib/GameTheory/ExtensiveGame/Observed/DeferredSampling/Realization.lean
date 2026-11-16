/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization

Behavioral-to-mixed history, payoff, continuation, and Nash on presentation-designated continuations transfer.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP

variable {N : Type uN} {U : Type uU}

/-- Under finite represented information and no absent-mindedness, independently sampling
a complete pure plan from a behavioral profile gives exactly the same bounded
complete-history law as sampling locally during play. -/
theorem behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G profile)
        current fuel) := by
  letI (i : N) : Fintype (G.observed.RepresentedInfo i) :=
    let presentation := (h.finiteDecisionPresentation i).1
    Fintype.ofEquiv (Fin presentation.1) presentation.2.symm
  letI (i : N) : LinearOrder (G.observed.RepresentedInfo i) :=
    let presentation := (h.finiteDecisionPresentation i).1
    LinearOrder.lift' presentation.2 presentation.2.injective
  letI (i : N) (information : G.observed.RepresentedInfo i) :
      DecidableEq (G.observed.InfoAction i information.1) :=
    (h.finiteDecisionPresentation i).2 information
  letI : Fintype G.observed.DecisionKey :=
    inferInstance
  letI : LinearOrder G.observed.DecisionKey :=
    LinearOrder.lift' toLex toLex.injective
  let hnoAbsent :=
    h.noAbsentMindedness
  let tree :=
    G.boundedHistoryTree
      hnoAbsent current Finset.univ
      (ObservedGame.FutureDecisionKeysAvailable.univ
        current)
      fuel
  let continuation := fun pureProfile : G.observed.PureProfile =>
    G.observed.base.toArena.stochasticHistoryLawFrom
      (BehavioralProfile.toHistoryPolicy G
        (pureProfile.toBehavioral G.observed))
      current fuel
  have htable :
      (((FiniteLaw.fintypePi
          (profile.decisionLaw G.observed)).map
            G.observed.decisionTableEquiv).bind continuation).Equivalent
        (((h.behavioralToMixedProfile profile).pureProfileLaw
          G.observed).bind continuation) :=
    (h.map_fintypePi_decisionLaw profile).bind
      (fun _ => FiniteLaw.Equivalent.refl _)
  have hpresampled :=
    G.boundedHistoryTree_runPresampled_eq_flatMixed
      profile hnoAbsent current fuel
  exact
    htable.symm.trans
      (hpresampled.symm.trans
        (G.boundedHistoryTree_runPresampled
          profile hnoAbsent current fuel))

/-- Compatibility wrapper under the stronger traditional finite Kuhn
hypotheses. -/
theorem behavioralToMixed_stoppedHistoryLawFrom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).Equivalent
      (G.observed.base.toArena.stochasticHistoryLawFrom
        (BehavioralProfile.toHistoryPolicy G profile)
        current fuel) := by
  let hweak :=
    h.toFiniteNoAbsentMindednessHypotheses
  simpa [hweak,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.toFiniteNoAbsentMindednessHypotheses] using
      G.behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
        hweak profile current fuel

/-- Behavioral-to-mixed conversion preserves the complete bounded optional
payoff law at every continuation root under finite represented information and no
absent-mindedness. -/
theorem behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        profile current fuel) := by
  apply FiniteLaw.Equivalent.trans
    (second :=
      (G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).map G.stoppedPayoffAtHistory)
  · exact FiniteLaw.Equivalent.of_eq
      (G.mixedStoppedPayoffLawFrom_eq_map_history
        (h.behavioralToMixedProfile profile) current fuel)
  exact
    (G.behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
      h profile current fuel).map G.stoppedPayoffAtHistory

/-- Compatibility wrapper for payoff-law preservation under the stronger
traditional finite Kuhn hypotheses. -/
theorem behavioralToMixed_stoppedPayoffLawFrom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).Equivalent
      (G.behavioralStoppedPayoffLawFrom
        profile current fuel) := by
  let hweak :=
    h.toFiniteNoAbsentMindednessHypotheses
  simpa [hweak,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.toFiniteNoAbsentMindednessHypotheses] using
      G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
        hweak profile current fuel

/-- Finite, non-absent-minded behavioral strategies and their independently
pre-sampled mixed plans have equivalent payoff laws at every declared root. -/
theorem behavioralToMixedContinuationHom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ∀ current, roots.IsRoot current → ∀ profile,
      (G.behavioralStoppedPayoffLawFrom
        profile current fuel).Equivalent
      (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile) current fuel) := by
  intro current _ profile
  exact
    (G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
      h profile current fuel).symm

/-- The semantic behavioral-to-mixed realization uses the identity root map. -/
theorem behavioralToMixedContinuationHom_of_noAbsentMindedness_declaredRootSurjective
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (_h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (_fuel : ℕ) :
    ∀ targetRoot, roots.IsRoot targetRoot →
      ∃ sourceRoot, roots.IsRoot sourceRoot ∧ sourceRoot = targetRoot := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, htargetRoot, rfl⟩

/-- A utility that respects finite-law equivalence agrees on behavioral play
and its independently pre-sampled mixed realization. -/
theorem behavioralToMixedContinuationHom_of_noAbsentMindedness_utilityCompatible
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    {V : Type*}
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i) :
    ∀ current, roots.IsRoot current → ∀ profile i,
      utility (G.behavioralStoppedPayoffLawFrom
        profile current fuel) i =
      utility (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile) current fuel) i := by
  intro current hroot profile i
  exact hutility
    (G.behavioralToMixedContinuationHom_of_noAbsentMindedness
      h roots fuel current hroot profile) i

/-- Mixed bounded Nash reflects to behavioral bounded Nash for every utility
that respects semantic equality of finite laws. -/
theorem isBehavioralNashOnRootsAtFuel_of_behavioralToMixed_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hmixed : G.IsMixedNashOnRootsAtFuel roots utility
      (h.behavioralToMixedProfile profile) fuel) :
    G.IsBehavioralNashOnRootsAtFuel roots utility profile fuel := by
  intro current hroot i deviation
  have hupdate :
      h.behavioralToMixedProfile
          (Function.update profile i deviation) =
        Function.update (h.behavioralToMixedProfile profile) i
          (h.behavioralToMixedStrategy i deviation) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
        ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
        ObservedGame.FiniteInformationHypotheses.behavioralToMixedProfile]
    · simp [ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
        ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
        ObservedGame.FiniteInformationHypotheses.behavioralToMixedProfile,
        hji]
  have hmixedDeviation :=
    hmixed current hroot i (h.behavioralToMixedStrategy i deviation)
  change
    utility (G.mixedStoppedPayoffLawFrom
      (Function.update (h.behavioralToMixedProfile profile) i
        (h.behavioralToMixedStrategy i deviation)) current fuel) i ≤
    utility (G.mixedStoppedPayoffLawFrom
      (h.behavioralToMixedProfile profile) current fuel) i at hmixedDeviation
  rw [← hupdate] at hmixedDeviation
  have hdeviationLaw :=
    G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
      h (Function.update profile i deviation) current fuel
  have hprofileLaw :=
    G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
      h profile current fuel
  calc
    utility (G.behavioralStoppedPayoffLawFrom
        (Function.update profile i deviation) current fuel) i =
        utility (G.mixedStoppedPayoffLawFrom
          (h.behavioralToMixedProfile
            (Function.update profile i deviation)) current fuel) i :=
      (hutility hdeviationLaw i).symm
    _ ≤ utility (G.mixedStoppedPayoffLawFrom
          (h.behavioralToMixedProfile profile) current fuel) i :=
      hmixedDeviation
    _ = utility (G.behavioralStoppedPayoffLawFrom
          profile current fuel) i :=
      hutility hprofileLaw i

/-- Perfect-recall compatibility wrapper for semantic continuation
realization. -/
theorem behavioralToMixedContinuationHom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ∀ current, roots.IsRoot current → ∀ profile,
      (G.behavioralStoppedPayoffLawFrom
        profile current fuel).Equivalent
      (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile) current fuel) :=
  G.behavioralToMixedContinuationHom_of_noAbsentMindedness
    h.toFiniteNoAbsentMindednessHypotheses roots fuel

/-- The perfect-recall semantic realization uses the identity root map. -/
theorem behavioralToMixedContinuationHom_declaredRootSurjective
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ∀ targetRoot, roots.IsRoot targetRoot →
      ∃ sourceRoot, roots.IsRoot sourceRoot ∧ sourceRoot = targetRoot :=
  G.behavioralToMixedContinuationHom_of_noAbsentMindedness_declaredRootSurjective
    h.toFiniteNoAbsentMindednessHypotheses roots fuel

/-- Perfect-recall compatibility wrapper for equivalence-respecting utility
compatibility. -/
theorem behavioralToMixedContinuationHom_utilityCompatible
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    {V : Type*}
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i) :
    ∀ current, roots.IsRoot current → ∀ profile i,
      utility (G.behavioralStoppedPayoffLawFrom
        profile current fuel) i =
      utility (G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile) current fuel) i :=
  G.behavioralToMixedContinuationHom_of_noAbsentMindedness_utilityCompatible
    h.toFiniteNoAbsentMindednessHypotheses roots fuel utility hutility

/-- Perfect-recall compatibility wrapper for one-way Nash reflection. -/
theorem isBehavioralNashOnRootsAtFuel_of_behavioralToMixed
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hmixed : G.IsMixedNashOnRootsAtFuel roots utility
      (h.behavioralToMixedProfile profile) fuel) :
    G.IsBehavioralNashOnRootsAtFuel roots utility profile fuel :=
  G.isBehavioralNashOnRootsAtFuel_of_behavioralToMixed_of_noAbsentMindedness
    h.toFiniteNoAbsentMindednessHypotheses roots utility hutility
      profile fuel hmixed

/-- Two-way bounded Nash transfer follows from rootwise semantic coverage of
arbitrary mixed deviations and an equivalence-respecting utility. -/
theorem isBehavioralNashOnRootsAtFuel_iff_mixed_of_deviationComplete
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [LinearOrder N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility : FiniteLaw (Option (N → U)) → N → V)
    (hutility : ∀ {left right}, left.Equivalent right →
      ∀ i, utility left i = utility right i)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hdeviation : ∀ current, roots.IsRoot current →
      ∀ (i : N) (targetStrategy : G.observed.MixedStrategy i),
        ∃ sourceStrategy : G.observed.BehavioralStrategy i,
          (G.mixedStoppedPayoffLawFrom
            (Function.update (h.behavioralToMixedProfile profile)
              i targetStrategy) current fuel).Equivalent
          (G.behavioralStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel)) :
    G.IsBehavioralNashOnRootsAtFuel roots utility profile fuel ↔
      G.IsMixedNashOnRootsAtFuel roots utility
        (h.behavioralToMixedProfile profile) fuel := by
  constructor
  · intro hbehavior current hroot i targetStrategy
    obtain ⟨sourceStrategy, htarget⟩ :=
      hdeviation current hroot i targetStrategy
    have hsource := hbehavior current hroot i sourceStrategy
    have hprofile :=
      G.behavioralToMixed_stoppedPayoffLawFrom
        h profile current fuel
    calc
      utility (G.mixedStoppedPayoffLawFrom
          (Function.update (h.behavioralToMixedProfile profile)
            i targetStrategy) current fuel) i =
          utility (G.behavioralStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy) current fuel) i :=
        hutility htarget i
      _ ≤ utility (G.behavioralStoppedPayoffLawFrom
            profile current fuel) i := hsource
      _ = utility (G.mixedStoppedPayoffLawFrom
            (h.behavioralToMixedProfile profile) current fuel) i :=
        (hutility hprofile i).symm
  · exact G.isBehavioralNashOnRootsAtFuel_of_behavioralToMixed
      h roots utility hutility profile fuel

end ExtensiveGame.ObservedChanceGame
