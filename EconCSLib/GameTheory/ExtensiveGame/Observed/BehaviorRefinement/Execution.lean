/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Core

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution

Behavioral execution, payoff-law, Nash, and bounded Nash on presentation-designated continuations transfer.
-/

namespace ExtensiveGame.ObservedChanceGame.InformationRefinement

universe uV

variable {N U : Type*}
variable {G H : ObservedChanceGame N U}

/-- The stochastic history policies induced by a coarse behavioral profile and
its fine lift commute exactly with the strict history-action equivalence. -/
theorem map_behavioralHistoryPolicy
    (r : G.InformationRefinement H)
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (hsource :
      ¬ G.observed.base.isTerminal history.1)
    (htarget :
      ¬ H.observed.base.isTerminal
        (r.observedRefinement.historyIso.stateEquiv
          history).1) :
    ((BehavioralProfile.toHistoryPolicy G profile)
        history hsource).map
          (r.observedRefinement.historyIso.actionEquiv
            history) =
      (BehavioralProfile.toHistoryPolicy H
        (r.observedRefinement.mapBehavioralProfile
          profile))
        (r.observedRefinement.historyIso.stateEquiv
          history)
        htarget := by
  cases hmover :
      G.observed.base.mover history.1 with
  | some i =>
      have htargetMover :
          H.observed.base.mover
              (r.observedRefinement.historyIso.stateEquiv
                history).1 =
            some i := by
        rw [r.observedRefinement.map_mover history]
        exact hmover
      rw [BehavioralProfile.toHistoryPolicy_of_mover
        G profile history hsource i hmover]
      rw [BehavioralProfile.toHistoryPolicy_of_mover
        H
        (r.observedRefinement.mapBehavioralProfile
          profile)
        (r.observedRefinement.historyIso.stateEquiv
          history)
        htarget i htargetMover]
      exact
        r.observedRefinement.map_behavioralActionLaw
          profile history i hmover hsource
          htargetMover htarget
  | none =>
      have hsourceChance :
          G.observed.base.isChanceState history.1 :=
        ⟨hmover, hsource⟩
      have htargetMover :
          H.observed.base.mover
              (r.observedRefinement.historyIso.stateEquiv
                history).1 =
            none := by
        rw [r.observedRefinement.map_mover history]
        exact hmover
      rw [BehavioralProfile.toHistoryPolicy_of_chance
        G profile history hsource hmover]
      rw [BehavioralProfile.toHistoryPolicy_of_chance
        H
        (r.observedRefinement.mapBehavioralProfile
          profile)
        (r.observedRefinement.historyIso.stateEquiv
          history)
        htarget htargetMover]
      exact
        r.map_chanceKernel history hsourceChance

/-- Exact naturality of bounded stochastic continuation execution under a
chance-aware information refinement. -/
theorem map_behavioralHistoryLawFrom
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    ∀ fuel,
      (G.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel).map
          r.observedRefinement.historyIso.stateEquiv =
        H.observed.base.toArena.stochasticHistoryLawFrom
          (BehavioralProfile.toHistoryPolicy H
            (r.observedRefinement.mapBehavioralProfile
              profile))
          (r.observedRefinement.historyIso.stateEquiv
            current)
          fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      exact
        FiniteLaw.pure_map
          r.observedRefinement.historyIso.stateEquiv
          current
  | succ fuel ih =>
      by_cases hsource :
          G.observed.base.isTerminal current.1
      · have htarget :
            H.observed.base.isTerminal
              (r.observedRefinement.historyIso.stateEquiv
                current).1 :=
          (r.observedRefinement.isTerminal_iff
            current).mp hsource
        rw [Arena.stochasticHistoryLawFrom_succ_of_terminal
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel hsource]
        rw [Arena.stochasticHistoryLawFrom_succ_of_terminal
          (BehavioralProfile.toHistoryPolicy H
            (r.observedRefinement.mapBehavioralProfile
              profile))
          (r.observedRefinement.historyIso.stateEquiv
            current)
          fuel htarget]
        exact
          FiniteLaw.pure_map
            r.observedRefinement.historyIso.stateEquiv
            current
      · have htarget :
            ¬ H.observed.base.isTerminal
              (r.observedRefinement.historyIso.stateEquiv
                current).1 :=
          not_congr
            (r.observedRefinement.isTerminal_iff
              current) |>.mp hsource
        rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel hsource]
        rw [Arena.stochasticHistoryLawFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy H
            (r.observedRefinement.mapBehavioralProfile
              profile))
          (r.observedRefinement.historyIso.stateEquiv
            current)
          fuel htarget]
        let sourcePolicy :=
          BehavioralProfile.toHistoryPolicy G profile
        let targetPolicy :=
          BehavioralProfile.toHistoryPolicy H
            (r.observedRefinement.mapBehavioralProfile
              profile)
        let sourceLaw :=
          sourcePolicy current hsource
        let targetContinuation :=
          fun action =>
            H.observed.base.toArena.stochasticHistoryLawFrom
                targetPolicy
                ⟨H.observed.base.next
                    (r.observedRefinement.historyIso.stateEquiv
                      current).1
                    action,
                  (r.observedRefinement.historyIso.stateEquiv
                    current).2.snoc action⟩
                fuel
        calc
          (sourceLaw.bind
              (fun action =>
                G.observed.base.toArena.stochasticHistoryLawFrom
                    sourcePolicy
                    ⟨G.observed.base.next
                        current.1 action,
                      current.2.snoc action⟩
                    fuel)).map
                r.observedRefinement.historyIso.stateEquiv =
            sourceLaw.bind
              (fun action =>
                (G.observed.base.toArena.stochasticHistoryLawFrom
                    sourcePolicy
                    ⟨G.observed.base.next
                        current.1 action,
                      current.2.snoc action⟩
                    fuel).map
                  r.observedRefinement.historyIso.stateEquiv) :=
              FiniteLaw.map_bind sourceLaw
                (fun action =>
                  G.observed.base.toArena.stochasticHistoryLawFrom
                      sourcePolicy
                      ⟨G.observed.base.next
                          current.1 action,
                        current.2.snoc action⟩
                      fuel)
                r.observedRefinement.historyIso.stateEquiv
          _ = sourceLaw.bind
              (fun action =>
                H.observed.base.toArena.stochasticHistoryLawFrom
                    targetPolicy
                    (r.observedRefinement.historyIso.stateEquiv
                        ⟨G.observed.base.next
                            current.1 action,
                          current.2.snoc action⟩)
                    fuel) := by
              apply congrArg
                (fun continuation =>
                  sourceLaw.bind continuation)
              funext action
              exact
                ih
                  ⟨G.observed.base.next
                      current.1 action,
                    current.2.snoc action⟩
          _ = sourceLaw.bind
              (targetContinuation ∘
                r.observedRefinement.historyIso.actionEquiv
                  current) := by
              apply congrArg
                (fun continuation =>
                  sourceLaw.bind continuation)
              funext action
              unfold targetContinuation
              change
                H.observed.base.toArena.stochasticHistoryLawFrom
                      targetPolicy
                      (r.observedRefinement.historyIso.stateEquiv
                          ⟨G.observed.base.next
                              current.1 action,
                            current.2.snoc action⟩)
                      fuel =
                  H.observed.base.toArena.stochasticHistoryLawFrom
                      targetPolicy
                      ⟨H.observed.base.next
                          (r.observedRefinement.historyIso.stateEquiv
                            current).1
                          (r.observedRefinement.historyIso.actionEquiv
                            current action),
                        (r.observedRefinement.historyIso.stateEquiv
                          current).2.snoc
                          (r.observedRefinement.historyIso.actionEquiv
                            current action)⟩
                      fuel
              apply congrArg
                (fun next =>
                  H.observed.base.toArena.stochasticHistoryLawFrom
                      targetPolicy next fuel)
              exact
                r.observedRefinement.historyIso.map_next
                  current action
          _ = (sourceLaw.map
                (r.observedRefinement.historyIso.actionEquiv
                  current)).bind
              targetContinuation :=
            (FiniteLaw.bind_map sourceLaw
              (r.observedRefinement.historyIso.actionEquiv
                current)
              targetContinuation).symm
          _ = (targetPolicy
                (r.observedRefinement.historyIso.stateEquiv
                  current)
                htarget).bind
              targetContinuation := by
            rw [r.map_behavioralHistoryPolicy
              profile current hsource htarget]
            rfl

/-- The optional terminal payoff represented at corresponding histories is
identical. -/
theorem map_stoppedPayoffAtHistory
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (history :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    H.stoppedPayoffAtHistory
        (r.observedRefinement.historyIso.stateEquiv
          history) =
      G.stoppedPayoffAtHistory history := by
  unfold stoppedPayoffAtHistory
  by_cases hsource :
      G.observed.base.isTerminal history.1
  · have htarget :
        H.observed.base.isTerminal
          (r.observedRefinement.historyIso.stateEquiv
            history).1 :=
      (r.observedRefinement.isTerminal_iff
        history).mp hsource
    rw [if_pos hsource, if_pos htarget,
      r.observedRefinement.map_payoff history hsource]
  · have htarget :
        ¬ H.observed.base.isTerminal
          (r.observedRefinement.historyIso.stateEquiv
            history).1 :=
      not_congr
        (r.observedRefinement.isTerminal_iff
          history) |>.mp hsource
    rw [if_neg hsource, if_neg htarget]

/-- A chance-aware information refinement preserves the entire bounded
optional-terminal-payoff law of every lifted behavioral profile. -/
theorem map_behavioralStoppedPayoffLawFrom
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    H.behavioralStoppedPayoffLawFrom
        (r.observedRefinement.mapBehavioralProfile
          profile)
        (r.observedRefinement.historyIso.stateEquiv
          current)
        fuel =
      G.behavioralStoppedPayoffLawFrom
        profile current fuel := by
  unfold behavioralStoppedPayoffLawFrom
  rw [← r.map_behavioralHistoryLawFrom
    profile current fuel]
  let sourceLaw :=
    G.observed.base.toArena.stochasticHistoryLawFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      current fuel
  calc
    (sourceLaw.map
        r.observedRefinement.historyIso.stateEquiv).map
          H.stoppedPayoffAtHistory =
      sourceLaw.map
        (H.stoppedPayoffAtHistory ∘
          r.observedRefinement.historyIso.stateEquiv) :=
        FiniteLaw.map_comp
          r.observedRefinement.historyIso.stateEquiv
          sourceLaw
          H.stoppedPayoffAtHistory
    _ = sourceLaw.map
        G.stoppedPayoffAtHistory := by
      apply congrArg
        (fun outcomeMap =>
          sourceLaw.map outcomeMap)
      funext history
      exact
        r.map_stoppedPayoffAtHistory history

/-- The bounded behavioral continuation of a chance-aware information
refinement is a game-form morphism. -/
def behavioralContinuationGameFormHom
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.behavioralContinuationGameForm
      current fuel).Hom
      (H.behavioralContinuationGameForm
        (r.observedRefinement.historyIso.stateEquiv
          current)
        fuel) where
  strategyMap :=
    r.observedRefinement.mapBehavioralStrategy
  outcomeMap := id
  map_outcome := by
    intro profile
    exact
      (r.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- The behavioral continuation morphism preserves a shared functional on
payoff laws. -/
theorem behavioralContinuationGameFormHom_utilityCompatible
    {V : Type uV}
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    GameForm.Hom.UtilityCompatible
      (r.behavioralContinuationGameFormHom
        current fuel)
      utility utility := by
  intro outcome i
  rfl

/-- Behavioral-strategy surjectivity of an information refinement gives
strategy surjectivity of every induced bounded continuation morphism. -/
theorem behavioralContinuationGameFormHom_strategySurjective
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective) :
    (r.behavioralContinuationGameFormHom
      current fuel).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Behavioral Nash equilibrium of a lifted fine continuation reflects to
the corresponding coarse continuation.

No surjectivity is needed in this direction: fine Nash already checks the
images of all coarse unilateral deviations. -/
theorem behavioralContinuationIsNash_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ)
    (hNash :
      (H.behavioralContinuationGameForm
        (r.observedRefinement.historyIso.stateEquiv
          current)
        fuel).IsNash
          utility
          (r.observedRefinement.mapBehavioralProfile
            profile)) :
    (G.behavioralContinuationGameForm
      current fuel).IsNash utility profile := by
  exact
    hNash.comap
      (r.behavioralContinuationGameFormHom
        current fuel)
      (r.behavioralContinuationGameFormHom_utilityCompatible
        utility current fuel)

/-- Under explicit behavioral deviation lifting, corresponding bounded
continuations have equivalent Nash predicates. -/
theorem behavioralContinuationIsNash_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.behavioralContinuationGameForm
      current fuel).IsNash utility profile ↔
      (H.behavioralContinuationGameForm
        (r.observedRefinement.historyIso.stateEquiv
          current)
        fuel).IsNash
          utility
          (r.observedRefinement.mapBehavioralProfile
            profile) := by
  exact
    (r.behavioralContinuationGameFormHom
      current fuel).isNash_iff_of_strategySurjective
        (r.behavioralContinuationGameFormHom_utilityCompatible
          utility current fuel)
        (r.behavioralContinuationGameFormHom_strategySurjective
          current fuel hsurjective)
        profile

/-- Bounded behavioral Nash on explicitly mapped target roots of a lifted
fine profile reflects to the selected coarse source roots. -/
theorem isBehavioralNashOnRootsAtFuel_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.MapsRootPresentations
        sourceRoots targetRoots)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsBehavioralNashOnRootsAtFuel
        targetRoots utility
        (r.observedRefinement.mapBehavioralProfile
          profile)
        fuel) :
    G.IsBehavioralNashOnRootsAtFuel
      sourceRoots utility profile fuel := by
  intro sourceRoot hsourceRoot
  have htargetRoot :
      targetRoots.IsRoot
        (r.observedRefinement.historyIso.stateEquiv sourceRoot) :=
    hroots sourceRoot hsourceRoot
  exact
    r.behavioralContinuationIsNash_of_map
      utility profile sourceRoot fuel
      (hSPE
        (r.observedRefinement.historyIso.stateEquiv
          sourceRoot)
        htargetRoot)

/-- With behavioral-strategy-surjective lifting and exact root
correspondence, bounded behavioral Nash transfers in both directions. -/
theorem isBehavioralNashOnRootsAtFuel_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      r.observedRefinement.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility :
      FiniteLaw (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnRootsAtFuel
        sourceRoots utility profile fuel ↔
      H.IsBehavioralNashOnRootsAtFuel
        targetRoots utility
        (r.observedRefinement.mapBehavioralProfile
          profile)
        fuel := by
  constructor
  · intro hSPE targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      r.observedRefinement.historyIso.stateEquiv.surjective
        targetRoot
    have hsourceRoot :
        sourceRoots.IsRoot sourceRoot :=
      (hroots sourceRoot).mpr htargetRoot
    have hsourceNash :=
      hSPE sourceRoot hsourceRoot
    exact
      (r.behavioralContinuationIsNash_iff_of_strategySurjective
        hsurjective utility profile sourceRoot fuel).mp
        hsourceNash
  · exact fun hSPE =>
      r.isBehavioralNashOnRootsAtFuel_of_map
        sourceRoots targetRoots
        (fun history => (hroots history).mp)
        utility profile fuel hSPE

end ExtensiveGame.ObservedChanceGame.InformationRefinement
