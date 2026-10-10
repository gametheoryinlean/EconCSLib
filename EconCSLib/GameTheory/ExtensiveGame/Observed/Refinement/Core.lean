/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Core

Strategy lifting, bounded execution, and bounded equilibrium transfer.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

namespace InformationRefinement

variable {G H : ObservedGame N U}

/-- Forgetting fine represented information yields represented coarse
information. -/
abbrev forgetRepresentedInfo
    (r : G.InformationRefinement H) (i : N) :=
  r.toControlled.forgetRepresentedInfo i

/-- Lift a coarse pure strategy to the finer information structure. -/
def mapStrategy (r : G.InformationRefinement H) (i : N)
    (strategy : G.PureStrategy i) :
    H.PureStrategy i :=
  r.toControlled.mapStrategy i strategy

/-- Lift a complete coarse pure profile player by player. -/
def mapProfile (r : G.InformationRefinement H)
    (profile : G.PureProfile) :
    H.PureProfile :=
  fun i => r.mapStrategy i (profile i)

/-- Every fine pure strategy is represented by a lifted coarse strategy.

This is the exact additional deviation-lifting hypothesis needed to turn the
default one-way equilibrium reflection into two-way transfer. It generally
fails for a genuine information refinement. -/
def StrategySurjective
    (r : G.InformationRefinement H) : Prop :=
  ∀ i : N, Function.Surjective (r.mapStrategy i)

/-- Identity refinement leaves pure strategies unchanged. -/
@[simp]
theorem refl_mapStrategy
    (G : ObservedGame N U) (i : N)
    (strategy : G.PureStrategy i) :
    (refl G).mapStrategy i strategy = strategy :=
  rfl

/-- Strategy lifting along a composite refinement is successive lifting. -/
@[simp]
theorem trans_mapStrategy {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (i : N) (strategy : G.PureStrategy i) :
    (r.trans s).mapStrategy i strategy =
      s.mapStrategy i (r.mapStrategy i strategy) :=
  rfl

/-- Profile lifting along a composite refinement is successive lifting. -/
@[simp]
theorem trans_mapProfile {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (profile : G.PureProfile) :
    (r.trans s).mapProfile profile =
      s.mapProfile (r.mapProfile profile) :=
  rfl

@[simp]
theorem mapProfile_apply
    (r : G.InformationRefinement H)
    (profile : G.PureProfile) (i : N) :
    r.mapProfile profile i = r.mapStrategy i (profile i) :=
  rfl

/-- Strategy lifting commutes with unilateral deviation. -/
theorem mapProfile_deviate [DecidableEq N]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile) (i : N)
    (strategy : G.PureStrategy i) :
    r.mapProfile (Function.update profile i strategy) =
      Function.update (r.mapProfile profile) i
        (r.mapStrategy i strategy) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [mapProfile]
  · simp [mapProfile, hji]

/-- Lifted and coarse profiles choose corresponding concrete actions at every
player-controlled history. -/
theorem map_actionAt
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (r.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1) :
    PureProfile.actionAt H
        (r.mapProfile profile)
        (r.historyIso.stateEquiv history) i htarget
        htarget_nonterminal =
      r.historyIso.actionEquiv history
        (PureProfile.actionAt G profile history i hsource
          hsource_nonterminal) := by
  exact
    r.toControlled.map_actionAt profile history i hsource
      hsource_nonterminal htarget htarget_nonterminal

/-- The strict history map identifies terminal histories exactly. -/
theorem isTerminal_iff
    (r : G.InformationRefinement H)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    G.base.isTerminal history.1 ↔
      H.base.isTerminal
        (r.historyIso.stateEquiv history).1 :=
  r.historyIso.isTerminal_iff history

/-- Pure history policies induced by lifted profiles commute with the strict
history and action equivalences. -/
theorem map_toHistoryPolicy
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hsource : ¬ G.base.isTerminal history.1)
    (htarget :
      ¬ H.base.isTerminal
        (r.historyIso.stateEquiv history).1) :
    (r.mapProfile profile).toHistoryPolicy H hNoChanceH
        (r.historyIso.stateEquiv history) htarget =
      r.historyIso.actionEquiv history
        (profile.toHistoryPolicy G hNoChanceG
          history hsource) := by
  let i := G.playerAt hNoChanceG history hsource
  have hsourceMover :
      G.base.mover history.1 = some i :=
    G.mover_playerAt hNoChanceG history hsource
  have htargetMover :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i := by
    rw [r.map_mover history]
    exact hsourceMover
  rw [PureProfile.toHistoryPolicy_of_mover
    H (r.mapProfile profile) hNoChanceH
    (r.historyIso.stateEquiv history) htarget
    i htargetMover]
  rw [PureProfile.toHistoryPolicy_of_mover
    G profile hNoChanceG history hsource
    i hsourceMover]
  exact
    r.map_actionAt profile history i
      hsourceMover
      (G.base.toArena.isDecision_of_not_isTerminal _ hsource)
      htargetMover
      (H.base.toArena.isDecision_of_not_isTerminal _ htarget)

/-- The strict history map commutes exactly with bounded continuation
execution of every lifted no-chance profile. -/
theorem map_stoppedHistoryFrom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) :
    ∀ fuel,
      r.historyIso.stateEquiv
          (G.stoppedHistoryFrom
            profile hNoChanceG current fuel) =
        H.stoppedHistoryFrom
          (r.mapProfile profile) hNoChanceH
          (r.historyIso.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hsource :
          G.base.isTerminal current.1
      · have htarget :
            H.base.isTerminal
              (r.historyIso.stateEquiv current).1 :=
          (r.isTerminal_iff current).mp hsource
        rw [stoppedHistoryFrom, stoppedHistoryFrom,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ (r.historyIso.stateEquiv current)
            fuel htarget]
      · have htarget :
            ¬ H.base.isTerminal
              (r.historyIso.stateEquiv current).1 :=
          not_congr (r.isTerminal_iff current) |>.mp hsource
        rw [stoppedHistoryFrom, stoppedHistoryFrom,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ (r.historyIso.stateEquiv current)
            fuel htarget]
        change
          r.historyIso.stateEquiv
              (G.stoppedHistoryFrom profile hNoChanceG
                ⟨G.base.next current.1
                    (profile.toHistoryPolicy G hNoChanceG
                      current hsource),
                  current.2.snoc
                    (profile.toHistoryPolicy G hNoChanceG
                      current hsource)⟩
                fuel) =
            H.stoppedHistoryFrom
              (r.mapProfile profile) hNoChanceH
              ⟨H.base.next
                  (r.historyIso.stateEquiv current).1
                  ((r.mapProfile profile).toHistoryPolicy
                    H hNoChanceH
                    (r.historyIso.stateEquiv current)
                    htarget),
                (r.historyIso.stateEquiv current).2.snoc
                  ((r.mapProfile profile).toHistoryPolicy
                    H hNoChanceH
                    (r.historyIso.stateEquiv current)
                    htarget)⟩
              fuel
        rw [ih]
        apply congrArg
          (fun next =>
            H.stoppedHistoryFrom
              (r.mapProfile profile) hNoChanceH
              next fuel)
        rw [r.map_toHistoryPolicy profile
          hNoChanceG hNoChanceH current hsource htarget]
        exact
          r.historyIso.map_next current
            (profile.toHistoryPolicy
              G hNoChanceG current hsource)

/-- Lifted and coarse profiles have exactly corresponding bounded optional
terminal payoffs from every continuation. -/
theorem map_stoppedPayoffFrom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    H.stoppedPayoffFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) fuel =
      G.stoppedPayoffFrom
        profile hNoChanceG current fuel := by
  rw [stoppedPayoffFrom, stoppedPayoffFrom,
    ← r.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
  let result :=
    G.stoppedHistoryFrom
      profile hNoChanceG current fuel
  change
    (if H.base.isTerminal
          (r.historyIso.stateEquiv result).1 then
        some
          (H.base.payoff
            (r.historyIso.stateEquiv result).1)
      else none) =
      if G.base.isTerminal result.1 then
        some (G.base.payoff result.1)
      else none
  by_cases hterminal :
      G.base.isTerminal result.1
  · have htarget :
        H.base.isTerminal
          (r.historyIso.stateEquiv result).1 :=
      (r.isTerminal_iff result).mp hterminal
    rw [if_pos htarget, if_pos hterminal,
      r.map_payoff result hterminal]
  · have htarget :
        ¬ H.base.isTerminal
          (r.historyIso.stateEquiv result).1 :=
      not_congr (r.isTerminal_iff result) |>.mp
        hterminal
    rw [if_neg htarget, if_neg hterminal]

/-- Every information refinement induces a game-form morphism between
corresponding bounded continuations. -/
def continuationGameFormHom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    (G.continuationGameForm
      hNoChanceG current fuel).Hom
      (H.continuationGameForm hNoChanceH
        (r.historyIso.stateEquiv current) fuel) where
  strategyMap := r.mapStrategy
  outcomeMap := id
  map_outcome := by
    intro profile
    exact
      (r.map_stoppedPayoffFrom profile
        hNoChanceG hNoChanceH current fuel).symm

/-- The bounded continuation morphism preserves the shared interpretation of
optional terminal outcomes. -/
theorem continuationGameFormHom_utilityCompatible
    {V : Type uV}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    GameForm.Hom.UtilityCompatible
      (r.continuationGameFormHom
        hNoChanceG hNoChanceH current fuel)
      utility utility := by
  intro outcome i
  rfl

/-- Strategy surjectivity of an information refinement is exactly strategy
surjectivity of each induced bounded continuation morphism. -/
theorem continuationGameFormHom_strategySurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ)
    (hsurjective : r.StrategySurjective) :
    (r.continuationGameFormHom
      hNoChanceG hNoChanceH current fuel
      ).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Nash equilibrium of a lifted fine continuation reflects to the coarse
continuation.

No surjectivity of the strategy lift is needed: the fine Nash hypothesis
already checks the images of all coarse unilateral deviations. -/
theorem continuationIsNash_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ)
    (hNash :
      (H.continuationGameForm hNoChanceH
        (r.historyIso.stateEquiv current) fuel).IsNash
        utility (r.mapProfile profile)) :
    (G.continuationGameForm hNoChanceG current fuel).IsNash
      utility profile := by
  exact
    hNash.comap
      (r.continuationGameFormHom
        hNoChanceG hNoChanceH current fuel)
      (r.continuationGameFormHom_utilityCompatible
        hNoChanceG hNoChanceH utility current fuel)

/-- Under explicit deviation lifting, corresponding bounded continuations
have equivalent Nash predicates. -/
theorem continuationIsNash_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (hsurjective : r.StrategySurjective)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    (G.continuationGameForm
      hNoChanceG current fuel).IsNash
        utility profile ↔
      (H.continuationGameForm hNoChanceH
        (r.historyIso.stateEquiv current) fuel).IsNash
        utility (r.mapProfile profile) := by
  exact
    (r.continuationGameFormHom
      hNoChanceG hNoChanceH current fuel
      ).isNash_iff_of_strategySurjective
        (r.continuationGameFormHom_utilityCompatible
          hNoChanceG hNoChanceH utility current fuel)
        (r.continuationGameFormHom_strategySurjective
          hNoChanceG hNoChanceH current fuel
          hsurjective)
        profile

/-- Bounded Nash on explicitly mapped roots of a lifted fine profile reflects
to bounded Nash on the selected coarse source roots. -/
theorem isPureNashOnRootsAtFuel_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.MapsRootPresentations sourceRoots targetRoots)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsPureNashOnRootsAtFuel
        hNoChanceH targetRoots utility (r.mapProfile profile) fuel) :
    G.IsPureNashOnRootsAtFuel
      hNoChanceG sourceRoots utility profile fuel := by
  intro sourceRoot hsourceRoot
  have htargetRoot :
      targetRoots.IsRoot (r.historyIso.stateEquiv sourceRoot) :=
    hroots sourceRoot hsourceRoot
  exact
    r.continuationIsNash_of_map
      hNoChanceG hNoChanceH utility profile
      sourceRoot fuel
      (hSPE
        (r.historyIso.stateEquiv sourceRoot)
        htargetRoot)

/-- With strategy-surjective lifting and exact root correspondence, bounded
pure Nash transfers in both directions. -/
theorem isPureNashOnRootsAtFuel_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (hsurjective : r.StrategySurjective)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnRootsAtFuel
        hNoChanceG sourceRoots utility profile fuel ↔
      H.IsPureNashOnRootsAtFuel
        hNoChanceH targetRoots utility
        (r.mapProfile profile) fuel := by
  constructor
  · intro hSPE targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      r.historyIso.stateEquiv.surjective
        targetRoot
    have hsourceRoot :
        sourceRoots.IsRoot sourceRoot :=
      (hroots sourceRoot).mpr htargetRoot
    have hsourceNash :=
      hSPE sourceRoot hsourceRoot
    have hmapped :=
      (r.continuationIsNash_iff_of_strategySurjective
        hNoChanceG hNoChanceH hsurjective
        utility profile sourceRoot fuel).mp
        hsourceNash
    change
      (H.continuationGameForm hNoChanceH
        (r.historyIso.stateEquiv sourceRoot)
        fuel).IsNash
          utility (r.mapProfile profile) at hmapped
    exact hmapped
  · exact fun hSPE =>
      r.isPureNashOnRootsAtFuel_of_map
        hNoChanceG hNoChanceH sourceRoots targetRoots
        (fun history => (hroots history).mp) utility
        profile fuel hSPE


end InformationRefinement

end ExtensiveGame.ObservedGame
