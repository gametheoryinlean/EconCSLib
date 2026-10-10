/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics

/-!
# Objective semantics under strict observed-EFG isomorphisms

This module transports the concrete pure terminal-objective continuation
semantics through a strict `ControlledObservedGame.Iso`.

A structural isomorphism alone does not preserve an objective. The explicit
`TerminalObjectiveCompatible` premise requires the target objective on every
mapped terminal history to equal the source objective. Only under that exact
commuting square do the continuation game forms become isomorphic and Nash
equilibrium transfer in both directions.
-/

namespace ExtensiveGame.ControlledObservedGame

universe uN uOutcome uV

variable {N : Type uN}

namespace InformationRefinement

variable {G H : ControlledObservedGame N}

/-- The pure history policies induced by a coarse profile and its lifted fine
profile commute with the strict history and action equivalences. -/
theorem map_toHistoryPolicy
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (history : G.base.History)
    (hsource : ¬ G.base.isTerminal history.1)
    (htarget :
      ¬ H.base.isTerminal
        (r.historyIso.stateEquiv history).1) :
    (r.mapProfile profile).toHistoryPolicy hNoChanceH
        (r.historyIso.stateEquiv history) htarget =
      r.historyIso.actionEquiv history
        (profile.toHistoryPolicy hNoChanceG history hsource) := by
  let player := G.playerAt hNoChanceG history hsource
  have hsourceMover :
      G.base.mover history.1 = some player :=
    G.mover_playerAt hNoChanceG history hsource
  have htargetMover :
      H.base.mover (r.historyIso.stateEquiv history).1 =
        some player := by
    rw [r.map_mover history]
    exact hsourceMover
  rw [PureProfile.toHistoryPolicy_of_mover
    (r.mapProfile profile) hNoChanceH
    (r.historyIso.stateEquiv history) htarget player htargetMover]
  rw [PureProfile.toHistoryPolicy_of_mover
    profile hNoChanceG history hsource player hsourceMover]
  exact
    r.map_actionAt profile history player hsourceMover
      (G.base.toArena.isDecision_of_not_isTerminal history.1 hsource)
      htargetMover
      (H.base.toArena.isDecision_of_not_isTerminal
        (r.historyIso.stateEquiv history).1 htarget)

/-- Strict history mapping commutes exactly with continuation execution of a
lifted no-chance pure profile. -/
theorem map_stoppedHistoryFrom
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History) :
    ∀ fuel,
      r.historyIso.stateEquiv
          (G.base.toArena.stoppedHistoryFrom
            (profile.toHistoryPolicy hNoChanceG) current fuel) =
        H.base.toArena.stoppedHistoryFrom
          ((r.mapProfile profile).toHistoryPolicy hNoChanceH)
          (r.historyIso.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hsource : G.base.isTerminal current.1
      · have htarget :
            H.base.isTerminal
              (r.historyIso.stateEquiv current).1 :=
          (r.historyIso.isTerminal_iff current).mp hsource
        rw [
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ (r.historyIso.stateEquiv current) fuel htarget]
      · have htarget :
            ¬ H.base.isTerminal
              (r.historyIso.stateEquiv current).1 :=
          (not_congr
            (r.historyIso.isTerminal_iff current)).mp hsource
        rw [
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ (r.historyIso.stateEquiv current) fuel htarget]
        rw [ih]
        apply congrArg
          (fun next =>
            H.base.toArena.stoppedHistoryFrom
              ((r.mapProfile profile).toHistoryPolicy hNoChanceH)
              next fuel)
        rw [r.map_toHistoryPolicy profile hNoChanceG hNoChanceH
          current hsource htarget]
        exact r.historyIso.map_next current
          (profile.toHistoryPolicy hNoChanceG current hsource)

/-- A coarse profile terminates exactly when its lifted fine profile
terminates at the corresponding history. -/
theorem pureTerminatesFrom_iff_map
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History) :
    G.PureTerminatesFrom profile hNoChanceG current ↔
      H.PureTerminatesFrom (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) := by
  constructor
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    change
      H.base.isTerminal
        (H.base.toArena.stoppedHistoryFrom
          ((r.mapProfile profile).toHistoryPolicy hNoChanceH)
          (r.historyIso.stateEquiv current) fuel).1
    rw [← r.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
    exact
      (r.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG) current fuel)).mp
        hterminal
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    have hmapped :
        H.base.isTerminal
          (r.historyIso.stateEquiv
            (G.base.toArena.stoppedHistoryFrom
              (profile.toHistoryPolicy hNoChanceG)
              current fuel)).1 := by
      rw [r.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current fuel]
      exact hterminal
    exact
      (r.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG) current fuel)).mpr
        hmapped

/-- The strict history map sends the selected coarse terminal history to the
selected fine terminal history of the lifted profile. -/
theorem map_terminalHistoryFrom
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel) :
    r.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current sourceFuel) =
      H.terminalHistoryFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel := by
  have hmappedTerminal :
      H.base.isTerminal
        (H.base.toArena.stoppedHistoryFrom
          ((r.mapProfile profile).toHistoryPolicy hNoChanceH)
          (r.historyIso.stateEquiv current) sourceFuel).1 := by
    rw [← r.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current sourceFuel]
    exact
      (r.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG)
          current sourceFuel)).mp hsourceTerminal
  calc
    r.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current sourceFuel) =
      H.base.toArena.stoppedHistoryFrom
        ((r.mapProfile profile).toHistoryPolicy hNoChanceH)
        (r.historyIso.stateEquiv current) sourceFuel := by
          exact r.map_stoppedHistoryFrom
            profile hNoChanceG hNoChanceH current sourceFuel
    _ =
      H.terminalHistoryFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel :=
      (H.terminalHistoryFrom_eq_of_terminal
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel htargetTerminal
        sourceFuel hmappedTerminal).symm

/-- Exact compatibility of history-sensitive terminal objectives with a
directional information refinement. -/
def TerminalObjectiveCompatible
    {Outcome : Type uOutcome}
    (r : G.InformationRefinement H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome) : Prop :=
  ∀ terminalHistory : G.base.toArena.TerminalHistoryFrom G.base.init,
    target
      ⟨r.historyIso.stateEquiv terminalHistory.1,
        (r.historyIso.isTerminal_iff terminalHistory.1).mp
          terminalHistory.2⟩ =
      source terminalHistory

/-- Under exact objective compatibility, lifted fine continuations have the
same terminal objective value as their coarse source continuations. -/
theorem map_terminalOutcomeFrom
    {Outcome : Type uOutcome}
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : r.TerminalObjectiveCompatible source target)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel) :
    H.terminalOutcomeFrom target (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel htargetTerminal =
      G.terminalOutcomeFrom source profile hNoChanceG current
        sourceFuel hsourceTerminal := by
  let sourceTerminal :
      G.base.toArena.TerminalHistoryFrom G.base.init :=
    ⟨G.terminalHistoryFrom
        profile hNoChanceG current sourceFuel,
      G.terminalHistoryFrom_terminal
        profile hNoChanceG current sourceFuel hsourceTerminal⟩
  let targetTerminal :
      H.base.toArena.TerminalHistoryFrom H.base.init :=
    ⟨H.terminalHistoryFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel,
      H.terminalHistoryFrom_terminal
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current) targetFuel htargetTerminal⟩
  have hterminal :
      targetTerminal =
        ⟨r.historyIso.stateEquiv sourceTerminal.1,
          (r.historyIso.isTerminal_iff sourceTerminal.1).mp
            sourceTerminal.2⟩ := by
    apply Subtype.ext
    exact
      (r.map_terminalHistoryFrom profile hNoChanceG hNoChanceH
        current sourceFuel targetFuel hsourceTerminal htargetTerminal).symm
  change target targetTerminal = source sourceTerminal
  rw [hterminal]
  exact hobjective sourceTerminal

/-- Exact objective compatibility induces a directional morphism from the
coarse total continuation game form to the fine one. -/
def terminalObjectiveContinuationGameFormHom
    {Outcome : Type uOutcome}
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : r.TerminalObjectiveCompatible source target)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (r.historyIso.stateEquiv current)) :
    (G.terminalObjectiveContinuationGameForm
      source hNoChanceG current terminationG).Hom
      (H.terminalObjectiveContinuationGameForm
        target hNoChanceH (r.historyIso.stateEquiv current)
        terminationH) where
  strategyMap := r.mapStrategy
  outcomeMap := id
  map_outcome := by
    intro profile
    exact
      (r.map_terminalOutcomeFrom source target hobjective profile
        hNoChanceG hNoChanceH current
        (terminationG.fuel profile)
        (terminationH.fuel (r.mapProfile profile))
        (terminationG.terminal profile)
        (terminationH.terminal (r.mapProfile profile))).symm

/-- Fine Nash equilibrium of a lifted profile reflects to the coarse
terminal-objective continuation under the exact objective square. -/
theorem terminalObjective_isNash_of_map
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : r.TerminalObjectiveCompatible source target)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (r.historyIso.stateEquiv current))
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hNash :
      (H.terminalObjectiveContinuationGameForm
        target hNoChanceH (r.historyIso.stateEquiv current)
        terminationH).IsNash utility (r.mapProfile profile)) :
    (G.terminalObjectiveContinuationGameForm
      source hNoChanceG current terminationG).IsNash
        utility profile := by
  exact
    hNash.comap
      (r.terminalObjectiveContinuationGameFormHom
        source target hobjective hNoChanceG hNoChanceH current
        terminationG terminationH)
      (by
        intro _outcome _player
        rfl)

end InformationRefinement

namespace Iso

variable {G H : ControlledObservedGame N}

/-- The pure history policies induced by mapped profiles commute with the
strict history and action equivalences. -/
theorem map_toHistoryPolicy
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (history : G.base.History)
    (hsource : ¬ G.base.isTerminal history.1)
    (htarget :
      ¬ H.base.isTerminal (e.historyIso.stateEquiv history).1) :
    (e.mapProfile profile).toHistoryPolicy hNoChanceH
        (e.historyIso.stateEquiv history) htarget =
      e.historyIso.actionEquiv history
        (profile.toHistoryPolicy hNoChanceG history hsource) := by
  let player := G.playerAt hNoChanceG history hsource
  have hsourceMover :
      G.base.mover history.1 = some player :=
    G.mover_playerAt hNoChanceG history hsource
  have htargetMover :
      H.base.mover (e.historyIso.stateEquiv history).1 =
        some player := by
    rw [e.map_mover history]
    exact hsourceMover
  rw [PureProfile.toHistoryPolicy_of_mover
    (e.mapProfile profile) hNoChanceH
    (e.historyIso.stateEquiv history) htarget player htargetMover]
  rw [PureProfile.toHistoryPolicy_of_mover
    profile hNoChanceG history hsource player hsourceMover]
  exact
    e.map_actionAt profile history player hsourceMover
      (G.base.toArena.isDecision_of_not_isTerminal history.1 hsource)
      htargetMover
      (H.base.toArena.isDecision_of_not_isTerminal
        (e.historyIso.stateEquiv history).1 htarget)

/-- Strict history mapping commutes exactly with continuation execution of a
mapped no-chance pure profile. -/
theorem map_stoppedHistoryFrom
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History) :
    ∀ fuel,
      e.historyIso.stateEquiv
          (G.base.toArena.stoppedHistoryFrom
            (profile.toHistoryPolicy hNoChanceG) current fuel) =
        H.base.toArena.stoppedHistoryFrom
          ((e.mapProfile profile).toHistoryPolicy hNoChanceH)
          (e.historyIso.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases hsource : G.base.isTerminal current.1
      · have htarget :
            H.base.isTerminal
              (e.historyIso.stateEquiv current).1 :=
          (e.historyIso.isTerminal_iff current).mp hsource
        rw [
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_terminal
            _ (e.historyIso.stateEquiv current) fuel htarget]
      · have htarget :
            ¬ H.base.isTerminal
              (e.historyIso.stateEquiv current).1 :=
          (not_congr
            (e.historyIso.isTerminal_iff current)).mp hsource
        rw [
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ current fuel hsource,
          Arena.stoppedHistoryFrom_succ_of_not_terminal
            _ (e.historyIso.stateEquiv current) fuel htarget]
        rw [ih]
        apply congrArg
          (fun next =>
            H.base.toArena.stoppedHistoryFrom
              ((e.mapProfile profile).toHistoryPolicy hNoChanceH)
              next fuel)
        rw [e.map_toHistoryPolicy profile hNoChanceG hNoChanceH
          current hsource htarget]
        exact e.historyIso.map_next current
          (profile.toHistoryPolicy hNoChanceG current hsource)

/-- Eventual pure termination at corresponding histories is invariant under a
strict observed-EFG isomorphism. -/
theorem pureTerminatesFrom_iff
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History) :
    G.PureTerminatesFrom profile hNoChanceG current ↔
      H.PureTerminatesFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) := by
  constructor
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    change
      H.base.isTerminal
        (H.base.toArena.stoppedHistoryFrom
          ((e.mapProfile profile).toHistoryPolicy hNoChanceH)
          (e.historyIso.stateEquiv current) fuel).1
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
    exact
      (e.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG) current fuel)).mp
        hterminal
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    have hmapped :
        H.base.isTerminal
          (e.historyIso.stateEquiv
            (G.base.toArena.stoppedHistoryFrom
              (profile.toHistoryPolicy hNoChanceG)
              current fuel)).1 := by
      rw [e.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current fuel]
      exact hterminal
    exact
      (e.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG) current fuel)).mpr
        hmapped

/-- Transport termination of every pure profile at one history. -/
theorem map_pureTerminatingAt
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (hterminates : G.PureTerminatingAt hNoChanceG current) :
    H.PureTerminatingAt hNoChanceH
      (e.historyIso.stateEquiv current) := by
  intro targetProfile
  let sourceProfile : G.PureProfile :=
    fun player => (e.strategyEquiv player).symm (targetProfile player)
  have hmapped :
      e.mapProfile sourceProfile = targetProfile := by
    funext player
    exact (e.strategyEquiv player).apply_symm_apply _
  rw [← hmapped]
  exact
    (e.pureTerminatesFrom_iff
      sourceProfile hNoChanceG hNoChanceH current).mp
      (hterminates sourceProfile)

/-- Strict execution maps the selected terminal history exactly. -/
theorem map_terminalHistoryFrom
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel) :
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current sourceFuel) =
      H.terminalHistoryFrom
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel := by
  have hmappedTerminal :
      H.base.isTerminal
        (H.base.toArena.stoppedHistoryFrom
          ((e.mapProfile profile).toHistoryPolicy hNoChanceH)
          (e.historyIso.stateEquiv current) sourceFuel).1 := by
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current sourceFuel]
    exact
      (e.historyIso.isTerminal_iff
        (G.base.toArena.stoppedHistoryFrom
          (profile.toHistoryPolicy hNoChanceG)
          current sourceFuel)).mp hsourceTerminal
  calc
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current sourceFuel) =
      H.base.toArena.stoppedHistoryFrom
        ((e.mapProfile profile).toHistoryPolicy hNoChanceH)
        (e.historyIso.stateEquiv current) sourceFuel := by
          exact e.map_stoppedHistoryFrom
            profile hNoChanceG hNoChanceH current sourceFuel
    _ =
      H.terminalHistoryFrom
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel :=
      (H.terminalHistoryFrom_eq_of_terminal
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel htargetTerminal
        sourceFuel hmappedTerminal).symm

/-- Exact compatibility of history-sensitive terminal objectives with a
strict observed-EFG isomorphism. -/
def TerminalObjectiveCompatible
    {Outcome : Type uOutcome}
    (e : G.Iso H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome) : Prop :=
  ∀ terminalHistory : G.base.toArena.TerminalHistoryFrom G.base.init,
    target
      ⟨e.historyIso.stateEquiv terminalHistory.1,
        (e.historyIso.isTerminal_iff terminalHistory.1).mp
          terminalHistory.2⟩ =
      source terminalHistory

/-- Under exact objective compatibility, corresponding pure continuations
have exactly the same terminal objective value. -/
theorem map_terminalOutcomeFrom
    {Outcome : Type uOutcome}
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : e.TerminalObjectiveCompatible source target)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel) :
    H.terminalOutcomeFrom target (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel htargetTerminal =
      G.terminalOutcomeFrom source profile hNoChanceG current
        sourceFuel hsourceTerminal := by
  let sourceTerminal :
      G.base.toArena.TerminalHistoryFrom G.base.init :=
    ⟨G.terminalHistoryFrom
        profile hNoChanceG current sourceFuel,
      G.terminalHistoryFrom_terminal
        profile hNoChanceG current sourceFuel hsourceTerminal⟩
  let targetTerminal :
      H.base.toArena.TerminalHistoryFrom H.base.init :=
    ⟨H.terminalHistoryFrom
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel,
      H.terminalHistoryFrom_terminal
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel htargetTerminal⟩
  have hterminal :
      targetTerminal =
        ⟨e.historyIso.stateEquiv sourceTerminal.1,
          (e.historyIso.isTerminal_iff sourceTerminal.1).mp
            sourceTerminal.2⟩ := by
    apply Subtype.ext
    exact
      (e.map_terminalHistoryFrom profile hNoChanceG hNoChanceH
        current sourceFuel targetFuel hsourceTerminal htargetTerminal).symm
  change target targetTerminal = source sourceTerminal
  rw [hterminal]
  exact hobjective sourceTerminal

/-- Exact objective compatibility induces a strict isomorphism of the two
total continuation game forms. -/
def terminalObjectiveContinuationGameFormIso
    {Outcome : Type uOutcome}
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : e.TerminalObjectiveCompatible source target)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (e.historyIso.stateEquiv current)) :
    (G.terminalObjectiveContinuationGameForm
      source hNoChanceG current terminationG).Iso
      (H.terminalObjectiveContinuationGameForm
        target hNoChanceH (e.historyIso.stateEquiv current)
        terminationH) where
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      (e.map_terminalOutcomeFrom source target hobjective profile
        hNoChanceG hNoChanceH current
        (terminationG.fuel profile)
        (terminationH.fuel (e.mapProfile profile))
        (terminationG.terminal profile)
        (terminationH.terminal (e.mapProfile profile))).symm

/-- Under the exact objective square, strict observed-EFG isomorphism
preserves and reflects pure Nash equilibrium at one continuation root. -/
theorem terminalObjective_isNash_iff
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    [(state : H.base.State) → Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (source :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (target :
      H.base.toArena.TerminalOutcome H.base.init Outcome)
    (hobjective : e.TerminalObjectiveCompatible source target)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.History)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (e.historyIso.stateEquiv current))
    (utility : Outcome → N → V)
    (profile : G.PureProfile) :
    (G.terminalObjectiveContinuationGameForm
      source hNoChanceG current terminationG).IsNash
        utility profile ↔
      (H.terminalObjectiveContinuationGameForm
        target hNoChanceH (e.historyIso.stateEquiv current)
        terminationH).IsNash utility (e.mapProfile profile) := by
  exact
    GameForm.Iso.isNash_iff
      (e.terminalObjectiveContinuationGameFormIso
        source target hobjective hNoChanceG hNoChanceH current
        terminationG terminationH)
      (by
        intro _outcome _player
        rfl)
      profile

end Iso

end ExtensiveGame.ControlledObservedGame
