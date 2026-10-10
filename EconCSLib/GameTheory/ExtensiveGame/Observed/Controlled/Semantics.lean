/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.IndexedContinuation
import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame

/-!
# Payoff-free observed continuation and objective semantics

Operational pure continuation semantics for history-sensitive terminal and
complete-path objectives, plus an adapter from a `ControlledObservedGame` to
an arbitrary indexed continuation evaluator.

The operational layer executes the canonical full pure-profile strategy
space. Terminal objectives require explicit reachable no-chance and
profile-by-profile termination evidence. Path objectives use the canonical
terminal-absorbing complete play and reattach the accumulated absolute prefix,
so an objective can distinguish histories that merge at the same endpoint.
The resulting Nash-on-presentation, lawful-system SPE, and complete standard
SPE predicates are concrete EFG semantics rather than arbitrary
evaluator-relative notions.

A client supplies strategy spaces, a horizon/index type, an outcome type, and
an evaluator on complete-history roots. The game supplies only payoff-free
dynamics, information, and the history-root type. Root presentation,
lawful-subgame coverage, utility interpretation, and deviation coverage remain
explicit and orthogonal.

The generic equilibrium predicates in this module are explicitly
**evaluator-relative**: an arbitrary evaluator does not by itself define the
standard execution semantics of an EFG. Operational standard-SPE definitions
in this module are limited to the concrete pure execution layer; the arbitrary
evaluator API retains its explicitly relative names.

The generic transfer theorem remains an abstract game-form result. It assumes
complete lawful source and target systems, exact continuation outcome
transport, utility compatibility, target strategy/deviation coverage, and
target lawful-root coverage; it does not infer execution semantics from those
premises.
-/

namespace ExtensiveGame.ControlledObservedGame

universe uN uStrategy uHorizon uOutcome uV

variable {N : Type uN}

/-! ## Operational pure objective semantics -/

variable {G : ControlledObservedGame N}

/-- One explicit fuel reaches a terminal history from an accumulated absolute
history under a pure profile. -/
def PureTerminatesAtFuel
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (fuel : ℕ) : Prop :=
  G.base.isTerminal
    (G.base.toArena.stoppedHistoryFrom
      (profile.toHistoryPolicy hNoChance) current fuel).1

/-- A pure profile eventually reaches a terminal history from one accumulated
absolute history. -/
def PureTerminatesFrom
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) : Prop :=
  ∃ fuel : ℕ, G.PureTerminatesAtFuel profile hNoChance current fuel

/-- Executable profile-indexed fuels together with a separate proof that each
chosen fuel reaches a terminal endpoint. -/
structure PureTerminationPlanAt
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) where
  /-- Runtime fuel used for one complete pure profile. -/
  fuel : G.PureProfile → ℕ
  /-- The runtime fuel reaches a terminal endpoint for every profile. -/
  terminal :
    ∀ profile,
      G.PureTerminatesAtFuel profile hNoChance current (fuel profile)

/-- Every pure profile terminates from one accumulated absolute history. -/
def PureTerminatingAt
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) : Prop :=
  ∀ profile : G.PureProfile,
    G.PureTerminatesFrom profile hNoChance current

/-- Every pure profile terminates at each root selected by an explicit
continuation presentation. -/
def PureTerminatingOnRoots
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.ContinuationRootPresentation) : Prop :=
  ∀ current : G.base.History,
    roots.IsRoot current →
      G.PureTerminatingAt hNoChance current

/-- Every pure profile terminates at each root of one explicit lawful subgame
system. -/
def PureTerminatingOn
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem) : Prop :=
  ∀ current : G.base.History,
    system.IsRoot current →
      G.PureTerminatingAt hNoChance current

/-- Presentation-wide termination restricts to a separately proved visible
lawful subgame system. -/
theorem PureTerminatingOnRoots.onSubgameSystem
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.ContinuationRootPresentation)
    (hterminates : G.PureTerminatingOnRoots hNoChance roots)
    (system : G.SubgameSystem)
    (hvisible : system.IsVisibleIn roots) :
    G.PureTerminatingOn hNoChance system :=
  fun current hroot =>
    hterminates current (hvisible current hroot)

/-- The absolute history reached at an explicit runtime fuel. -/
def terminalHistoryFrom
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (fuel : ℕ) :
    G.base.History :=
  G.base.toArena.stoppedHistoryFrom
    (profile.toHistoryPolicy hNoChance) current fuel

/-- The selected eventual history is terminal. -/
theorem terminalHistoryFrom_terminal
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (fuel : ℕ)
    (hterminal :
      G.PureTerminatesAtFuel profile hNoChance current fuel) :
    G.base.isTerminal
      (G.terminalHistoryFrom
        profile hNoChance current fuel).1 :=
  hterminal

/-- Any fuel that has already terminated yields the selected terminal
history. -/
theorem terminalHistoryFrom_eq_of_terminal
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (selectedFuel : ℕ)
    (hselectedTerminal :
      G.PureTerminatesAtFuel profile hNoChance current selectedFuel)
    (fuel : ℕ)
    (hterminal : G.PureTerminatesAtFuel profile hNoChance current fuel) :
    G.terminalHistoryFrom profile hNoChance current selectedFuel =
      G.base.toArena.stoppedHistoryFrom
        (profile.toHistoryPolicy hNoChance) current fuel := by
  exact
    Arena.stoppedHistoryFrom_eq_of_terminal
      (profile.toHistoryPolicy hNoChance) current
      selectedFuel fuel
      (G.terminalHistoryFrom_terminal
        profile hNoChance current selectedFuel hselectedTerminal)
      hterminal

/-- Evaluate a history-sensitive terminal objective on the absolute terminal
history selected by pure execution. -/
def terminalOutcomeFrom
    {Outcome : Type uOutcome}
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (fuel : ℕ)
    (hterminal :
      G.PureTerminatesAtFuel profile hNoChance current fuel) :
    Outcome :=
  objective
    ⟨G.terminalHistoryFrom profile hNoChance current fuel,
      G.terminalHistoryFrom_terminal
        profile hNoChance current fuel hterminal⟩

/-- The root play obtained by executing from `current` and reattaching the
complete accumulated prefix.

The reattachment is essential for path objectives: evaluating only a
re-rooted suffix would forget earlier occurrences and the absolute clock. -/
def pureContinuationPlay
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) :
    G.base.toArena.CompletePlayFrom G.base.init :=
  Arena.CompletePlayFromHistory.reattachTail
    ⟨current,
      (profile.toHistoryPolicy hNoChance).completePlayFrom current⟩

/-- Evaluate a root-relative path objective after an accumulated history
without losing the prefix. -/
def pathOutcomeFrom
    {Outcome : Type uOutcome}
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) :
    Outcome :=
  objective (G.pureContinuationPlay profile hNoChance current)

/-- Total continuation game form for a history-sensitive terminal objective.

The full pure strategy spaces are reused, so deviations are the canonical
complete pure-strategy deviations. Totality comes only from the supplied
profile-by-profile termination proof. -/
def terminalObjectiveContinuationGameForm
    {Outcome : Type uOutcome}
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History)
    (termination : G.PureTerminationPlanAt hNoChance current) :
    GameForm N where
  Strategy := G.PureStrategy
  Outcome := Outcome
  outcome profile :=
    G.terminalOutcomeFrom objective profile hNoChance current
      (termination.fuel profile) (termination.terminal profile)

/-- Continuation game form for a root-relative complete-path objective.

No termination hypothesis is needed because a `PathOutcome` is defined on
both eventually terminal and genuinely infinite complete plays. -/
def pathObjectiveContinuationGameForm
    {Outcome : Type uOutcome}
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.History) :
    GameForm N where
  Strategy := G.PureStrategy
  Outcome := Outcome
  outcome profile :=
    G.pathOutcomeFrom objective profile hNoChance current

/-- Pure Nash equilibrium at every presentation-designated root under a
history-sensitive terminal objective. This is not, by itself, SPE. -/
def IsPureTerminalNashOnRoots
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.ContinuationRootPresentation)
    (termination :
      ∀ current, roots.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.History,
    ∀ hroot : roots.IsRoot current,
      (G.terminalObjectiveContinuationGameForm objective hNoChance current
        (termination current hroot)).IsNash utility profile

/-- Pure subgame perfection on one explicit lawful subgame system under a
history-sensitive terminal objective. -/
def IsPureTerminalSubgamePerfectOn
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.History,
    ∀ hroot : system.IsRoot current,
      (G.terminalObjectiveContinuationGameForm objective hNoChance current
        (termination current hroot)).IsNash utility profile

/-- Standard pure SPE for a history-sensitive terminal objective. The
complete system tests every structurally lawful subgame root. -/
def IsPureTerminalStandardSubgamePerfect
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  G.IsPureTerminalSubgamePerfectOn objective hNoChance
    system.toSubgameSystem termination utility profile

/-- Terminal-objective SPE on a lawful system is Nash at the initial root. -/
theorem IsPureTerminalSubgamePerfectOn.isNashAtInit
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureTerminalSubgamePerfectOn objective hNoChance
        system termination utility profile) :
    (G.terminalObjectiveContinuationGameForm objective hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (termination
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.init_isRoot)).IsNash utility profile :=
  hspe
    (Arena.HistoryFrom.nil G.base.toArena G.base.init)
    system.init_isRoot

/-- Terminal-objective SPE gives Nash at every selected lawful-system root. -/
theorem IsPureTerminalSubgamePerfectOn.toNashOnSystemRoots
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureTerminalSubgamePerfectOn objective hNoChance
        system termination utility profile) :
    ∀ current, ∀ hroot : system.IsRoot current,
      (G.terminalObjectiveContinuationGameForm objective hNoChance current
        (termination current hroot)).IsNash utility profile :=
  hspe

/-- Complete terminal-objective standard SPE is SPE on its underlying lawful
system. -/
theorem IsPureTerminalStandardSubgamePerfect.toSubgamePerfectOn
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureTerminalStandardSubgamePerfect objective hNoChance
        system termination utility profile) :
    G.IsPureTerminalSubgamePerfectOn objective hNoChance
      system.toSubgameSystem termination utility profile :=
  hspe

/-- Complete terminal-objective standard SPE is Nash at the initial root. -/
theorem IsPureTerminalStandardSubgamePerfect.isNashAtInit
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureTerminalStandardSubgamePerfect objective hNoChance
        system termination utility profile) :
    (G.terminalObjectiveContinuationGameForm objective hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (termination
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.toSubgameSystem.init_isRoot)).IsNash utility profile :=
  IsPureTerminalSubgamePerfectOn.isNashAtInit G objective hNoChance
    system.toSubgameSystem termination utility profile hspe

/-- Complete terminal-objective standard SPE is Nash at every structurally
lawful root. -/
theorem IsPureTerminalStandardSubgamePerfect.toNashOnLawfulRoots
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.TerminalOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureTerminalStandardSubgamePerfect objective hNoChance
        system termination utility profile) :
    ∀ current, ∀ hlawful : G.IsLawfulSubgameRoot current,
      (G.terminalObjectiveContinuationGameForm objective hNoChance current
        (termination current
          (system.complete current hlawful))).IsNash utility profile := by
  intro current hlawful
  exact hspe current (system.complete current hlawful)

/-- Pure Nash equilibrium at every presentation-designated root for a
complete-path objective. -/
def IsPurePathNashOnRoots
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.ContinuationRootPresentation)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.History,
    roots.IsRoot current →
      (G.pathObjectiveContinuationGameForm
        objective hNoChance current).IsNash utility profile

/-- Pure subgame perfection on an explicit lawful system for a complete-path
objective. -/
def IsPurePathSubgamePerfectOn
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.History,
    system.IsRoot current →
      (G.pathObjectiveContinuationGameForm
        objective hNoChance current).IsNash utility profile

/-- Standard pure SPE on every lawful root for a complete-path objective. -/
def IsPurePathStandardSubgamePerfect
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (utility : Outcome → N → V)
    (profile : G.PureProfile) : Prop :=
  G.IsPurePathSubgamePerfectOn objective hNoChance
    system.toSubgameSystem utility profile

/-- Complete path-objective standard SPE is SPE on its underlying lawful
system. -/
theorem IsPurePathStandardSubgamePerfect.toSubgamePerfectOn
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPurePathStandardSubgamePerfect objective hNoChance
        system utility profile) :
    G.IsPurePathSubgamePerfectOn objective hNoChance
      system.toSubgameSystem utility profile :=
  hspe

/-- Complete path-objective standard SPE is Nash at the initial root. -/
theorem IsPurePathStandardSubgamePerfect.isNashAtInit
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPurePathStandardSubgamePerfect objective hNoChance
        system utility profile) :
    (G.pathObjectiveContinuationGameForm objective hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)).IsNash
        utility profile :=
  hspe
    (Arena.HistoryFrom.nil G.base.toArena G.base.init)
    system.toSubgameSystem.init_isRoot

/-- Complete path-objective standard SPE is Nash at every structurally lawful
root. -/
theorem IsPurePathStandardSubgamePerfect.toNashOnLawfulRoots
    {Outcome : Type uOutcome} {V : Type uV}
    [DecidableEq N] [Preorder V]
    (G : ControlledObservedGame N)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (objective :
      G.base.toArena.PathOutcome G.base.init Outcome)
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (utility : Outcome → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPurePathStandardSubgamePerfect objective hNoChance
        system utility profile) :
    ∀ current, G.IsLawfulSubgameRoot current →
      (G.pathObjectiveContinuationGameForm objective hNoChance current).IsNash
        utility profile := by
  intro current hlawful
  exact hspe current (system.complete current hlawful)

/-- An arbitrary indexed continuation evaluator attached to a payoff-free
controlled observed EFG. -/
structure ContinuationSemantics (G : ControlledObservedGame N) where
  /-- Complete strategy space for each player in this semantic mode. -/
  Strategy : N → Type uStrategy
  /-- Horizon, approximation, discount, or total-semantics index. -/
  Horizon : Type uHorizon
  /-- Result type of evaluation. -/
  Outcome : Type uOutcome
  /-- Evaluate a complete profile from a complete history root. -/
  evaluate :
    Horizon →
      G.base.toArena.HistoryFrom G.base.init →
      (∀ i, Strategy i) → Outcome

namespace ContinuationSemantics

variable {G : ControlledObservedGame N}

/-- Complete profiles of one attached continuation semantics. -/
abbrev Profile (S : G.ContinuationSemantics) :=
  ∀ i, S.Strategy i

/-- Reuse the generic indexed continuation layer with an explicit tested-root
predicate. -/
def toIndexedGameFormOn
    (S : G.ContinuationSemantics)
    (roots :
      G.base.toArena.HistoryFrom G.base.init → Prop) :
    IndexedContinuationGameForm N where
  Strategy := S.Strategy
  Horizon := S.Horizon
  Root := G.base.toArena.HistoryFrom G.base.init
  IsDeclaredRoot := roots
  Outcome := S.Outcome
  outcome := S.evaluate

/-- The indexed continuation adapter on an explicit root presentation. -/
def toIndexedGameFormOnPresentation
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation) :
    IndexedContinuationGameForm N :=
  S.toIndexedGameFormOn roots.IsRoot

@[simp]
theorem toIndexedGameFormOnPresentation_outcome
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (horizon : S.Horizon)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (profile : S.Profile) :
    (S.toIndexedGameFormOnPresentation roots).outcome
        horizon root profile =
      S.evaluate horizon root profile :=
  rfl

/-- Nash equilibrium of an attached evaluator on every root selected by an
explicit root presentation at one semantic index. -/
def IsNashOnPresentationAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
    utility horizon profile

/-- Evaluator-relative continuation equilibrium at one semantic index on an
explicit, possibly conservative, lawful subgame system.

This definition makes no claim that `evaluate` is generated by EFG
execution. -/
def IsEvaluatorContinuationEquilibriumOnAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.SubgameSystem)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  (S.toIndexedGameFormOn system.IsRoot).IsNashOnRootsAt
    utility horizon profile

/-- Evaluator-relative continuation equilibrium at one semantic index on
every structurally lawful subgame root.

Complete lawful-root coverage does not turn an arbitrary evaluator into
operational EFG execution. -/
def IsEvaluatorContinuationEquilibriumAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.CompleteSubgameSystem)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  S.IsEvaluatorContinuationEquilibriumOnAt system.toSubgameSystem
    utility horizon profile

/-- The explicit-presentation adapter introduces no new equilibrium
predicate. -/
theorem isNashOnPresentationAt_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) :
    S.IsNashOnPresentationAt roots utility horizon profile ↔
      (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
        utility horizon profile :=
  Iff.rfl

/-- An assumption-explicit indexed continuation morphism preserves and
reflects evaluator-relative continuation equilibrium.

The two `CompleteSubgameSystem`s certify that the tested roots are exactly the
structurally lawful roots of their respective payoff-free observed EFGs. The
morphism field `map_outcome` preserves every continuation outcome for every
profile; `StrategySurjective` supplies reverse coverage of target deviations;
and `DeclaredRootSurjective` supplies reverse coverage of lawful target roots.
`UtilityCompatible` states the final outcome interpretation square. No
compiler or weak serialization receives these properties automatically. -/
theorem isEvaluatorContinuationEquilibriumAt_iff_of_surjective
    {H : ControlledObservedGame N}
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (T : H.ContinuationSemantics)
    (sourceSystem : G.CompleteSubgameSystem)
    (targetSystem : H.CompleteSubgameSystem)
    (f :
      (S.toIndexedGameFormOn
        sourceSystem.toSubgameSystem.IsRoot).Hom
        (T.toIndexedGameFormOn
          targetSystem.toSubgameSystem.IsRoot))
    (sourceUtility :
      S.Horizon →
        G.base.toArena.HistoryFrom G.base.init →
          S.Outcome → N → V)
    (targetUtility :
      T.Horizon →
        H.base.toArena.HistoryFrom H.base.init →
          T.Outcome → N → V)
    (hutility :
      f.UtilityCompatible sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (horizon : S.Horizon)
    (profile : S.Profile) :
    S.IsEvaluatorContinuationEquilibriumAt sourceSystem
        (sourceUtility horizon) horizon profile ↔
      T.IsEvaluatorContinuationEquilibriumAt targetSystem
        (targetUtility (f.horizonMap horizon))
        (f.horizonMap horizon) (f.mapProfile profile) := by
  exact
    f.isNashOnRootsAt_iff_of_surjective
      hutility hstrategy hroot horizon profile

end ContinuationSemantics

end ExtensiveGame.ControlledObservedGame
