/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.SPE

Termination-certified total continuation semantics and pure
subgame-perfect equilibrium for history-indexed observed extensive games.

The general Arena model permits infinite play, so a total terminal payoff
cannot be extracted without an explicit termination assumption. The local
primitive is termination of every pure profile from one accumulated history:

```lean
G.PureTerminatingAt hNoChance current
```

`PureTerminating` quantifies that condition over every
presentation-designated continuation root, while `PureTerminatingOn`
restricts it to an explicit lawful subgame system. Both relative-system and
standard SPE use `PureTerminatingOn`; standard SPE additionally requires a
`CompleteSubgameSystem`, certifying that every structurally lawful root is
selected independently of designated-root metadata. The bound may depend on
the root and profile.
`Arena.stoppedHistoryFrom_eq_of_terminal` proves that any two bounds which have
already terminated produce the same history; consequently the chosen terminal
payoff is independent of the witness fuel.

A strict `ObservedGame.Iso` transports termination, total continuation game
forms, relative-system pure SPE, and complete standard pure SPE in both
directions.

## Main definitions

* `ObservedGame.PureTerminatesFrom` — one profile eventually terminates from
  one accumulated history.
* `ObservedGame.PureTerminating` — all pure profiles terminate from every
  presentation-designated continuation root.
* `ObservedGame.terminalContinuationGameForm` — total `N → U` continuation
  outcome semantics.
* `ObservedGame.IsPureNashOnRoots` — Nash equilibrium at
  every presentation-designated continuation root.
* `ObservedGame.IsPureSubgamePerfectOn` — pure subgame perfection on an
  explicit, possibly conservative lawful `SubgameSystem`.
* `ObservedGame.IsPureStandardSubgamePerfect` — standard SPE on a
  `CompleteSubgameSystem` containing every structurally lawful root.

## Main results

* `Iso.pureTerminatesFrom_iff` and `pureTerminating_iff` — termination
  invariance.
* `Iso.map_terminalHistoryFrom` and `map_terminalPayoffFrom` — exact total
  outcome preservation.
* `Iso.isPureSubgamePerfectOn_iff` — relative-system pure-SPE transfer in both
  directions.
* `Iso.isPureStandardSubgamePerfect_iff` — complete standard-SPE transfer in
  both directions.

## Source boundary

`IsPureStandardSubgamePerfect` is the occurrence-sensitive pure,
termination-certified specialization of standard SPE in
[MFoGT, Def. 6.4.2]. `IsPureSubgamePerfectOn` and
`IsPureNashOnRoots` quantify over caller-selected root families and are
EconCSLib-specific conservative variants; they are not cited as standard SPE
unless the supplied system is complete.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

/-- One explicit fuel reaches a terminal history from `current`. -/
abbrev PureTerminatesAtFuel
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) : Prop :=
  G.toControlledObservedGame.PureTerminatesAtFuel
    profile hNoChance current fuel

/-- Executable profile-indexed termination fuels and their terminal
specification at one accumulated history. -/
abbrev PureTerminationPlanAt
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) :=
  G.toControlledObservedGame.PureTerminationPlanAt hNoChance current

/-- A pure profile eventually reaches a terminal history from `current`. -/
abbrev PureTerminatesFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  G.toControlledObservedGame.PureTerminatesFrom
    profile hNoChance current

/-- Every pure profile terminates from one accumulated history. -/
abbrev PureTerminatingAt
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  G.toControlledObservedGame.PureTerminatingAt hNoChance current

/-- Every pure profile terminates from every presentation-designated
continuation root. -/
abbrev PureTerminatingOnRoots
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.RootPresentation) : Prop :=
  G.toControlledObservedGame.PureTerminatingOnRoots
    hNoChance roots

/-- Every pure profile terminates from each root of one explicit lawful
subgame system. -/
abbrev PureTerminatingOn
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem) : Prop :=
  G.toControlledObservedGame.PureTerminatingOn
    hNoChance system

/-- Termination on all presentation-designated continuations implies
termination on a lawful subgame system when that system is separately proved
presentation-visible. -/
theorem PureTerminatingOnRoots.onSubgameSystem
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.RootPresentation)
    (hterminates : G.PureTerminatingOnRoots hNoChance roots)
    (system : G.SubgameSystem)
    (hvisible : system.IsVisibleIn roots) :
    G.PureTerminatingOn hNoChance system :=
  ControlledObservedGame.PureTerminatingOnRoots.onSubgameSystem
    G.toControlledObservedGame hNoChance roots hterminates
    system hvisible

/-- The history reached at an explicit runtime fuel. -/
abbrev terminalHistoryFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.toControlledObservedGame.terminalHistoryFrom
    profile hNoChance current fuel

/-- The selected eventual history is terminal. -/
theorem terminalHistoryFrom_terminal
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ)
    (hterminal :
      G.PureTerminatesAtFuel profile hNoChance current fuel) :
    G.base.isTerminal
      (G.terminalHistoryFrom profile hNoChance current fuel).1 :=
  G.toControlledObservedGame.terminalHistoryFrom_terminal
    profile hNoChance current fuel hterminal

/-- The selected terminal history equals the result at any other fuel which
has already reached a terminal endpoint. -/
theorem terminalHistoryFrom_eq_of_terminal
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (selectedFuel : ℕ)
    (hselectedTerminal :
      G.PureTerminatesAtFuel profile hNoChance current selectedFuel)
    (fuel : ℕ)
    (hterminal : G.PureTerminatesAtFuel profile hNoChance current fuel) :
    G.terminalHistoryFrom profile hNoChance current selectedFuel =
      G.stoppedHistoryFrom profile hNoChance current fuel :=
  G.toControlledObservedGame.terminalHistoryFrom_eq_of_terminal
    profile hNoChance current selectedFuel hselectedTerminal fuel hterminal

/-- The total terminal payoff of an eventually terminating pure
continuation. -/
def terminalPayoffFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (fuel : ℕ)
    (hterminal :
      G.PureTerminatesAtFuel profile hNoChance current fuel) :
    N → U :=
  G.toControlledObservedGame.terminalOutcomeFrom
    G.base.terminalPayoffOutcome profile hNoChance current fuel hterminal

namespace Iso

variable {G H : ObservedGame N U}

/-- Transport the structural lawfulness of one target root from its inverse
image through a strict observed-EFG isomorphism. -/
def mapLawfulSubgameRoot
    (e : G.Iso H)
    (root : H.base.toArena.HistoryFrom H.base.init)
    (hlawful :
      G.IsLawfulSubgameRoot
        (e.historyIso.stateEquiv.symm root)) :
    H.IsLawfulSubgameRoot root :=
  e.toControlledIso.mapLawfulSubgameRoot root hlawful

/-- Transport a lawful standard-subgame system through a strict observed-EFG
isomorphism.  Roots are pulled back along the history equivalence, while the
singleton and information-set closure laws are transported through the
information-state and continuation equivalences. -/
def mapSubgameSystem
    (e : G.Iso H) (system : G.SubgameSystem) :
    H.SubgameSystem :=
  e.toControlledIso.mapSubgameSystem system

/-- Transport a complete standard-subgame system through a strict
observed-EFG isomorphism. Completeness is preserved because structural
lawfulness is reflected by the inverse isomorphism. -/
def mapCompleteSubgameSystem
    (e : G.Iso H) (system : G.CompleteSubgameSystem) :
    H.CompleteSubgameSystem :=
  e.toControlledIso.mapCompleteSubgameSystem system

/-- Eventual pure termination at corresponding histories is invariant under a
strict observed-EFG isomorphism. -/
theorem pureTerminatesFrom_iff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) :
    G.PureTerminatesFrom profile hNoChanceG current ↔
      H.PureTerminatesFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) := by
  constructor
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    change
      H.base.isTerminal
        (H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) fuel).1
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current fuel)).mp
        hterminal
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    have hmapped :
        H.base.isTerminal
          (e.historyIso.stateEquiv
            (G.stoppedHistoryFrom profile hNoChanceG current fuel)).1 := by
      rw [e.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current fuel]
      exact hterminal
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current fuel)).mpr
        hmapped

/-- Map a root-scoped pure-termination certificate through a strict
observed-EFG isomorphism and an explicit root correspondence. -/
theorem map_pureTerminatingOnRoots
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots)
    (hterminates :
      G.PureTerminatingOnRoots hNoChanceG sourceRoots) :
    H.PureTerminatingOnRoots hNoChanceH targetRoots := by
  intro targetRoot htargetRoot targetProfile
  let sourceRoot := e.historyIso.stateEquiv.symm targetRoot
  let sourceProfile := e.unmapProfile targetProfile
  have hmapRoot :
      e.historyIso.stateEquiv sourceRoot = targetRoot :=
    e.historyIso.stateEquiv.apply_symm_apply targetRoot
  have hsourceRoot : sourceRoots.IsRoot sourceRoot := by
    apply (hroots sourceRoot).mpr
    simpa [hmapRoot] using htargetRoot
  have hsourceTerminates :=
    hterminates sourceRoot hsourceRoot sourceProfile
  have hmapped :=
    (e.pureTerminatesFrom_iff sourceProfile
      hNoChanceG hNoChanceH sourceRoot).mp hsourceTerminates
  simpa [sourceProfile, hmapRoot] using hmapped

/-- Map a pure-termination certificate on one lawful subgame system through a
strict observed-EFG isomorphism. -/
theorem map_pureTerminatingOn
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (hterminates : G.PureTerminatingOn hNoChanceG system) :
    H.PureTerminatingOn hNoChanceH (e.mapSubgameSystem system) := by
  intro targetRoot htargetRoot targetProfile
  let sourceRoot := e.historyIso.stateEquiv.symm targetRoot
  let sourceProfile := e.unmapProfile targetProfile
  have hmapRoot :
      e.historyIso.stateEquiv sourceRoot = targetRoot :=
    e.historyIso.stateEquiv.apply_symm_apply targetRoot
  have hsourceTerminates :=
    hterminates sourceRoot htargetRoot sourceProfile
  have hmapped :=
    (e.pureTerminatesFrom_iff sourceProfile
      hNoChanceG hNoChanceH sourceRoot).mp hsourceTerminates
  simpa [sourceProfile, hmapRoot] using hmapped

/-- Pure termination on explicitly corresponding roots is invariant under a
strict observed-EFG isomorphism. -/
theorem pureTerminatingOnRoots_iff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots) :
    G.PureTerminatingOnRoots hNoChanceG sourceRoots ↔
      H.PureTerminatingOnRoots hNoChanceH targetRoots := by
  constructor
  · exact
      e.map_pureTerminatingOnRoots hNoChanceG hNoChanceH
        sourceRoots targetRoots hroots
  · intro hterminates sourceRoot hsourceRoot sourceProfile
    have htargetRoot :
        targetRoots.IsRoot (e.historyIso.stateEquiv sourceRoot) :=
      (hroots sourceRoot).mp hsourceRoot
    have htargetTerminates :=
      hterminates (e.historyIso.stateEquiv sourceRoot) htargetRoot
        (e.mapProfile sourceProfile)
    exact
      (e.pureTerminatesFrom_iff sourceProfile
        hNoChanceG hNoChanceH sourceRoot).mpr htargetTerminates

/-- Strict history mapping sends a source history reached at terminal fuel to
the target history reached at any terminal fuel. -/
theorem map_terminalHistoryFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel) :
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom profile hNoChanceG current sourceFuel) =
      H.terminalHistoryFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel := by
  have hmappedTerminal :
      H.PureTerminatesAtFuel (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) sourceFuel := by
    change
      H.base.isTerminal
        (H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) sourceFuel).1
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current sourceFuel]
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current sourceFuel)).mp
        hsourceTerminal
  calc
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom profile hNoChanceG current sourceFuel) =
        H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) sourceFuel := by
      exact e.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current sourceFuel
    _ = H.terminalHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) targetFuel :=
      (H.terminalHistoryFrom_eq_of_terminal
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel htargetTerminal
        sourceFuel hmappedTerminal).symm

/-- Strict observed-EFG isomorphisms preserve total eventual terminal payoffs
exactly. -/
theorem map_terminalPayoffFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (sourceFuel targetFuel : ℕ)
    (hsourceTerminal :
      G.PureTerminatesAtFuel profile hNoChanceG current sourceFuel)
    (htargetTerminal :
      H.PureTerminatesAtFuel (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel) :
    H.terminalPayoffFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) targetFuel htargetTerminal =
      G.terminalPayoffFrom profile hNoChanceG current
        sourceFuel hsourceTerminal := by
  change
    H.base.payoff
        (H.terminalHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) targetFuel).1 =
      G.base.payoff
        (G.terminalHistoryFrom profile hNoChanceG current sourceFuel).1
  rw [
    ← e.map_terminalHistoryFrom profile hNoChanceG hNoChanceH
      current sourceFuel targetFuel hsourceTerminal htargetTerminal]
  exact
    e.map_payoff
      (G.terminalHistoryFrom profile hNoChanceG current sourceFuel)
      (G.terminalHistoryFrom_terminal
        profile hNoChanceG current sourceFuel hsourceTerminal)

end Iso

/-! ### Total continuation game forms and pure equilibrium layers -/

/-- Total deterministic continuation semantics at an accumulated history,
given termination of every pure profile from that history. -/
abbrev terminalContinuationGameForm
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (termination : G.PureTerminationPlanAt hNoChance current) :
    GameForm N :=
  G.toControlledObservedGame.terminalObjectiveContinuationGameForm
    G.base.terminalPayoffOutcome hNoChance current termination

/-- Endpoint-payoff continuation is exactly the specialization of the
canonical history-sensitive terminal-objective semantics to
`ExtensiveGame.terminalPayoffOutcome`. -/
theorem terminalContinuationGameForm_eq_terminalObjective
    (G : ObservedGame N U)
    [(state : G.base.State) → Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (termination : G.PureTerminationPlanAt hNoChance current) :
    G.terminalContinuationGameForm hNoChance current termination =
      G.toControlledObservedGame.terminalObjectiveContinuationGameForm
        G.base.terminalPayoffOutcome hNoChance current termination :=
  rfl

/-- Pure Nash equilibrium on every presentation-designated continuation under
total terminal-outcome semantics.

This is the accurate name for the historical predicate that quantified
an explicit `RootPresentation` directly. It is useful for conservative
continuation systems, but is not by itself standard subgame perfection. -/
def IsPureNashOnRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (roots : G.RootPresentation)
    (termination :
      ∀ current, roots.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    ∀ hroot : roots.IsRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (termination current hroot)).IsNash utility profile

/-- Pure subgame perfection on an explicit lawful subgame system under total
terminal-outcome semantics.

Unlike the designated-continuation predicate, the roots here carry the
information-set singleton and closure laws in `SubgameSystem`. The supplied
system may still be a conservative subset of all lawful roots, which is why
the primary name ends in `On`. -/
def IsPureSubgamePerfectOn
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    ∀ hroot : system.IsRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (termination current hroot)).IsNash utility profile

/-- Standard pure subgame-perfect equilibrium on every structurally lawful
subgame root.

The completeness field rules out a conservative root subset: every root
satisfying `IsLawfulSubgameRoot` is tested. -/
def IsPureStandardSubgamePerfect
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  G.IsPureSubgamePerfectOn hNoChance system.toSubgameSystem
    termination utility profile

/-- Subgame perfection on any lawful system is Nash at that system's initial
root. -/
theorem IsPureSubgamePerfectOn.isNashAtInit
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureSubgamePerfectOn hNoChance system termination
        utility profile) :
    (G.terminalContinuationGameForm hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (termination
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.init_isRoot)).IsNash utility profile :=
  hspe
    (Arena.HistoryFrom.nil G.base.toArena G.base.init)
    system.init_isRoot

/-- Subgame perfection on a lawful system implies Nash optimality on every
root selected by that same system. -/
theorem IsPureSubgamePerfectOn.toNashOnSystemRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureSubgamePerfectOn hNoChance system
        termination
        utility profile) :
    ∀ current, ∀ hroot : system.IsRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (termination current hroot)).IsNash
        utility profile := by
  intro current hroot
  exact hspe current hroot

/-- Complete standard SPE is Nash at the initial whole-game root. -/
theorem IsPureStandardSubgamePerfect.isNashAtInit
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        termination utility profile) :
    (G.terminalContinuationGameForm hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (termination
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.toSubgameSystem.init_isRoot)).IsNash utility profile :=
  IsPureSubgamePerfectOn.isNashAtInit
    G hNoChance system.toSubgameSystem termination
    utility profile hspe

/-- Complete standard SPE is Nash at every structurally lawful subgame root. -/
theorem IsPureStandardSubgamePerfect.toNashOnLawfulRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        termination utility profile) :
    ∀ current, ∀ hlawful : G.IsLawfulSubgameRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (termination current
          (system.complete current hlawful))).IsNash
        utility profile := by
  intro current hlawful
  exact hspe current (system.complete current hlawful)

/-- A complete standard SPE is, definitionally, subgame-perfect on its
underlying complete lawful system. -/
theorem IsPureStandardSubgamePerfect.toSubgamePerfectOn
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (termination :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChance current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        termination utility profile) :
    G.IsPureSubgamePerfectOn hNoChance system.toSubgameSystem
      termination utility profile :=
  hspe

namespace Iso

variable {G H : ObservedGame N U}

/-- A strict observed-EFG isomorphism induces a strict game-form isomorphism
between corresponding total continuation games. -/
def terminalContinuationGameFormIso
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (e.historyIso.stateEquiv current)) :
    (G.terminalContinuationGameForm
      hNoChanceG current terminationG).Iso
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv current) terminationH) where
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      (e.map_terminalPayoffFrom profile hNoChanceG hNoChanceH current
        (terminationG.fuel profile)
        (terminationH.fuel (e.mapProfile profile))
        (terminationG.terminal profile)
        (terminationH.terminal (e.mapProfile profile))).symm

/-- Total continuation game-form isomorphism preserves a shared
outcome-utility interpretation. -/
theorem terminalContinuationGameFormIso_utilityCompatible
    {V : Type uV}
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : (N → U) → N → V)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (terminationG : G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      H.PureTerminationPlanAt hNoChanceH
        (e.historyIso.stateEquiv current)) :
    GameForm.Iso.UtilityCompatible
      (e.terminalContinuationGameFormIso hNoChanceG hNoChanceH current
        terminationG terminationH)
      utility utility := by
  intro outcome i
  rfl

/-- Strict structural observed-EFG isomorphism preserves total pure-strategy
Nash equilibrium on explicitly corresponding root presentations in both
directions. -/
theorem isPureNashOnRoots_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots)
    (terminationG :
      ∀ current, sourceRoots.IsRoot current →
        G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      ∀ current, targetRoots.IsRoot current →
        H.PureTerminationPlanAt hNoChanceH current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureNashOnRoots hNoChanceG sourceRoots
        terminationG utility profile ↔
      H.IsPureNashOnRoots hNoChanceH targetRoots
        terminationH
        utility (e.mapProfile profile) := by
  constructor
  · intro hspe targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      e.historyIso.stateEquiv.surjective targetRoot
    have hsourceRoot : sourceRoots.IsRoot sourceRoot :=
      (hroots sourceRoot).mpr htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot)
            ((hroots sourceRoot).mp hsourceRoot)))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot)
            ((hroots sourceRoot).mp hsourceRoot)))
        profile |>.mp hsourceNash
    change
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv sourceRoot)
        (terminationH
          (e.historyIso.stateEquiv sourceRoot)
          ((hroots sourceRoot).mp hsourceRoot))).IsNash
        utility (e.mapProfile profile) at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        targetRoots.IsRoot (e.historyIso.stateEquiv sourceRoot) :=
      (hroots sourceRoot).mp hsourceRoot
    have htargetNash :=
      hspe (e.historyIso.stateEquiv sourceRoot) htargetRoot
    exact
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        profile |>.mpr htargetNash

/-- Strict structural observed-EFG isomorphism transports a lawful subgame
system and preserves total pure-strategy equilibrium on that system in both
directions. -/
theorem isPureSubgamePerfectOn_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (system : G.SubgameSystem)
    (terminationG :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      ∀ current, (e.mapSubgameSystem system).IsRoot current →
        H.PureTerminationPlanAt hNoChanceH current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureSubgamePerfectOn
        hNoChanceG system terminationG utility profile ↔
      H.IsPureSubgamePerfectOn hNoChanceH
        (e.mapSubgameSystem system)
        terminationH
        utility (e.mapProfile profile) := by
  constructor
  · intro hspe targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      e.historyIso.stateEquiv.surjective targetRoot
    have hsourceRoot : system.IsRoot sourceRoot := by
      change
        system.IsRoot
          (e.historyIso.stateEquiv.symm
            (e.historyIso.stateEquiv sourceRoot))
        at htargetRoot
      simpa using htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot)
            htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot)
            htargetRoot))
        profile |>.mp hsourceNash
    change
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv sourceRoot)
        (terminationH
          (e.historyIso.stateEquiv sourceRoot)
          htargetRoot)).IsNash
        utility (e.mapProfile profile) at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        (e.mapSubgameSystem system).IsRoot
          (e.historyIso.stateEquiv sourceRoot) := by
      change
        system.IsRoot
          (e.historyIso.stateEquiv.symm
            (e.historyIso.stateEquiv sourceRoot))
      simpa
    have htargetNash :=
      hspe (e.historyIso.stateEquiv sourceRoot) htargetRoot
    exact
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (terminationG sourceRoot hsourceRoot)
          (terminationH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        profile |>.mpr htargetNash

/-- Strict observed-EFG isomorphisms preserve complete standard pure SPE in
both directions. -/
theorem isPureStandardSubgamePerfect_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (system : G.CompleteSubgameSystem)
    (terminationG :
      ∀ current, system.IsRoot current →
        G.PureTerminationPlanAt hNoChanceG current)
    (terminationH :
      ∀ current, (e.mapCompleteSubgameSystem system).IsRoot current →
        H.PureTerminationPlanAt hNoChanceH current)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureStandardSubgamePerfect
        hNoChanceG system terminationG utility profile ↔
      H.IsPureStandardSubgamePerfect hNoChanceH
        (e.mapCompleteSubgameSystem system)
        terminationH
        utility (e.mapProfile profile) := by
  simpa [IsPureStandardSubgamePerfect, mapCompleteSubgameSystem] using
    e.isPureSubgamePerfectOn_iff
      hNoChanceG hNoChanceH system.toSubgameSystem
      terminationG terminationH utility profile

end Iso

end ExtensiveGame.ObservedGame
