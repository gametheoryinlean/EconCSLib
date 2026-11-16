/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Game

A history-indexed observed extensive-game layer over `ExtensiveGame`.

The base game continues to own states, dependent actions, transitions, movers,
and payoffs.  This wrapper adds an observation for every player at every
history and a public observation at every history.  Player-controlled histories
also map to decision information states, which determine abstract action types.
An explicit equivalence identifies those abstract actions with the legal base
actions.

This indexing makes information-set consistency structural: a pure strategy
has type

```lean
(I : G.RepresentedInfo i) → G.InfoAction i I.1
```

and therefore cannot inspect the concrete history after receiving `I`.

This core module defines player-controlled no-chance execution. The
`Chance` and `Behavior` extension modules add normalized
chance kernels and behavioral strategies without changing the base history or
information-indexed pure-strategy interfaces.

## Main definitions

* `ExtensiveGame.ObservedGame` — observations and information-indexed actions
  over a base extensive game.
* `ObservedGame.ofControlledObservedGame` and `toControlledObservedGame` —
  attach an arbitrary state payoff to, or erase it from, the payoff-free
  controlled observed carrier.
* `ObservedGame.relabelPlayers` and `relabelPureProfileEquiv` — reindex the
  player carrier, payoff coordinates, and dependent pure profiles along an
  equivalence.
* `ObservedGame.historyInformation` — the legacy all-history information
  carrier with an explicit public projection.
* `ObservedGame.decisionHistoryInformation` — full-history private observation
  with decision-only information states.
* `ObservedGame.completeInformation` — the canonical root-free
  decision-history complete-information carrier of an ordinary
  `ExtensiveGame`.
* `ObservedGame.ContinuationRootPresentation.initialOnly` and
  `.allHistories` — explicit, orthogonal choices of presentation-designated
  continuation roots.
* `ObservedGame.PureStrategy` and `PureProfile` — game-bound contingent plans.
* `PureProfile.toHistoryPolicy` — terminal-aware execution of a no-chance
  profile.
* `ObservedGame.RootPresentation` — external history roots selected for one
  continuation analysis; lawfulness as standard subgames is separate.
* `ObservedGame.IsLawfulSubgameRoot`, `SubgameSystem`, and
  `CompleteSubgameSystem` — compatibility names projected definitionally from
  the canonical payoff-free `ControlledObservedGame` infrastructure.
* `ObservedGame.stoppedHistoryFrom`, `stoppedPayoffFrom`, `stoppedHistory`, and
  `stoppedPayoff` — continuation and root profile semantics.
-/

namespace ExtensiveGame

universe uN uU uA uS uO uI uP

/-- A history-indexed observation and information-action layer over an
extensive game.

`Observation` is defined for every player at every history, including histories
where that player does not move.  `observe_public` says that each player's
observation refines the public observation.  `InfoState` indexes only
player-decision information; `infoAt` and `actionEquiv` are therefore required
only when the history is controlled by the given player. -/
structure ObservedGame (N : Type uN) (U : Type uU) where
  /-- The underlying transition, mover, and payoff data. -/
  base : ExtensiveGame.{uN, uU, uS, uA} N U
  /-- Player `i`'s observation type, defined at every history. -/
  Observation : N → Type uO
  /-- Public observation type. -/
  PublicObservation : Type uP
  /-- Player `i`'s observation after a complete history. -/
  observe :
    (i : N) → base.toArena.HistoryFrom base.init → Observation i
  /-- The public observation after a complete history. -/
  publicObserve :
    base.toArena.HistoryFrom base.init → PublicObservation
  /-- Forget private observation data and retain its public component. -/
  publicOf : (i : N) → Observation i → PublicObservation
  /-- Every player's observation refines the public observation. -/
  observe_public :
    ∀ (i : N) (h : base.toArena.HistoryFrom base.init),
      publicOf i (observe i h) = publicObserve h
  /-- Player `i`'s decision information-state type. -/
  InfoState : N → Type uI
  /-- Project a complete decision-information/memory state to its current
  observable signal.  This map need not be injective: an information state
  may retain memory beyond the current signal. -/
  infoObserve : (i : N) → InfoState i → Observation i
  /-- The decision information state at a genuine decision history controlled
  by player `i`. -/
  infoAt :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N),
      base.mover h.1 = some i →
        base.toArena.IsDecision h.1 → InfoState i
  /-- Decision information projects to the acting player's current
  observation.  This does not assert that `InfoState` contains no additional
  memory. -/
  infoAt_observe :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover h.1 = some i)
      (hdecision : base.toArena.IsDecision h.1),
      infoObserve i (infoAt h i hmover hdecision) = observe i h
  /-- Abstract actions available at a player information state. -/
  InfoAction : (i : N) → InfoState i → Type uA
  /-- Abstract information-state actions are exactly the legal base actions at
  each player-controlled history represented by that state. -/
  actionEquiv :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover h.1 = some i)
      (hdecision : base.toArena.IsDecision h.1),
      InfoAction i (infoAt h i hmover hdecision) ≃ base.Action h.1

namespace ObservedGame

variable {N M U : Type*} (G : ObservedGame N U)

/-- Forget the state-payoff interpretation, retaining exactly the payoff-free
controlled dynamics and observation/information structure.

This is the additive migration projection to the canonical root-free carrier.
All state, action, transition, mover, observation, information, and
information-action data are preserved definitionally. -/
abbrev toControlledObservedGame (G : ObservedGame N U) :
    ControlledObservedGame N where
  base := G.base.toControlledGame
  Observation := G.Observation
  PublicObservation := G.PublicObservation
  observe := G.observe
  publicObserve := G.publicObserve
  publicOf := G.publicOf
  observe_public := G.observe_public
  InfoState := G.InfoState
  infoObserve := G.infoObserve
  infoAt := G.infoAt
  infoAt_observe := G.infoAt_observe
  InfoAction := G.InfoAction
  actionEquiv := G.actionEquiv

@[simp]
theorem toControlledObservedGame_base
    (G : ObservedGame N U) :
    G.toControlledObservedGame.base = G.base.toControlledGame :=
  rfl

/-- Package the information state at one concrete observed decision as a
represented strategy coordinate. -/
abbrev representedInfoAt :=
  G.toControlledObservedGame.representedInfoAt

/-- Add an arbitrary endpoint-state payoff interpretation to a payoff-free
controlled observed game.

This is the downstream inverse construction to
`ObservedGame.toControlledObservedGame`: it preserves the entire controlled
observation/information carrier definitionally and adds only the supplied
state payoff. Path objectives and solution concepts remain external. -/
def ofControlledObservedGame
    (G : ControlledObservedGame N)
    (payoff : G.base.State → N → U) :
    ObservedGame N U where
  base := ExtensiveGame.ofControlledGame G.base payoff
  Observation := G.Observation
  PublicObservation := G.PublicObservation
  observe := G.observe
  publicObserve := G.publicObserve
  publicOf := G.publicOf
  observe_public := G.observe_public
  InfoState := G.InfoState
  infoObserve := G.infoObserve
  infoAt := G.infoAt
  infoAt_observe := G.infoAt_observe
  InfoAction := G.InfoAction
  actionEquiv := G.actionEquiv

@[simp]
theorem ofControlledObservedGame_toControlledObservedGame
    (G : ControlledObservedGame N)
    (payoff : G.base.State → N → U) :
    (ofControlledObservedGame G payoff).toControlledObservedGame = G :=
  rfl

@[simp]
theorem ofControlledObservedGame_payoff
    (G : ControlledObservedGame N)
    (payoff : G.base.State → N → U)
    (state : G.base.State) (i : N) :
    (ofControlledObservedGame G payoff).base.payoff state i =
      payoff state i :=
  rfl

/-- Reattaching an observed game's existing state payoff after the payoff-free
projection recovers the original observed game. -/
@[simp]
theorem ofControlledObservedGame_toControlledObservedGame_payoff
    (G : ObservedGame N U) :
    ofControlledObservedGame
        G.toControlledObservedGame G.base.payoff =
      G := by
  cases G
  rfl

/-- Relabel an observed game's player carrier along an equivalence.

The controlled observation/information carrier uses the canonical payoff-free
relabeling. The endpoint payoff vector is reindexed by the same equivalence,
so no player-specific outcome coordinate is lost. -/
def relabelPlayers
    (G : ObservedGame N U)
    (e : M ≃ N) :
    ObservedGame M U :=
  ofControlledObservedGame
    (G.toControlledObservedGame.relabelPlayers e)
    (fun state i => G.base.payoff state (e i))

@[simp]
theorem relabelPlayers_toControlledObservedGame
    (G : ObservedGame N U)
    (e : M ≃ N) :
    (G.relabelPlayers e).toControlledObservedGame =
      G.toControlledObservedGame.relabelPlayers e :=
  rfl

@[simp]
theorem relabelPlayers_payoff
    (G : ObservedGame N U)
    (e : M ≃ N)
    (state : G.base.State) (i : M) :
    (G.relabelPlayers e).base.payoff state i =
      G.base.payoff state (e i) :=
  rfl

/-- Presentation-level selection of designated continuation roots for an
ordinary extensive game.

This is deliberately weaker than `ObservedGame.SubgameSystem`: it records
which roots a presentation exposes, but carries no standard-subgame
lawfulness claim. Keeping it separate from observation data makes the root
choice explicit at every smart-constructor call. -/
structure ContinuationRootPresentation (base : ExtensiveGame N U) where
  /-- Complete histories exposed as continuation roots. -/
  IsRoot : base.toArena.HistoryFrom base.init → Prop
  /-- The initial empty history is always exposed. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil base.toArena base.init)

namespace ContinuationRootPresentation

variable {base : ExtensiveGame N U}

/-- Root presentations are determined by their root predicate; the initial
root certificate is propositional. -/
@[ext]
theorem ext (first second : ContinuationRootPresentation base)
    (hroot : first.IsRoot = second.IsRoot) :
    first = second := by
  cases first
  cases second
  cases hroot
  rfl

/-- Expose only the initial history as a presentation-designated continuation
root. No later history is selected implicitly. -/
def initialOnly (base : ExtensiveGame N U) :
    ContinuationRootPresentation base where
  IsRoot := fun history =>
    history = Arena.HistoryFrom.nil base.toArena base.init
  init_isRoot := rfl

/-- Expose every legal complete history as a presentation-designated
continuation root.

This does not claim that every history is a lawful standard-subgame root.
Use a `SubgameSystem` (or `CompleteSubgameSystem`) when that stronger semantic
claim is required. -/
def allHistories (base : ExtensiveGame N U) :
    ContinuationRootPresentation base where
  IsRoot := fun _history => True
  init_isRoot := trivial

@[simp]
theorem initialOnly_isRoot_iff
    (history : base.toArena.HistoryFrom base.init) :
    (initialOnly base).IsRoot history ↔
      history = Arena.HistoryFrom.nil base.toArena base.init :=
  Iff.rfl

@[simp]
theorem allHistories_isRoot
    (history : base.toArena.HistoryFrom base.init) :
    (allHistories base).IsRoot history :=
  trivial

end ContinuationRootPresentation

/-- A root presentation for an already constructed observed game. -/
abbrev RootPresentation (G : ObservedGame N U) :=
  ContinuationRootPresentation G.base

/-- Migrate a legacy root presentation to the root-free payoff-free observed
carrier. -/
def ContinuationRootPresentation.toControlled
    {base : ExtensiveGame N U}
    (roots : ContinuationRootPresentation base)
    (G : ObservedGame N U)
    (hbase : G.base = base) :
    G.toControlledObservedGame.ContinuationRootPresentation := by
  subst hbase
  exact
    { IsRoot := roots.IsRoot
      init_isRoot := roots.init_isRoot }

/-- An `ObservedGame` root presentation coerces losslessly to the canonical
payoff-free root presentation of its controlled projection.

This keeps established dot-notation calls such as
`system.IsVisibleIn roots` compatible after lawful subgame systems are
definitionally owned by `ControlledObservedGame`. -/
instance rootPresentationCoeToControlled (G : ObservedGame N U) :
    Coe G.RootPresentation
      G.toControlledObservedGame.ContinuationRootPresentation where
  coe roots :=
    roots.toControlled G rfl

@[simp]
theorem rootPresentation_coe_isRoot
    {G : ObservedGame N U}
    (roots : G.RootPresentation)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    ((roots :
      G.toControlledObservedGame.ContinuationRootPresentation).IsRoot root) ↔
      roots.IsRoot root :=
  Iff.rfl

namespace CompleteInformation

/-- The complete-history carrier used by the canonical complete-information
presentation. -/
abbrev History (base : ExtensiveGame N U) :=
  base.toArena.HistoryFrom base.init

/-- An orthogonal public projection for a history-information presentation.

Private observation and decision information remain the complete history;
this component controls only which public quotient of that history is
exposed. -/
structure PublicObservationPresentation
    (base : ExtensiveGame N U) where
  /-- Public observation carrier. -/
  PublicObservation : Type uP
  /-- Public projection of a complete history. -/
  publicObserve : History base → PublicObservation

namespace PublicObservationPresentation

variable {base : ExtensiveGame N U}

/-- Public-observation presentations are determined by their carrier and
history projection. -/
@[ext]
theorem ext
    (first second : PublicObservationPresentation base)
    (hcarrier :
      first.PublicObservation = second.PublicObservation)
    (hprojection :
      HEq first.publicObserve second.publicObserve) :
    first = second := by
  cases first
  cases second
  cases hcarrier
  cases hprojection
  rfl

/-- Keep the entire complete history public. -/
def fullHistory (base : ExtensiveGame N U) :
    PublicObservationPresentation base where
  PublicObservation := History base
  publicObserve := fun history => history

/-- Hide all history detail from the public observation. -/
def trivial (base : ExtensiveGame N U) :
    PublicObservationPresentation base where
  PublicObservation := Unit
  publicObserve := fun _history => ()

@[simp]
theorem fullHistory_publicObserve
    (base : ExtensiveGame N U) (history : History base) :
    (fullHistory base).publicObserve history = history :=
  rfl

@[simp]
theorem trivial_publicObserve
    (base : ExtensiveGame N U) (history : History base) :
    (trivial base).publicObserve history = () :=
  rfl

end PublicObservationPresentation

/-- Player `i`'s legacy all-history information state.

This intentionally includes histories where `i` does not move. Consequently
`PureStrategy i` asks for an action at every complete history; callers whose
action family is empty away from `i`'s decision histories should instead use
a decision-history presentation. -/
abbrev InfoState (base : ExtensiveGame N U) (_i : N) :=
  History base

/-- Endpoint actions for a legacy all-history information carrier. -/
abbrev InfoAction (base : ExtensiveGame N U) (i : N)
    (information : InfoState base i) :=
  base.Action information.1

/-- A complete history whose mover label is player `i`.

This is the canonical perfect-information strategy domain. Chance,
other-player, and terminal histories are excluded, even when an unconstrained
base labels a terminal endpoint with player `i`. -/
abbrev DecisionHistory (base : ExtensiveGame N U) (i : N) :=
  {history : History base //
    base.mover history.1 = some i ∧
      base.toArena.IsDecision history.1}

/-- Legal actions at one decision history of player `i`. -/
abbrev DecisionAction (base : ExtensiveGame N U) (i : N)
    (information : DecisionHistory base i) :=
  base.Action information.1.1

end CompleteInformation

/-- Root-free form of the legacy all-history information presentation.

Continuation roots are supplied later through a `RootPresentation`; this
constructor chooses only observation and information data. -/
abbrev historyInformation
    (base : ExtensiveGame N U)
    (publicPresentation :
      CompleteInformation.PublicObservationPresentation base) :
    ObservedGame N U where
  base := base
  Observation := fun _i => CompleteInformation.History base
  PublicObservation := publicPresentation.PublicObservation
  observe := fun _i history => history
  publicObserve := publicPresentation.publicObserve
  publicOf :=
    fun _i observation => publicPresentation.publicObserve observation
  observe_public := fun _i _history => rfl
  InfoState := CompleteInformation.InfoState base
  infoObserve := fun _i information => information
  infoAt := fun history _i _hmover _hnonterminal => history
  infoAt_observe :=
    fun _history _i _hmover _hnonterminal => rfl
  InfoAction := CompleteInformation.InfoAction base
  actionEquiv :=
    fun _history _i _hmover _hnonterminal => Equiv.refl _

/-- Root-free decision-history complete-information presentation.

Player `i`'s information states are exactly the complete histories controlled
by `i`. The result contains no analysis-root choice; pair it with an explicit
`RootPresentation` when constructing continuation semantics. -/
abbrev decisionHistoryInformation
    (base : ExtensiveGame N U)
    (publicPresentation :
      CompleteInformation.PublicObservationPresentation base) :
    ObservedGame N U where
  base := base
  Observation := fun _i => CompleteInformation.History base
  PublicObservation := publicPresentation.PublicObservation
  observe := fun _i history => history
  publicObserve := publicPresentation.publicObserve
  publicOf :=
    fun _i observation => publicPresentation.publicObserve observation
  observe_public := fun _i _history => rfl
  InfoState := CompleteInformation.DecisionHistory base
  infoObserve := fun _i information => information.1
  infoAt := fun history _i hmover hnonterminal =>
    ⟨history, hmover, hnonterminal⟩
  infoAt_observe :=
    fun _history _i _hmover _hnonterminal => rfl
  InfoAction := CompleteInformation.DecisionAction base
  actionEquiv :=
    fun _history _i _hmover _hnonterminal => Equiv.refl _

/-- Canonical root-free complete-information presentation of an ordinary
state-payoff extensive game. -/
abbrev completeInformation
    (base : ExtensiveGame N U) :
    ObservedGame N U :=
  decisionHistoryInformation base
    (CompleteInformation.PublicObservationPresentation.fullHistory base)

/-- `current` extends `root` in the occurrence-sensitive history unfolding.

This is a compatibility name for the canonical payoff-free predicate on
`G.toControlledObservedGame`; state payoffs play no role. -/
abbrev IsContinuationOf
    (root current : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  G.toControlledObservedGame.IsContinuationOf root current

/-- Every history is its own payoff-free continuation. -/
theorem IsContinuationOf.refl
    (root : G.base.toArena.HistoryFrom G.base.init) :
    G.IsContinuationOf root root :=
  ControlledObservedGame.IsContinuationOf.refl
    G.toControlledObservedGame root

/-- Compatibility name for the canonical payoff-free lawful-subgame-root
predicate on `G.toControlledObservedGame`. -/
abbrev IsLawfulSubgameRoot
    (root : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  G.toControlledObservedGame.IsLawfulSubgameRoot root

/-- Compatibility name for a payoff-free selected lawful-subgame system. -/
abbrev SubgameSystem :=
  G.toControlledObservedGame.SubgameSystem

namespace SubgameSystem

variable {G : ObservedGame N U}

/-- Every selected root satisfies the canonical payoff-free lawfulness
predicate. -/
def isLawful (system : G.SubgameSystem)
    {root : G.base.toArena.HistoryFrom G.base.init}
    (hroot : system.IsRoot root) :
    G.IsLawfulSubgameRoot root :=
  ControlledObservedGame.SubgameSystem.isLawful system hroot

/-- Whether every root in a lawful system is also exposed by the
presentation's designated-continuation metadata.

This is intentionally a property rather than a field: mathematical subgame
lawfulness and standard SPE do not depend on presentation visibility. -/
def IsVisibleIn (system : G.SubgameSystem)
    (roots : G.RootPresentation) : Prop :=
  ∀ root, system.IsRoot root → roots.IsRoot root

/-- Derived compatibility accessor for the proper-root singleton condition. -/
theorem root_information_singleton (system : G.SubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (hroot : system.IsRoot root)
    (hproper :
      root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init) :
    ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (hdecision : G.base.toArena.IsDecision root.1)
      (other : G.base.toArena.HistoryFrom G.base.init)
      (hother : G.base.mover other.1 = some i)
      (hother_decision : G.base.toArena.IsDecision other.1),
      G.infoAt root i hmover hdecision =
          G.infoAt other i hother hother_decision →
        other = root :=
  ControlledObservedGame.SubgameSystem.root_information_singleton
    system root hroot hproper

/-- Derived compatibility accessor for information-set closure. -/
theorem information_closed (system : G.SubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (hroot : system.IsRoot root) :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (hdecision : G.base.toArena.IsDecision current.1)
        (other : G.base.toArena.HistoryFrom G.base.init)
        (hother : G.base.mover other.1 = some i)
        (hother_decision : G.base.toArena.IsDecision other.1),
        G.infoAt current i hmover hdecision =
            G.infoAt other i hother hother_decision →
          G.IsContinuationOf root other :=
  ControlledObservedGame.SubgameSystem.information_closed
    system root hroot

end SubgameSystem

/-- The initial history is always a lawful subgame root: it represents the
whole game, and every complete history lies in its continuation. This remains
true when an imperfect-recall presentation reuses the initial decision
information state later in play. -/
theorem init_isLawfulSubgameRoot (G : ObservedGame N U) :
    G.IsLawfulSubgameRoot
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) :=
  ControlledObservedGame.init_isLawfulSubgameRoot
    G.toControlledObservedGame

/-- The smallest lawful subgame system selects only the whole-game initial
root. This is independent of which additional roots the presentation
designates. -/
def SubgameSystem.initialOnly (G : ObservedGame N U) :
    G.SubgameSystem :=
  ControlledObservedGame.SubgameSystem.initialOnly
    G.toControlledObservedGame

@[simp]
theorem SubgameSystem.initialOnly_isRoot_iff
    (G : ObservedGame N U)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    (SubgameSystem.initialOnly G).IsRoot root ↔
      root = Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  ControlledObservedGame.SubgameSystem.initialOnly_isRoot_iff
    G.toControlledObservedGame root

/-- Compatibility name for a complete payoff-free lawful-subgame system. -/
abbrev CompleteSubgameSystem :=
  G.toControlledObservedGame.CompleteSubgameSystem

namespace CompleteSubgameSystem

variable {G : ObservedGame N U}

/-- A complete system selects exactly the structurally lawful roots. -/
theorem isRoot_iff_isLawful (system : G.CompleteSubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    system.toSubgameSystem.IsRoot root ↔
      G.IsLawfulSubgameRoot root :=
  ControlledObservedGame.CompleteSubgameSystem.isRoot_iff_isLawful
    system root

/-- The canonical complete system selects exactly the structurally lawful
roots. It exists for every observed EFG and does not inspect designated-root
metadata. -/
def canonical (G : ObservedGame N U) : G.CompleteSubgameSystem :=
  ControlledObservedGame.CompleteSubgameSystem.canonical
    G.toControlledObservedGame

end CompleteSubgameSystem

/-- A represented history witnessing that `information` is a reachable
decision information state for player `i`.

This witness belongs to the core observed-game vocabulary: representation is
independent of any later recall, finiteness, or equilibrium hypothesis. -/
abbrev DecisionInfoWitness
    (G : ObservedGame N U) (i : N)
    (information : G.InfoState i) :=
  G.toControlledObservedGame.DecisionInfoWitness i information

/-- Decision-information values represented by at least one concrete player
decision. -/
abbrev RepresentedInfo (i : N) :=
  G.toControlledObservedGame.RepresentedInfo i

/-- Every represented observed-game information coordinate has an abstract
legal action. -/
theorem representedInfo_nonempty_infoAction
    (i : N) (information : G.RepresentedInfo i) :
    Nonempty (G.InfoAction i information.1) :=
  G.toControlledObservedGame.representedInfo_nonempty_infoAction
    i information

/-- A game-bound pure strategy for player `i`: one abstract action at every
information state, with no concrete history argument. -/
abbrev PureStrategy (i : N) : Type _ :=
  G.toControlledObservedGame.PureStrategy i

/-- A pure-strategy profile for all players. -/
abbrev PureProfile : Type _ :=
  G.toControlledObservedGame.PureProfile

/-- Pure observed-game profiles are invariant under bijective player
renaming, up to dependent-function reindexing. -/
def relabelPureProfileEquiv (e : M ≃ N) :
    (G.relabelPlayers e).PureProfile ≃ G.PureProfile :=
  G.toControlledObservedGame.relabelPureProfileEquiv e

/-- The legal base action prescribed by a pure strategy at a concrete history
controlled by player `i`. -/
def PureStrategy.actionAt {i : N} (σ : G.PureStrategy i)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i)
    (hdecision : G.base.toArena.IsDecision h.1) :
    G.base.Action h.1 :=
  ControlledObservedGame.PureStrategy.actionAt
    G.toControlledObservedGame σ h hmover hdecision

/-- The legal base action prescribed by a profile at a concrete
player-controlled history. -/
def PureProfile.actionAt (σ : G.PureProfile)
    (h : G.base.toArena.HistoryFrom G.base.init) (i : N)
    (hmover : G.base.mover h.1 = some i)
    (hdecision : G.base.toArena.IsDecision h.1) :
    G.base.Action h.1 :=
  ObservedGame.PureStrategy.actionAt
    G (σ i) h hmover hdecision

/-- Equal information states force a pure profile to make the same packaged
abstract choice.  Packaging the action with its dependent information-state
index states constancy without choosing a transport between action types. -/
theorem PureProfile.choice_eq_of_infoState_eq
    (σ : G.PureProfile) (i : N)
    (h k : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i)
    (kmover : G.base.mover k.1 = some i)
    (hdecision : G.base.toArena.IsDecision h.1)
    (kdecision : G.base.toArena.IsDecision k.1)
    (hsame :
      G.infoAt h i hmover hdecision =
        G.infoAt k i kmover kdecision) :
    (⟨G.toControlledObservedGame.representedInfoAt h i hmover hdecision,
        σ i (G.toControlledObservedGame.representedInfoAt h i hmover hdecision)⟩ :
      Σ I : G.RepresentedInfo i, G.InfoAction i I.1) =
    ⟨G.toControlledObservedGame.representedInfoAt k i kmover kdecision,
      σ i (G.toControlledObservedGame.representedInfoAt k i kmover kdecision)⟩ :=
  ControlledObservedGame.PureProfile.choice_eq_of_infoState_eq
    G.toControlledObservedGame σ i h k hmover kmover
      hdecision kdecision hsame

/-- Equal decision information states imply equal public observations at the
represented histories. -/
theorem publicObserve_eq_of_infoAt_eq
    (i : N) (h k : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i)
    (kmover : G.base.mover k.1 = some i)
    (hdecision : G.base.toArena.IsDecision h.1)
    (kdecision : G.base.toArena.IsDecision k.1)
    (hsame :
      G.infoAt h i hmover hdecision =
        G.infoAt k i kmover kdecision) :
    G.publicObserve h = G.publicObserve k :=
  ControlledObservedGame.publicObserve_eq_of_infoAt_eq
    G.toControlledObservedGame i h k hmover kmover
      hdecision kdecision hsame

/-- The mover option at a nonterminal history is inhabited in a no-chance
game. -/
abbrev moverIsSome (hNoChance : G.base.NoChanceOnHistories)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) :
    (G.base.mover h.1).isSome = true :=
  ControlledObservedGame.moverIsSome
    (G := G.toControlledObservedGame)
    hNoChance h hnonterminal

/-- The strategic player controlling a nonterminal history in a no-chance
game. -/
abbrev playerAt (hNoChance : G.base.NoChanceOnHistories)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) : N :=
  ControlledObservedGame.playerAt
    (G := G.toControlledObservedGame)
    hNoChance h hnonterminal

/-- `playerAt` recovers the player stored in the base mover field. -/
theorem mover_playerAt (hNoChance : G.base.NoChanceOnHistories)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) :
    G.base.mover h.1 =
      some (G.playerAt hNoChance h hnonterminal) :=
  ControlledObservedGame.mover_playerAt
    (G := G.toControlledObservedGame)
    hNoChance h hnonterminal

/-- Convert a pure profile into a terminal-aware history policy when the base
game has no chance nodes. -/
abbrev PureProfile.toHistoryPolicy (σ : G.PureProfile)
    (hNoChance : G.base.NoChanceOnHistories) :
    G.base.toArena.HistoryPolicy G.base.init :=
  ControlledObservedGame.PureProfile.toHistoryPolicy
    σ hNoChance

/-- At a player-controlled history, profile execution uses exactly
`PureProfile.actionAt`. -/
theorem PureProfile.toHistoryPolicy_of_mover
    (σ : G.PureProfile) (hNoChance : G.base.NoChanceOnHistories)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) (i : N)
    (hmover : G.base.mover h.1 = some i) :
    σ.toHistoryPolicy G hNoChance h hnonterminal =
      σ.actionAt G h i hmover
        (G.base.toArena.isDecision_of_not_isTerminal h.1 hnonterminal) := by
  simpa only [PureProfile.actionAt] using
    (ControlledObservedGame.PureProfile.toHistoryPolicy_of_mover
      σ hNoChance h hnonterminal i hmover)

/-- Continue executing a no-chance pure profile from an accumulated history,
stopping at a terminal endpoint or when `fuel` is exhausted. -/
def stoppedHistoryFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) (fuel : ℕ) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.base.toArena.stoppedHistoryFrom
    (σ.toHistoryPolicy G hNoChance) current fuel

/-- Return the terminal payoff reached by continuing a no-chance pure profile
from an accumulated history, or `none` when the supplied fuel expires first. -/
def stoppedPayoffFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init) (fuel : ℕ) :
    Option (N → U) :=
  let result := G.stoppedHistoryFrom σ hNoChance current fuel
  if G.base.isTerminal result.1 then
    some (G.base.payoff result.1)
  else
    none

/-- Execute a no-chance pure profile from the initial empty history, stopping
at a terminal endpoint or when `fuel` is exhausted. -/
def stoppedHistory
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChanceOnHistories) (fuel : ℕ) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.stoppedHistoryFrom σ hNoChance
    (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel

/-- Return the terminal payoff reached by a no-chance pure profile, or `none`
if its execution exhausts the supplied fuel first. -/
def stoppedPayoff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChanceOnHistories) (fuel : ℕ) :
    Option (N → U) :=
  G.stoppedPayoffFrom σ hNoChance
    (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel

end ObservedGame

end ExtensiveGame
