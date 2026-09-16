/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay
import Mathlib.Data.Fintype.EquivFin

/-!
# Payoff-free observed controlled games

API role: **canonical carrier**. This is the root of the
`Observed.Controlled` module hierarchy and owns only the base
observation/information record. Semantic and responsibility owners live below
`Observed.Controlled`; payoff-aware adapters are isolated below
`Observed.Controlled.Compat`.

This module is the objective-free information layer for extensive games.
`ControlledDecisionGame` is the observation-free minimal strategy carrier;
`ControlledObservedGame` optionally extends it with private and public
observations. Neither stores payoff nor continuation-root selection.

Continuation roots are supplied by the separate
`ContinuationRootPresentation`; lawful standard subgames remain a stronger,
independent payoff-free certificate in
`Controlled.Infrastructure.Subgame`.

## Main definitions

* `ControlledDecisionGame` and `ControlledObservedGame`.
* `ControlledDecisionGame.RepresentedInfo`, `PureStrategy`, and `PureProfile`.
* `ControlledObservedGame.relabelPlayers` and `relabelPureProfileEquiv`.
* `ControlledObservedGame.ContinuationRootPresentation`.
* `ControlledObservedGame.PureStrategy` and `PureProfile`.
* `ControlledObservedGame.completeInformation`.
-/

namespace ExtensiveGame

universe uN uA uS uO uI uP

/-- Minimal decision-information data over a payoff-free controlled game.

This carrier contains no observation or public-signal layer. It is the minimal
information-set core needed for pure strategies: a controlled Arena, decision
information, and equivalences between abstract and concrete legal actions. -/
structure ControlledDecisionGame (N : Type uN) where
  /-- The payoff-free controlled dynamics. -/
  base : ControlledGame.{uN, uA, uS} N
  /-- Player `i`'s decision-information carrier. -/
  InfoState : N → Type uI
  /-- Decision information at a genuine decision history controlled by player
  `i`.

  The constructive `IsDecision` premise supplies an actual legal action. This
  avoids treating `¬ IsEmpty` as data and makes terminal mover labels
  semantically irrelevant. -/
  infoAt :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N),
      base.mover history.1 = some i →
      base.toArena.IsDecision history.1 →
      InfoState i
  /-- Abstract actions at one decision-information state. -/
  InfoAction : (i : N) → InfoState i → Type uA
  /-- Abstract information actions are exactly the legal concrete actions at
  each represented decision history. -/
  actionEquiv :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i)
      (hdecision : base.toArena.IsDecision history.1),
      InfoAction i (infoAt history i hmover hdecision) ≃
        base.Action history.1

/-- Optional private/public observation extension of a minimal decision game.

Objectives, probability, finiteness, recall, and continuation-root selection
remain external. Analyses that need only information sets and strategies can
use `ControlledDecisionGame` without choosing any observation carrier. -/
structure ControlledObservedGame (N : Type uN)
    extends ControlledDecisionGame.{uN, uA, uS, uI} N where
  /-- Player `i`'s current private-observation type. -/
  Observation : N → Type uO
  /-- Public-observation type. -/
  PublicObservation : Type uP
  /-- Player `i`'s private observation after a complete history. -/
  observe :
    (i : N) → base.toArena.HistoryFrom base.init → Observation i
  /-- Public observation after a complete history. -/
  publicObserve :
    base.toArena.HistoryFrom base.init → PublicObservation
  /-- Forget private data and retain its public component. -/
  publicOf : (i : N) → Observation i → PublicObservation
  /-- Every private observation refines the public observation. -/
  observe_public :
    ∀ (i : N) (history : base.toArena.HistoryFrom base.init),
      publicOf i (observe i history) = publicObserve history
  /-- Forget decision memory and retain the current private signal. -/
  infoObserve : (i : N) → InfoState i → Observation i
  /-- Decision information projects to the current private signal. -/
  infoAt_observe :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i)
      (hdecision : base.toArena.IsDecision history.1),
      infoObserve i (infoAt history i hmover hdecision) =
        observe i history

namespace ControlledDecisionGame

variable {N : Type*} (G : ControlledDecisionGame N)

/-- A concrete player decision representing an abstract information state. -/
structure DecisionInfoWitness
    (G : ControlledDecisionGame N) (i : N)
    (information : G.InfoState i) where
  /-- Representing complete history. -/
  history : G.base.History
  /-- The selected player moves at the endpoint. -/
  mover : G.base.mover history.1 = some i
  /-- The endpoint has an actual legal action. -/
  decision : G.base.toArena.IsDecision history.1
  /-- The history represents the requested information state. -/
  infoAt_eq : G.infoAt history i mover decision = information

/-- Decision-information values that occur at at least one genuine player
decision. -/
def RepresentedInfo (G : ControlledDecisionGame N) (i : N) :=
  { information : G.InfoState i //
    Nonempty (G.DecisionInfoWitness i information) }

/-- Package the information state at one concrete decision as a represented
strategy coordinate. -/
def representedInfoAt
    (history : G.base.History) (i : N)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.RepresentedInfo i :=
  ⟨G.infoAt history i hmover hdecision,
    ⟨{
      history := history
      mover := hmover
      decision := hdecision
      infoAt_eq := rfl
    }⟩⟩

/-- Every represented decision-information coordinate has at least one
abstract legal action. This follows from its decision witness and therefore
requires no global mover-coherence or representation certificate. -/
theorem representedInfo_nonempty_infoAction
    (i : N) (information : G.RepresentedInfo i) :
    Nonempty (G.InfoAction i information.1) := by
  rcases information.2 with ⟨witness⟩
  have habstract :=
    witness.decision.map
      (G.actionEquiv witness.history i witness.mover
        witness.decision).symm
  simpa [witness.infoAt_eq] using habstract

/-- A deterministic contingent plan indexed only by represented decision
information. -/
def PureStrategy (i : N) : Type _ :=
  (information : G.RepresentedInfo i) →
    G.InfoAction i information.1

/-- A profile of payoff-free pure contingent plans. -/
def PureProfile : Type _ :=
  (i : N) → G.PureStrategy i

namespace PureStrategy

/-- Realize an abstract pure action at one represented concrete history. -/
def actionAt {i : N} (strategy : G.PureStrategy i)
    (history : G.base.History)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.base.Action history.1 :=
  G.actionEquiv history i hmover hdecision
    (strategy (G.representedInfoAt history i hmover hdecision))

end PureStrategy

end ControlledDecisionGame

namespace ControlledObservedGame

variable {N M : Type*} (G : ControlledObservedGame N)

/-- Relabel the player carrier along an equivalence while preserving the
Arena, initial state, histories, public observation, and every indexed
information/action fiber.

If `e : M ≃ N`, the result uses `M` as its player type. An old mover `i : N`
is renamed to `e.symm i`; data indexed by a new player `j : M` reuse the old
fiber indexed by `e j`. This is a structural reindexing, not a player
addition/deletion operation. -/
def relabelPlayers (e : M ≃ N) :
    ControlledObservedGame M where
  base :=
    { toArena := G.base.toArena
      init := G.base.init
      mover := fun state => (G.base.mover state).map e.symm }
  Observation := fun i => G.Observation (e i)
  PublicObservation := G.PublicObservation
  observe := fun i history => G.observe (e i) history
  publicObserve := G.publicObserve
  publicOf := fun i observation => G.publicOf (e i) observation
  observe_public := fun i history => G.observe_public (e i) history
  InfoState := fun i => G.InfoState (e i)
  infoObserve := fun i information => G.infoObserve (e i) information
  infoAt := by
    intro history i hmover hdecision
    apply G.infoAt history (e i) _ hdecision
    have h := congrArg (Option.map e) hmover
    simpa using h
  infoAt_observe := by
    intro history i hmover hdecision
    apply G.infoAt_observe
  InfoAction := fun i information => G.InfoAction (e i) information
  actionEquiv := by
    intro history i hmover hdecision
    apply G.actionEquiv

@[simp]
theorem relabelPlayers_toArena
    (e : M ≃ N) :
    (G.relabelPlayers e).base.toArena = G.base.toArena :=
  rfl

@[simp]
theorem relabelPlayers_init
    (e : M ≃ N) :
    (G.relabelPlayers e).base.init = G.base.init :=
  rfl

@[simp]
theorem relabelPlayers_mover
    (e : M ≃ N) (state : G.base.State) :
    (G.relabelPlayers e).base.mover state =
      (G.base.mover state).map e.symm :=
  rfl

@[simp]
theorem relabelPlayers_observe
    (e : M ≃ N) (i : M)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (G.relabelPlayers e).observe i history =
      G.observe (e i) history :=
  rfl

/-- Caller-selected continuation roots for one payoff-free observed game.

This presentation carries no standard-subgame lawfulness claim. It is
deliberately separate from the observed-game record so changing analysis roots
does not change the identity of the dynamics or information structure. -/
structure ContinuationRootPresentation
    (G : ControlledObservedGame N) where
  /-- Histories exposed to a root-scoped analysis. -/
  IsRoot : G.base.toArena.HistoryFrom G.base.init → Prop
  /-- The initial empty history is always exposed. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil G.base.toArena G.base.init)

namespace ContinuationRootPresentation

variable {G : ControlledObservedGame N}

/-- Reuse a root presentation after bijective player relabeling.

The Arena and complete-history carrier are definitionally unchanged. -/
def relabelPlayers
    (roots : G.ContinuationRootPresentation)
    (e : M ≃ N) :
    (G.relabelPlayers e).ContinuationRootPresentation where
  IsRoot := roots.IsRoot
  init_isRoot := roots.init_isRoot

@[simp]
theorem relabelPlayers_isRoot
    (roots : G.ContinuationRootPresentation)
    (e : M ≃ N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (roots.relabelPlayers e).IsRoot history ↔
      roots.IsRoot history :=
  Iff.rfl

/-- Expose only the initial history. -/
def initialOnly (G : ControlledObservedGame N) :
    G.ContinuationRootPresentation where
  IsRoot := fun history =>
    history = Arena.HistoryFrom.nil G.base.toArena G.base.init
  init_isRoot := rfl

/-- Expose every legal complete history, without claiming that every history
is a lawful standard-subgame root. -/
def allHistories (G : ControlledObservedGame N) :
    G.ContinuationRootPresentation where
  IsRoot := fun _history => True
  init_isRoot := trivial

@[simp]
theorem initialOnly_isRoot_iff
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (initialOnly G).IsRoot history ↔
      history = Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  Iff.rfl

@[simp]
theorem allHistories_isRoot
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (allHistories G).IsRoot history :=
  trivial

end ContinuationRootPresentation

/-- Compatibility name for the minimal-core decision witness. -/
abbrev DecisionInfoWitness (i : N) (information : G.InfoState i) :=
  G.toControlledDecisionGame.DecisionInfoWitness i information

/-- Compatibility name for represented minimal-core information. -/
abbrev RepresentedInfo (i : N) :=
  G.toControlledDecisionGame.RepresentedInfo i

/-- Package one observed-game decision as a represented strategy coordinate. -/
abbrev representedInfoAt :=
  G.toControlledDecisionGame.representedInfoAt

/-- Pure strategies are owned by the observation-free decision core. -/
abbrev PureStrategy (i : N) : Type _ :=
  G.toControlledDecisionGame.PureStrategy i

/-- Pure profiles are owned by the observation-free decision core. -/
abbrev PureProfile : Type _ :=
  G.toControlledDecisionGame.PureProfile

/-- Represented information is invariant under bijective player renaming. -/
def relabelRepresentedInfoEquiv (e : M ≃ N) (i : M) :
    (G.relabelPlayers e).RepresentedInfo i ≃
      G.RepresentedInfo (e i) where
  toFun information :=
    ⟨information.1, by
      rcases information.2 with ⟨witness⟩
      refine ⟨{
        history := witness.history
        mover := ?_
        decision := witness.decision
        infoAt_eq := ?_
      }⟩
      · have hmover := congrArg (Option.map e) witness.mover
        simpa using hmover
      · simpa using witness.infoAt_eq⟩
  invFun information :=
    ⟨information.1, by
      rcases information.2 with ⟨witness⟩
      refine ⟨{
        history := witness.history
        mover := ?_
        decision := witness.decision
        infoAt_eq := ?_
      }⟩
      · change (G.base.mover witness.history.1).map e.symm = some i
        rw [witness.mover]
        simp
      · simpa using witness.infoAt_eq⟩
  left_inv information := by
    apply Subtype.ext
    rfl
  right_inv information := by
    apply Subtype.ext
    rfl

/-- Pure strategies are invariant under bijective player renaming at one
player coordinate. -/
def relabelPureStrategyEquiv (e : M ≃ N) (i : M) :
    (G.relabelPlayers e).PureStrategy i ≃ G.PureStrategy (e i) :=
  (G.relabelRepresentedInfoEquiv e i).piCongr fun _information =>
    Equiv.refl _

/-- Pure profiles are invariant under bijective player renaming, up to the
corresponding dependent-function reindexing. -/
def relabelPureProfileEquiv (e : M ≃ N) :
    (G.relabelPlayers e).PureProfile ≃ G.PureProfile :=
  (Equiv.piCongrRight fun i => G.relabelPureStrategyEquiv e i).trans
    (e.piCongrLeft G.PureStrategy)

namespace PureStrategy

/-- Realize an abstract pure action at one represented concrete history. -/
def actionAt {i : N} (strategy : G.PureStrategy i)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.base.Action history.1 :=
  G.actionEquiv history i hmover hdecision
    (strategy (G.representedInfoAt history i hmover hdecision))

end PureStrategy

/-- Realize the concrete action selected by a pure profile at one represented
player decision. -/
def PureProfile.actionAt (profile : G.PureProfile)
    (history : G.base.toArena.HistoryFrom G.base.init) (i : N)
    (hmover : G.base.mover history.1 = some i)
    (hdecision : G.base.toArena.IsDecision history.1) :
    G.base.Action history.1 :=
  ControlledObservedGame.PureStrategy.actionAt
    G (profile i) history hmover hdecision

/-- Equal decision information forces a pure profile to make the same
dependent abstract choice.

The sigma packaging states constancy without choosing a transport between
potentially dependent action fibers. -/
theorem PureProfile.choice_eq_of_infoState_eq
    (profile : G.PureProfile) (i : N)
    (first second :
      G.base.toArena.HistoryFrom G.base.init)
    (firstMover : G.base.mover first.1 = some i)
    (secondMover : G.base.mover second.1 = some i)
    (firstDecision : G.base.toArena.IsDecision first.1)
    (secondDecision : G.base.toArena.IsDecision second.1)
    (hsame :
      G.infoAt first i firstMover firstDecision =
        G.infoAt second i secondMover secondDecision) :
    (⟨G.representedInfoAt first i firstMover firstDecision,
        profile i
          (G.representedInfoAt first i firstMover firstDecision)⟩ :
      Σ information : G.RepresentedInfo i,
        G.InfoAction i information.1) =
      ⟨G.representedInfoAt second i secondMover secondDecision,
        profile i
          (G.representedInfoAt second i secondMover secondDecision)⟩ :=
  congrArg
    (fun information : G.RepresentedInfo i =>
      (⟨information, profile i information⟩ :
        Σ state : G.RepresentedInfo i, G.InfoAction i state.1))
    (Subtype.ext hsame)

/-- Equal represented decision information implies equal public
observations. -/
theorem publicObserve_eq_of_infoAt_eq
    (i : N)
    (first second :
      G.base.toArena.HistoryFrom G.base.init)
    (firstMover : G.base.mover first.1 = some i)
    (secondMover : G.base.mover second.1 = some i)
    (firstDecision : G.base.toArena.IsDecision first.1)
    (secondDecision : G.base.toArena.IsDecision second.1)
    (hsame :
      G.infoAt first i firstMover firstDecision =
        G.infoAt second i secondMover secondDecision) :
    G.publicObserve first = G.publicObserve second := by
  calc
    G.publicObserve first =
        G.publicOf i (G.observe i first) :=
      (G.observe_public i first).symm
    _ = G.publicOf i
        (G.infoObserve i
          (G.infoAt first i firstMover firstDecision)) := by
      rw [G.infoAt_observe
        first i firstMover firstDecision]
    _ = G.publicOf i
        (G.infoObserve i
          (G.infoAt second i secondMover secondDecision)) := by
      rw [hsame]
    _ = G.publicOf i (G.observe i second) := by
      rw [G.infoAt_observe
        second i secondMover secondDecision]
    _ = G.publicObserve second :=
      G.observe_public i second

namespace CompleteInformation

  /-- A genuine decision history whose endpoint is controlled by player `i`.
  Terminal mover labels are deliberately ignored. -/
abbrev DecisionHistory (base : ControlledGame N) (i : N) :=
  {history : base.toArena.HistoryFrom base.init //
    base.mover history.1 = some i ∧
      base.toArena.IsDecision history.1}

/-- Legal actions at a payoff-free complete-information decision history. -/
abbrev DecisionAction (base : ControlledGame N) (i : N)
    (information : DecisionHistory base i) :=
  base.Action information.1.1

end CompleteInformation

/-- Canonical payoff-free complete-information presentation.

Private and public observations retain the complete history. Player `i`'s
information states contain exactly histories whose endpoint mover is `i`, so
chance, other-player, and all terminal histories create no spurious strategy
coordinates. -/
abbrev completeInformation (base : ControlledGame N) :
    ControlledObservedGame N where
  base := base
  Observation := fun _i => base.toArena.HistoryFrom base.init
  PublicObservation := base.toArena.HistoryFrom base.init
  observe := fun _i history => history
  publicObserve := fun history => history
  publicOf := fun _i observation => observation
  observe_public := fun _i _history => rfl
  InfoState := CompleteInformation.DecisionHistory base
  infoObserve := fun _i information => information.1
  infoAt := fun history _i hmover hdecision =>
    ⟨history, hmover, hdecision⟩
  infoAt_observe := fun _history _i _hmover _hdecision => rfl
  InfoAction := CompleteInformation.DecisionAction base
  actionEquiv :=
    fun _history _i _hmover _hdecision => Equiv.refl _

end ControlledObservedGame

end ExtensiveGame
