/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.GameForm.Basic
import Mathlib.Tactic.Order

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Core

Serializer states, observations, information, and behavioral-profile compilation.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU uSA uO uP

variable {n : ℕ} {U : Type uU}
  (G : FOSG.{0, uU, uSA, uSA, uO, uP} (Fin (n + 1)) U)

/-- A partial simultaneous action containing choices for all players whose
indices are strictly below `count`. -/
def PartialAction (world : G.WorldState) (count : ℕ) : Type _ :=
  FiniteLaw.FinPrefix (fun i : Fin (n + 1) => G.PlayerAction i world) count

namespace PartialAction

/-- The empty partial action. -/
def empty (world : G.WorldState) : PartialAction G world 0 :=
  FiniteLaw.FinPrefix.empty

/-- Append the action of player `count` to a partial simultaneous action. -/
def snoc {world : G.WorldState} {count : ℕ}
    (collected : PartialAction G world count)
    (hcount : count < n + 1)
    (action : G.PlayerAction ⟨count, hcount⟩ world) :
    PartialAction G world (count + 1) :=
  FiniteLaw.FinPrefix.snoc collected hcount action

/-- A complete partial action is a joint action. -/
def complete {world : G.WorldState}
    (collected : PartialAction G world (n + 1)) :
    G.JointAction world :=
  FiniteLaw.FinPrefix.complete collected rfl

/-- Restrict a complete joint action to the first `count` players. -/
def ofJoint {world : G.WorldState}
    (jointAction : G.JointAction world) (count : ℕ) :
    PartialAction G world count :=
  fun i _ => jointAction i

/-- Appending the next component to a restricted joint action gives the next
restriction. -/
theorem snoc_ofJoint {world : G.WorldState}
    (jointAction : G.JointAction world)
    (count : ℕ) (hcount : count < n + 1) :
    snoc G (ofJoint G jointAction count) hcount
        (jointAction ⟨count, hcount⟩) =
      ofJoint G jointAction (count + 1) := by
  funext i hi
  by_cases hprevious : i.val < count
  · simp [snoc, FiniteLaw.FinPrefix.snoc, ofJoint, hprevious]
  · have hvalue : i.val = count :=
      Nat.eq_of_lt_succ_of_not_lt hi hprevious
    have hplayer : i = (⟨count, hcount⟩ : Fin (n + 1)) :=
      Fin.ext hvalue
    subst i
    simp [snoc, FiniteLaw.FinPrefix.snoc, ofJoint]

end PartialAction

/-- Hidden state of the sequentialized EFG.

`player` stores earlier choices in `collected`, but the observation compiler
below intentionally forgets them. -/
inductive State : Type _
  | root
  | terminal
      (history : G.HistoryState)
      (hterminal : G.isTerminal history.1)
  | player
      (history : G.HistoryState)
      (hnonterminal : ¬ G.isTerminal history.1)
      (count : ℕ)
      (hcount : count < n + 1)
      (collected : PartialAction G history.1 count)
  | chance
      (history : G.HistoryState)
      (hnonterminal : ¬ G.isTerminal history.1)
      (action : G.JointAction history.1)

/-- The serializer state at a FOSG macro boundary. -/
def boundary
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState) :
    State G :=
  if hterminal : G.isTerminal history.1 then
    .terminal history hterminal
  else
    .player history hterminal 0 (Nat.zero_lt_succ n)
      (PartialAction.empty G history.1)

/-- Legal action type in the turn-taking serialization. -/
def Action : State G → Type _
  | .root => G.WorldState
  | .terminal _ _ => PEmpty
  | .player history _ count hcount _ =>
      G.PlayerAction ⟨count, hcount⟩ history.1
  | .chance _ _ _ => G.WorldState

/-- One deterministic serializer transition.

The final player decision enters a chance phase; the chance action is the
realized next world state and returns execution to a macro boundary. -/
def next
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    (state : State G) → Action G state → State G
  | .root, world =>
      boundary G ⟨world, FOSG.History.initial world⟩
  | .terminal _ _, action => nomatch action
  | .player history hnonterminal count hcount collected, action => by
      let extended :=
        PartialAction.snoc G collected hcount action
      if hnext : count + 1 < n + 1 then
        exact
          .player history hnonterminal (count + 1) hnext extended
      else
        have hcomplete : count + 1 = n + 1 :=
          Nat.le_antisymm (Nat.succ_le_of_lt hcount)
            (Nat.le_of_not_gt hnext)
        let jointAction : G.JointAction history.1 :=
          fun i => extended i (by simpa only [hcomplete] using i.isLt)
        exact .chance history hnonterminal jointAction
  | .chance history _ action, nextWorld =>
      boundary G
        ⟨nextWorld,
          FOSG.History.snoc history.2 action nextWorld⟩

/-- The Arena underlying the sequentialized EFG. -/
def arena
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    Arena where
  State := State G
  Action := Action G
  next := next G

/-- Strategic mover at a serializer state. -/
def mover : State G → Option (Fin (n + 1))
  | .root => none
  | .terminal _ _ => none
  | .player _ _ count hcount _ => some ⟨count, hcount⟩
  | .chance _ _ _ => none

/-- The turn-taking extensive game generated by the serializer.

`rootPayoff` is operationally irrelevant because the root is a chance node,
but supplying it keeps the compiler free of an arbitrary `Nonempty U`
assumption. -/
def game
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    ExtensiveGame (Fin (n + 1)) U where
  toArena := arena G
  init := .root
  mover := mover G
  payoff
    | .root => rootPayoff
    | .terminal history _ => G.payoff history.1
    | .player history _ _ _ _ => G.payoff history.1
    | .chance history _ _ => G.payoff history.1

@[simp]
theorem boundary_of_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState)
    (hterminal : G.isTerminal history.1) :
    boundary G history = .terminal history hterminal := by
  simp [boundary, hterminal]

@[simp]
theorem boundary_of_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (history : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal history.1) :
    boundary G history =
      .player history hnonterminal 0 (Nat.zero_lt_succ n)
        (PartialAction.empty G history.1) := by
  simp [boundary, hnonterminal]

/-- The serializer macro-boundary constructor retains the complete source
FOSG history state. -/
theorem boundary_injective
    [(world : G.WorldState) → Decidable (G.isTerminal world)] :
    Function.Injective (boundary G) := by
  intro source₁ source₂ heq
  by_cases hterminal₁ : G.isTerminal source₁.1
  · by_cases hterminal₂ : G.isTerminal source₂.1
    · rw [boundary_of_terminal G source₁ hterminal₁,
          boundary_of_terminal G source₂ hterminal₂] at heq
      injection heq
    · rw [boundary_of_terminal G source₁ hterminal₁,
          boundary_of_not_terminal G source₂ hterminal₂] at heq
      contradiction
  · by_cases hterminal₂ : G.isTerminal source₂.1
    · rw [boundary_of_not_terminal G source₁ hterminal₁,
          boundary_of_terminal G source₂ hterminal₂] at heq
      contradiction
    · rw [boundary_of_not_terminal G source₁ hterminal₁,
          boundary_of_not_terminal G source₂ hterminal₂] at heq
      injection heq

/-- Canonical player-collection state for a fixed joint action prefix. -/
def playerState (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1) :
    State G :=
  .player source hnonterminal count hcount
    (PartialAction.ofJoint G jointAction count)

/-- Canonical chance state after all components of a joint action have been
collected. -/
def chanceState (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1) :
    State G :=
  .chance source hnonterminal jointAction

/-- A nonterminal macro boundary is the first canonical player state. -/
theorem boundary_eq_playerState
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1) :
    boundary G source =
      playerState G source hnonterminal jointAction 0
        (Nat.zero_lt_succ n) := by
  rw [boundary_of_not_terminal G source hnonterminal]
  congr
  funext i hi
  exact (Nat.not_lt_zero i.val hi).elim

/-- One non-final canonical player choice advances to the next player. -/
theorem next_playerState_of_lt
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1)
    (hnext : count + 1 < n + 1) :
    next G
        (playerState G source hnonterminal jointAction count hcount)
        (jointAction ⟨count, hcount⟩) =
      playerState G source hnonterminal jointAction (count + 1)
        hnext := by
  simp [next, playerState, hnext, PartialAction.snoc_ofJoint]

/-- The final canonical player choice advances to the transition-chance
state. -/
theorem next_playerState_of_not_lt
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1)
    (hlast : ¬ count + 1 < n + 1) :
    next G
        (playerState G source hnonterminal jointAction count hcount)
        (jointAction ⟨count, hcount⟩) =
      chanceState G source hnonterminal jointAction := by
  simp only [playerState, next, hlast, ↓reduceDIte,
    PartialAction.snoc_ofJoint]
  congr

/-! ### Observation and information compilation -/

/-- The accumulated private FOSG view exposed at a serializer state.

The initial root precedes the random initial world and therefore exposes
`none`.  All states inside one serialized macro step expose the same
pre-transition FOSG view, independently of collected individual actions. -/
def privateView (i : Fin (n + 1)) :
    State G → Option (List (G.Observation i))
  | .root => none
  | .terminal history _ =>
      some (G.privateObservations i history.2)
  | .player history _ _ _ _ =>
      some (G.privateObservations i history.2)
  | .chance history _ _ =>
      some (G.privateObservations i history.2)

/-- The accumulated public FOSG view exposed at a serializer state. -/
def publicView :
    State G → Option (List G.PublicObservation)
  | .root => none
  | .terminal history _ =>
      some (G.publicObservations history.2)
  | .player history _ _ _ _ =>
      some (G.publicObservations history.2)
  | .chance history _ _ =>
      some (G.publicObservations history.2)

/-- Forget a serialized private view to its public component. -/
def publicOf (i : Fin (n + 1)) :
    Option (List (G.Observation i)) →
      Option (List G.PublicObservation) :=
  Option.map (List.map (G.publicOf i))

/-- Every serialized private view determines the serialized public view. -/
theorem privateView_public (i : Fin (n + 1)) (state : State G) :
    publicOf G i (privateView G i state) = publicView G state := by
  cases state with
  | root =>
      rfl
  | terminal history hterminal =>
      simp [privateView, publicView, publicOf,
        G.privateObservations_map_publicOf i history.2]
  | player history hnonterminal count hcount collected =>
      simp [privateView, publicView, publicOf,
        G.privateObservations_map_publicOf i history.2]
  | chance history hnonterminal action =>
      simp [privateView, publicView, publicOf,
        G.privateObservations_map_publicOf i history.2]

/-- Decision information at a player-controlled serializer state.

The mover equality rules out all non-player phases and identifies the
requested player with the current `Fin` index. -/
def infoAt (D : G.DecisionModel)
    (state : State G) (i : Fin (n + 1))
    (hmover : mover G state = some i) :
    D.InfoState i := by
  cases state with
  | root =>
      simp [mover] at hmover
  | terminal history hterminal =>
      simp [mover] at hmover
  | player history hnonterminal count hcount collected =>
      have hplayer :
          (⟨count, hcount⟩ : Fin (n + 1)) = i :=
        Option.some.inj hmover
      subst i
      exact D.infoAt history hnonterminal ⟨count, hcount⟩
  | chance history hnonterminal action =>
      simp [mover] at hmover

/-- Compiled decision information represents exactly the private FOSG view. -/
theorem infoAt_observe (D : G.DecisionModel)
    (state : State G) (i : Fin (n + 1))
    (hmover : mover G state = some i) :
    some (D.infoObserve i (infoAt G D state i hmover)) =
      privateView G i state := by
  cases state with
  | root =>
      simp [mover] at hmover
  | terminal history hterminal =>
      simp [mover] at hmover
  | player history hnonterminal count hcount collected =>
      have hplayer :
          (⟨count, hcount⟩ : Fin (n + 1)) = i :=
        Option.some.inj hmover
      subst i
      simp only [infoAt, privateView, Option.some.injEq]
      exact D.infoAt_observe history hnonterminal ⟨count, hcount⟩
  | chance history hnonterminal action =>
      simp [mover] at hmover

/-- Information-indexed FOSG actions are exactly the legal actions at a
player-controlled serializer state. -/
def infoActionEquiv (D : G.DecisionModel)
    (state : State G) (i : Fin (n + 1))
    (hmover : mover G state = some i) :
    D.InfoAction i (infoAt G D state i hmover) ≃ Action G state := by
  cases state with
  | root =>
      simp [mover] at hmover
  | terminal history hterminal =>
      simp [mover] at hmover
  | player history hnonterminal count hcount collected =>
      have hplayer :
          (⟨count, hcount⟩ : Fin (n + 1)) = i :=
        Option.some.inj hmover
      subst i
      simpa only [infoAt, Action] using
        D.actionEquiv history hnonterminal ⟨count, hcount⟩
  | chance history hnonterminal action =>
      simp [mover] at hmover

/-- Designated continuation roots in the serialized EFG.

Only macro boundaries may inherit the caller's FOSG declared-root predicate.
The synthetic initial root is always designated; intermediate player and
chance phases are not newly designated continuations.  This predicate does
not independently certify standard EFG subgames. -/
def isDesignatedContinuationRoot
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    State G → Prop
  | .root => True
  | .terminal history _ => sourceDeclaredRoot history
  | .player history _ count _ _ =>
      count = 0 ∧ sourceDeclaredRoot history
  | .chance _ _ _ => False

/-- The normalized chance law at root and transition-chance phases. -/
def chanceKernel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (history :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hchance : (game G rootPayoff).isChanceState history.1) :
    FiniteLaw ((game G rootPayoff).Action history.1) := by
  cases hstate : history.1 with
  | root =>
      exact G.init
  | terminal source hterminal =>
      exfalso
      apply hchance.2
      rw [hstate]
      exact ⟨fun action => nomatch action⟩
  | player source hnonterminal count hcount collected =>
      have : some (⟨count, hcount⟩ : Fin (n + 1)) = none := by
        simpa [game, mover, hstate] using hchance.1
      cases this
  | chance source hnonterminal action =>
      exact G.transition source.1 action

/-- Compile a finite nonempty-player FOSG into a root-free turn-taking
observed chance EFG.

All player and public observations remain constant throughout the hidden
individual-action collection phase. Continuation roots are attached
separately by `rootPresentation`. -/
def observedChanceGameCore
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U) :
    ObservedChanceGame (Fin (n + 1)) U where
  observed :=
    { base := game G rootPayoff
      Observation := fun i => Option (List (G.Observation i))
      PublicObservation := Option (List G.PublicObservation)
      observe := fun i history => privateView G i history.1
      publicObserve := fun history => publicView G history.1
      publicOf := publicOf G
      observe_public := by
        intro i history
        exact privateView_public G i history.1
      InfoState := D.InfoState
      infoObserve := fun i information =>
        some (D.infoObserve i information)
      infoAt := fun history i hmover _hnonterminal =>
        infoAt G D history.1 i hmover
      infoAt_observe := by
        intro history i hmover _hnonterminal
        exact infoAt_observe G D history.1 i hmover
      InfoAction := D.InfoAction
      actionEquiv := fun history i hmover _hnonterminal =>
        infoActionEquiv G D history.1 i hmover }
  chanceKernel := chanceKernel G rootPayoff

/-- Compatibility constructor retaining the established root-parameterized
signature.

The root predicate is intentionally not part of the compiled game value.
New code that only needs the serialized game should use
`observedChanceGameCore`; use `rootPresentation` when continuation roots are
also required. -/
def observedChanceGame
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (_sourceDeclaredRoot : G.HistoryState → Prop) :
    ObservedChanceGame (Fin (n + 1)) U :=
  observedChanceGameCore G D rootPayoff

/-- The established root-parameterized constructor is definitionally the
root-free compiled game. -/
@[simp]
theorem observedChanceGame_eq_core
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    observedChanceGame G D rootPayoff sourceDeclaredRoot =
      observedChanceGameCore G D rootPayoff :=
  rfl

/-- External continuation roots for the serialized EFG.

Macro boundaries inherit the caller's source-root predicate and the synthetic
initial root is included. The presentation is kept separate from the
root-free observed chance-game value. -/
def rootPresentation
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (observedChanceGameCore G D rootPayoff).observed.RootPresentation where
  IsRoot := fun history =>
    isDesignatedContinuationRoot G sourceDeclaredRoot history.1
  init_isRoot := by
    change True
    trivial

/-! ### Information-indexed behavioral-profile compilation -/

/-- Restrict one FOSG behavioral strategy to information states represented by
genuine serialized player decisions. -/
def serializedObservedBehavioralStrategy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (i : Fin (n + 1))
    (strategy : D.BehavioralStrategy i) :
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).observed.BehavioralStrategy i :=
  fun information => strategy information.1

/-- Reinterpret a FOSG `DecisionModel` behavioral profile as a behavioral
profile of the serialized observed EFG by restricting it to represented
decision information.

The compiler deliberately reuses the same information-state and abstract
action types.  No hidden serializer state appears in the resulting strategy.
-/
def serializedObservedBehavioralProfile
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).observed.BehavioralProfile :=
  fun i => serializedObservedBehavioralStrategy G D rootPayoff
    sourceDeclaredRoot i (profile i)

/-- Optional certificate that restriction to represented serialized
information is an equivalence of strategy spaces.

This is deliberately not part of the compiler: arbitrary `InfoState` values
may be ghost coordinates with no decision witness, and their action fibers
need not admit a canonical extension. -/
structure BehavioralStrategyEquivalence
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) where
  /-- Playerwise strategy equivalence. -/
  strategyEquiv :
    (i : Fin (n + 1)) →
      D.BehavioralStrategy i ≃
        (observedChanceGame G D rootPayoff
          sourceDeclaredRoot).observed.BehavioralStrategy i
  /-- The forward equivalence is the compiler's restriction map. -/
  strategyEquiv_apply :
    ∀ (i : Fin (n + 1)) (strategy : D.BehavioralStrategy i)
      (information :
        (observedChanceGame G D rootPayoff
          sourceDeclaredRoot).observed.RepresentedInfo i),
      strategyEquiv i strategy information = strategy information.1

/-- A supplied playerwise certificate induces an equivalence of complete
behavioral profiles. -/
def serializedObservedBehavioralProfileEquiv
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (certificate :
      BehavioralStrategyEquivalence G D rootPayoff sourceDeclaredRoot) :
    D.BehavioralProfile ≃
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.BehavioralProfile :=
  Equiv.piCongrRight certificate.strategyEquiv

/-- The micro-step stochastic history policy induced by a serialized
behavioral profile and the compiler's declared chance kernels. -/
def serializedBehavioralHistoryPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (game G rootPayoff).toArena.StochasticHistoryPolicy
      (game G rootPayoff).init :=
  ObservedChanceGame.BehavioralProfile.toHistoryPolicy
    (observedChanceGame G D rootPayoff sourceDeclaredRoot)
    (serializedObservedBehavioralProfile G D rootPayoff
      sourceDeclaredRoot profile)

/-- The serialized behavioral history policy uses every declared chance
kernel exactly. -/
theorem serializedBehavioralHistoryPolicy_chanceConsistent
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).ChanceConsistent
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile) :=
  ObservedChanceGame.BehavioralProfile.toHistoryPolicy_chanceConsistent
    (observedChanceGame G D rootPayoff sourceDeclaredRoot)
    (serializedObservedBehavioralProfile G D rootPayoff
      sourceDeclaredRoot profile)

/-- Behavioral-profile compilation commutes exactly with unilateral
deviation. -/
theorem serializedObservedBehavioralProfile_deviate
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (who : Fin (n + 1))
    (deviation : D.BehavioralStrategy who) :
    serializedObservedBehavioralProfile G D rootPayoff
        sourceDeclaredRoot
        (FOSG.DecisionModel.BehavioralProfile.deviate
          D profile who deviation) =
      ObservedGame.BehavioralProfile.deviate
        (observedChanceGame G D rootPayoff
          sourceDeclaredRoot).observed
        (serializedObservedBehavioralProfile G D rootPayoff
          sourceDeclaredRoot profile)
        who
        (serializedObservedBehavioralStrategy G D rootPayoff
          sourceDeclaredRoot who deviation) := by
  funext i information
  by_cases hi : i = who
  · subst i
    simp [serializedObservedBehavioralProfile,
      FOSG.DecisionModel.BehavioralProfile.deviate,
      ObservedGame.BehavioralProfile.deviate]
  · simp [serializedObservedBehavioralProfile,
      FOSG.DecisionModel.BehavioralProfile.deviate,
      ObservedGame.BehavioralProfile.deviate, hi]

/-- At every serialized player node, the genuine observed-EFG behavioral
history policy uses exactly the corresponding source information-state action
law. -/
theorem serializedBehavioralHistoryPolicy_player
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (count : ℕ) (hcount : count < n + 1)
    (collected : PartialAction G source.1 count)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.player source hsource count hcount collected))
    (hnonterminal :
      ¬ (game G rootPayoff).isTerminal
        (.player source hsource count hcount collected)) :
    serializedBehavioralHistoryPolicy G D rootPayoff
        sourceDeclaredRoot profile
        ⟨.player source hsource count hcount collected, history⟩
        hnonterminal =
      (profile ⟨count, hcount⟩
          (D.infoAt source hsource ⟨count, hcount⟩)).map
        (D.actionEquiv source hsource ⟨count, hcount⟩) := by
  exact
    ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover
      (observedChanceGame G D rootPayoff sourceDeclaredRoot)
      (serializedObservedBehavioralProfile G D rootPayoff
        sourceDeclaredRoot profile)
      ⟨.player source hsource count hcount collected, history⟩
      hnonterminal ⟨count, hcount⟩ rfl

/-- At a serialized transition-chance node, the genuine behavioral history
policy uses the original FOSG transition kernel exactly. -/
theorem serializedBehavioralHistoryPolicy_chance
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.chance source hsource jointAction))
    (hnonterminal :
      ¬ (game G rootPayoff).isTerminal
        (.chance source hsource jointAction)) :
    serializedBehavioralHistoryPolicy G D rootPayoff
        sourceDeclaredRoot profile
        ⟨.chance source hsource jointAction, history⟩
        hnonterminal =
      G.transition source.1 jointAction := by
  exact
    ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
      (observedChanceGame G D rootPayoff sourceDeclaredRoot)
      (serializedObservedBehavioralProfile G D rootPayoff
        sourceDeclaredRoot profile)
      ⟨.chance source hsource jointAction, history⟩
      hnonterminal rfl

/-- At the synthetic root, the genuine behavioral history policy uses the
original FOSG initial-world law exactly. -/
theorem serializedBehavioralHistoryPolicy_root
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (hnonterminal :
      ¬ (game G rootPayoff).isTerminal .root) :
    serializedBehavioralHistoryPolicy G D rootPayoff
        sourceDeclaredRoot profile
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        hnonterminal =
      G.init := by
  exact
    ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
      (observedChanceGame G D rootPayoff sourceDeclaredRoot)
      (serializedObservedBehavioralProfile G D rootPayoff
        sourceDeclaredRoot profile)
      (Arena.HistoryFrom.nil
        (game G rootPayoff).toArena
        (game G rootPayoff).init)
      hnonterminal rfl

/-- The concrete action law of each source player at one nonterminal macro
history.  Its finite dependent product is `DecisionModel.jointActionLaw`. -/
def behavioralActionLaws
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (i : Fin (n + 1)) :
    FiniteLaw (G.PlayerAction i source.1) :=
  (profile i (D.infoAt source hsource i)).map
    (D.actionEquiv source hsource i)

/-- The source behavioral joint-action law is exactly the increasing-index
prefix sampler used by the serializer. -/
theorem jointActionLaw_eq_finPi
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1) :
    D.jointActionLaw profile source hsource =
      FiniteLaw.finPi (n + 1)
        (behavioralActionLaws G D profile source hsource) :=
  rfl

/-- Every joint action in a completion law's support extends the already
collected serialized prefix. -/
theorem collected_eq_of_mem_support_finPiFrom
    (D : G.DecisionModel)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (remaining count : ℕ)
    (htotal : count + remaining = n + 1)
    (collected : PartialAction G source.1 count)
    (jointAction : G.JointAction source.1)
    (hjoint :
      (FiniteLaw.finPiFrom
        (behavioralActionLaws G D profile source hsource)
        remaining count htotal collected).HasPositiveAtom jointAction) :
    PartialAction.ofJoint G jointAction count = collected := by
  funext i hi
  exact
    FiniteLaw.finPiFrom_apply_eq_of_hasPositiveAtom_of_lt
      (behavioralActionLaws G D profile source hsource)
      remaining count htotal collected jointAction hjoint i hi

end ExtensiveGame.FOSG.Sequentialization
