/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall

/-!
# EconCSLib.GameTheory.ExtensiveGame.Compiler.FiniteImperfectObserved

Compile the compact finite imperfect-game presentation into the
history-indexed observed-EFG interface.

`FiniteImperfectGame` stores an optional information-set label at each compact
state together with an explicit abstract action type for each label and a
concrete-action equivalence at every represented node. The compiler completes
that decision-information presentation:

* player states carrying `some k` share a player-indexed labeled information
  state;
* player states carrying `none` receive a singleton information state;
* every labeled information state uses its declared abstract action type and
  its explicit equivalence to each represented concrete state;
* the acting player's current observation is this completed decision
  information in this particular compiler;
  nonacting-player observations and the public observation are deliberately
  trivial because the compact model stores no such data.

Both the finite presentation and the resulting `ObservedGame.PureStrategy`
are genuinely information-indexed and cannot inspect the current compact
state after receiving a shared label. Continuation roots remain separate from
the compiler certificate: an information label alone is insufficient to
choose a universal lawful subgame convention.

## Main definitions

* `FiniteImperfectGame.DecisionInfo` — labeled or singleton player decision
  information.
* `FiniteImperfectGame.ObservedCompiler` — information well-formedness
  certificate.
* `FiniteImperfectGame.ObservedCompiler.toObservedGame`.
* `FiniteImperfectGame.ObservedCompiler.ofInfoWellFormed`.
* `FiniteImperfectGame.ObservedChanceCompiler` — an observed compiler plus a
  normalized law at every represented chance state.
* `FiniteImperfectGame.ObservedChanceCompiler.toObservedChanceGame`.

## Main results

* `decisionInfoAt_of_some`, `decisionInfoAt_of_none`, and
  `decisionInfoAt_eq_of_same_info`.

The opt-in tiny-game compiler and perfect-recall regressions live in
`EconCSLib.Examples.ExtensiveGame.FiniteImperfectCompilation`.
-/

namespace FiniteImperfectGame

variable {N U : Type*}
variable (G : FiniteImperfectGame N U)

/-- View the duplicated finite transition data as the common Arena-based
extensive-game foundation. -/
def toExtensiveGame : ExtensiveGame N U where
  State := G.State
  Action := G.Action
  next := G.next
  init := G.init
  mover := G.mover
  payoff := G.payoff

/-- A raw information-set label witnessed at a decision of player `i`. -/
def PlayerInfoLabel (i : N) :=
  { information : G.InfoSet //
    ∃ state : G.State,
      G.info state = some information ∧
        G.mover state = some i }

/-- An unlabeled player decision, treated as a singleton information state. -/
def SingletonDecision (i : N) :=
  { state : G.State //
    G.info state = none ∧
      G.mover state = some i }

/-- Completed decision information for player `i`.

Raw `some k` labels are shared across all represented nodes.  A player node
with `info = none` is interpreted as a singleton decision rather than merged
with every other unlabeled node. -/
def DecisionInfo (i : N) :=
  G.PlayerInfoLabel i ⊕ G.SingletonDecision i

/-- Completed decision information at a concrete player state. -/
def decisionInfoAt
    (state : G.State) (i : N)
    (hmover : G.mover state = some i) :
    G.DecisionInfo i :=
  match hinfo : G.info state with
  | some information =>
      Sum.inl
        ⟨information,
          state, hinfo, hmover⟩
  | none =>
      Sum.inr
        ⟨state, hinfo, hmover⟩

/-- A labeled player state compiles to the corresponding shared information
label. -/
theorem decisionInfoAt_of_some
    (state : G.State) (i : N)
    (hmover : G.mover state = some i)
    (information : G.InfoSet)
    (hinfo : G.info state = some information) :
    G.decisionInfoAt state i hmover =
      Sum.inl
        (⟨information,
          state, hinfo, hmover⟩ :
          G.PlayerInfoLabel i) := by
  unfold decisionInfoAt
  split
  · rename_i information' hinfo'
    have hinformation : information' = information :=
      Option.some.inj (hinfo'.symm.trans hinfo)
    subst information'
    rfl
  · rename_i hnone
    simp [hinfo] at hnone

/-- An unlabeled player state compiles to its singleton information state. -/
theorem decisionInfoAt_of_none
    (state : G.State) (i : N)
    (hmover : G.mover state = some i)
    (hinfo : G.info state = none) :
    G.decisionInfoAt state i hmover =
      Sum.inr
        (⟨state, hinfo, hmover⟩ :
          G.SingletonDecision i) := by
  unfold decisionInfoAt
  split
  · rename_i information hsome
    simp [hinfo] at hsome
  · rfl

/-- Two player decisions carrying the same raw information label compile to
the same completed decision-information state. -/
theorem decisionInfoAt_eq_of_same_info
    (source target : G.State) (i : N)
    (sourceMover : G.mover source = some i)
    (targetMover : G.mover target = some i)
    (information : G.InfoSet)
    (sourceInfo : G.info source = some information)
    (targetInfo : G.info target = some information) :
    G.decisionInfoAt source i sourceMover =
      G.decisionInfoAt target i targetMover := by
  rw [G.decisionInfoAt_of_some source i sourceMover information sourceInfo]
  rw [G.decisionInfoAt_of_some target i targetMover information targetInfo]

/-- The abstract action type at a completed information state.

Labeled information uses the action type explicitly declared by the finite
presentation. Unlabeled player nodes are singleton information states and use
their concrete legal action type. -/
def DecisionInfo.Action
    {i : N} (information : G.DecisionInfo i) : Type _ :=
  match information with
  | .inl labeled => G.InfoAction labeled.1
  | .inr singleton => G.Action singleton.1

/-- Equivalence between the completed information action and the concrete
legal action at a represented player state. -/
def decisionActionEquiv
    (state : G.State) (i : N)
    (hmover : G.mover state = some i) :
    (G.decisionInfoAt state i hmover).Action G ≃
      G.Action state := by
  cases hinfo : G.info state with
  | some information =>
      rw [G.decisionInfoAt_of_some state i hmover information hinfo]
      exact G.actionEquiv state information hinfo
  | none =>
      rw [G.decisionInfoAt_of_none state i hmover hinfo]
      exact Equiv.refl _

/-- Compiler certificate from a finite imperfect presentation to an observed
EFG.

Information-set well-formedness is explicit. Continuation roots are not stored
here; callers pair the compiled observed game with an external root
presentation or lawful subgame system. -/
structure ObservedCompiler where
  /-- Local information labels have coherent movers and action types
  and are attached only to player nodes. -/
  infoWellFormed : G.InfoWellFormed

namespace ObservedCompiler

variable {G : FiniteImperfectGame N U}
variable [DecidableEq N]

/-- Construct an observed compiler from information well-formedness. -/
def ofInfoWellFormed
    (hinfo : G.InfoWellFormed) :
    G.ObservedCompiler where
  infoWellFormed := hinfo

/-- Acting-player observation in the compiled EFG.

The compact presentation contains no observations of nonacting players, so
those histories receive `none`. -/
def observe
    (_C : G.ObservedCompiler)
    (i : N)
    (history :
      G.toExtensiveGame.toArena.HistoryFrom
        G.toExtensiveGame.init) :
    Option (G.DecisionInfo i) :=
  if hmover : G.mover history.1 = some i then
    some (G.decisionInfoAt history.1 i hmover)
  else
    none

/-- Compile a finite imperfect presentation into the canonical observed-EFG
layer.

The source and compiled strategy spaces are both information-indexed. The
compiler additionally completes unlabeled player nodes as singleton
information states; it does not claim a literal type equivalence between the
two presentations. -/
def toObservedGame
    (C : G.ObservedCompiler) :
    ExtensiveGame.ObservedGame N U where
  base := G.toExtensiveGame
  Observation := fun i =>
    Option (G.DecisionInfo i)
  PublicObservation := Unit
  observe := C.observe
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := by
    intro i history
    rfl
  InfoState := G.DecisionInfo
  infoObserve := fun _ information =>
    some information
  infoAt := fun history i hmover _hnonterminal =>
    G.decisionInfoAt history.1 i hmover
  infoAt_observe := by
    intro history i hmover _hnonterminal
    change G.mover history.1 = some i at hmover
    simp [observe, hmover]
  InfoAction := fun _ information =>
    information.Action G
  actionEquiv := fun history i hmover _hnonterminal =>
    G.decisionActionEquiv
      history.1 i hmover

end ObservedCompiler

/-! ### Optional normalized chance semantics -/

/-- Compiler certificate for a finite imperfect presentation with normalized
chance laws.

The chance law is separate from the legacy `FiniteImperfectGame` record so
existing record construction and deterministic users remain source
compatible.  It is state-indexed because the compact source identifies a node
by its state; the compiler reuses the same law at every complete history
ending in that state. -/
structure ObservedChanceCompiler extends G.ObservedCompiler where
  /-- Normalized law on the concrete legal actions at every nonterminal
  state whose mover is `none`. -/
  chanceLaw :
    (state : G.State) →
      G.toExtensiveGame.isChanceState state →
      FiniteLaw (G.Action state)

namespace ObservedChanceCompiler

variable {G : FiniteImperfectGame N U}
variable [DecidableEq N]

/-- Build the conservative initial-root chance compiler without changing the
legacy compact game record. -/
def initialRoot
    (hinfo : G.InfoWellFormed)
    (chanceLaw :
      (state : G.State) →
        G.toExtensiveGame.isChanceState state →
        FiniteLaw (G.Action state)) :
    G.ObservedChanceCompiler where
  toObservedCompiler := ObservedCompiler.ofInfoWellFormed hinfo
  chanceLaw := chanceLaw

/-- Compile compact information and the separately supplied normalized chance
laws to the canonical observed chance-game layer. -/
def toObservedChanceGame
    (C : G.ObservedChanceCompiler) :
    ExtensiveGame.ObservedChanceGame N U :=
  ExtensiveGame.ObservedChanceGame.withChanceKernel
    C.toObservedCompiler.toObservedGame
    (fun history hchance =>
      C.chanceLaw history.1 hchance)

@[simp]
theorem toObservedChanceGame_observed
    (C : G.ObservedChanceCompiler) :
    C.toObservedChanceGame.observed =
      C.toObservedCompiler.toObservedGame := rfl

@[simp]
theorem toObservedChanceGame_chanceKernel
    (C : G.ObservedChanceCompiler)
    (history :
      G.toExtensiveGame.toArena.HistoryFrom
        G.toExtensiveGame.init)
    (hchance :
      G.toExtensiveGame.isChanceState history.1) :
    C.toObservedChanceGame.chanceKernel history hchance =
      C.chanceLaw history.1 hchance := rfl

/-- Compiled behavioral execution uses the source certificate's law exactly
at each chance history. -/
theorem toHistoryPolicy_of_chance
    (C : G.ObservedChanceCompiler)
    (profile :
      C.toObservedChanceGame.observed.BehavioralProfile)
    (history :
      G.toExtensiveGame.toArena.HistoryFrom
        G.toExtensiveGame.init)
    (hnonterminal :
      ¬ G.toExtensiveGame.isTerminal history.1)
    (hmover :
      G.toExtensiveGame.mover history.1 = none) :
    ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
        C.toObservedChanceGame profile history hnonterminal =
      C.chanceLaw history.1 ⟨hmover, hnonterminal⟩ := by
  rw [ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
    _ _ _ hnonterminal hmover]
  rfl

end ObservedChanceCompiler

end FiniteImperfectGame
