/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.DependentFiber
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free observed-game morphism core

This leaf owns the structural comparison of `ControlledObservedGame`.
`ControlledObservedGame.Hom` records a directional map of histories and
information carriers. `ControlledObservedGame.Iso` is the strict invertible
relation: one source step is one target step, dependent action fibers are
equivalent, and concrete realization commutes.

Continuation roots are not fields of either relation. Their one-way or exact
correspondence is supplied independently through
`MapsRootPresentations`/`PreservesRootPresentations`.

Payoff compatibility and conversion from the legacy `ObservedGame.Iso` live
in `Controlled.Compat.Morphism`. Lawful-subgame and recall transport live in
their respective `Controlled.Morphism` leaves, so this structural core has no
subgame, recall, finite-EFG, structural-length, or payoff-aware observed-game
dependency.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*}

/-! ## Directional structural homomorphisms -/

/-- A directional map of payoff-free histories, observations, and information
carriers.

This relation intentionally does not claim execution-law preservation:
dependent information actions are mapped as carriers, while exact commuting
with concrete action realization is reserved for `Iso` and stronger
simulation certificates. -/
structure Hom (G H : ControlledObservedGame N) where
  /-- Strict one-step map of complete-history arenas. -/
  historyHom : G.base.unfold.toArena.Hom H.base.unfold.toArena
  /-- The empty history is preserved. -/
  map_init :
    historyHom.state
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Mover labels are preserved. -/
  map_mover :
    ∀ history : G.base.History,
      H.base.mover (historyHom.state history).1 =
        G.base.mover history.1
  /-- Map private observations. -/
  mapObservation : (i : N) → G.Observation i → H.Observation i
  /-- Private observation commutes with history mapping. -/
  map_observe :
    ∀ (i : N) (history : G.base.History),
      mapObservation i (G.observe i history) =
        H.observe i (historyHom.state history)
  /-- Map public observations. -/
  mapPublic : G.PublicObservation → H.PublicObservation
  /-- Public observation commutes with history mapping. -/
  map_publicObserve :
    ∀ history : G.base.History,
      mapPublic (G.publicObserve history) =
        H.publicObserve (historyHom.state history)
  /-- Map decision information. -/
  mapInfo : (i : N) → G.InfoState i → H.InfoState i
  /-- Decision information commutes at represented histories. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyHom.state history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyHom.state history).1),
      mapInfo i
          (G.infoAt history i hsource hsource_nonterminal) =
        H.infoAt (historyHom.state history) i htarget
          htarget_nonterminal
  /-- Map dependent information-action carriers. -/
  mapInfoAction :
    ∀ (i : N) (information : G.InfoState i),
      G.InfoAction i information →
        H.InfoAction i (mapInfo i information)

namespace Hom

variable {G H : ControlledObservedGame N}

/-- A structural hom maps selected source roots into selected target roots. -/
def MapsRootPresentations
    (f : G.Hom H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history →
      targetRoots.IsRoot (f.historyHom.state history)

/-- Identity structural homomorphism. -/
def refl (G : ControlledObservedGame N) : G.Hom G where
  historyHom := Arena.Hom.id G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  mapObservation := fun _ observation => observation
  map_observe := by intro i history; rfl
  mapPublic := id
  map_publicObserve := by intro history; rfl
  mapInfo := fun _ information => information
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    congr
  mapInfoAction := fun _ _ action => action

/-- Composition of directional structural homomorphisms. -/
def trans {K : ControlledObservedGame N}
    (f : G.Hom H) (g : H.Hom K) : G.Hom K where
  historyHom := g.historyHom.comp f.historyHom
  map_init := by
    change
      g.historyHom.state
          (f.historyHom.state
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        Arena.HistoryFrom.nil K.base.toArena K.base.init
    rw [f.map_init, g.map_init]
  map_mover := by
    intro history
    change
      K.base.mover
          (g.historyHom.state
            (f.historyHom.state history)).1 =
        G.base.mover history.1
    rw [g.map_mover, f.map_mover]
  mapObservation := fun i =>
    g.mapObservation i ∘ f.mapObservation i
  map_observe := by
    intro i history
    change
      g.mapObservation i
          (f.mapObservation i (G.observe i history)) =
        K.observe i
          (g.historyHom.state
            (f.historyHom.state history))
    rw [f.map_observe, g.map_observe]
  mapPublic := g.mapPublic ∘ f.mapPublic
  map_publicObserve := by
    intro history
    change
      g.mapPublic (f.mapPublic (G.publicObserve history)) =
        K.publicObserve
          (g.historyHom.state
            (f.historyHom.state history))
    rw [f.map_publicObserve, g.map_publicObserve]
  mapInfo := fun i => g.mapInfo i ∘ f.mapInfo i
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    have hmiddle :
        H.base.mover (f.historyHom.state history).1 = some i := by
      rw [f.map_mover history]
      exact hsource
    have hmiddle_nonterminal :
        H.base.toArena.IsDecision
          (f.historyHom.state history).1 :=
      f.historyHom.isDecision hsource_nonterminal
    exact
      (congrArg (g.mapInfo i)
        (f.map_infoAt history i hsource hsource_nonterminal
          hmiddle hmiddle_nonterminal)).trans
        (g.map_infoAt
          (f.historyHom.state history) i
          hmiddle hmiddle_nonterminal htarget htarget_nonterminal)
  mapInfoAction := fun i information action =>
    g.mapInfoAction i (f.mapInfo i information)
      (f.mapInfoAction i information action)

/-- Structural hom composition preserves one-way root mapping. -/
theorem trans_mapsRootPresentations
    {K : ControlledObservedGame N}
    (f : G.Hom H) (g : H.Hom K)
    {sourceRoots : G.ContinuationRootPresentation}
    {middleRoots : H.ContinuationRootPresentation}
    {targetRoots : K.ContinuationRootPresentation}
    (hf : f.MapsRootPresentations sourceRoots middleRoots)
    (hg : g.MapsRootPresentations middleRoots targetRoots) :
    (f.trans g).MapsRootPresentations sourceRoots targetRoots := by
  intro history hroot
  exact hg _ (hf history hroot)

end Hom

/-! ## Directional information refinement -/

/-- A payoff-free information refinement from a coarse presentation `G` to a
finer presentation `H`.

The complete-history dynamics are strictly isomorphic. Fine private, public,
and decision information forgets to coarse information, while every coarse
information action lifts to the corresponding fine fiber. -/
structure InformationRefinement
    (G H : ControlledObservedGame N) where
  /-- Strict equivalence of complete-history dynamics. -/
  historyIso : G.base.unfold.toArena.Iso H.base.unfold.toArena
  /-- Empty histories correspond. -/
  map_init :
    historyIso.stateEquiv
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Mover labels correspond. -/
  map_mover :
    ∀ history : G.base.History,
      H.base.mover (historyIso.stateEquiv history).1 =
        G.base.mover history.1
  /-- Forget fine private observations. -/
  forgetObservation :
    (i : N) → H.Observation i → G.Observation i
  /-- Private-observation forgetting commutes with history transport. -/
  forget_observe :
    ∀ (i : N) (history : G.base.History),
      forgetObservation i
          (H.observe i (historyIso.stateEquiv history)) =
        G.observe i history
  /-- Forget fine public observations. -/
  forgetPublic : H.PublicObservation → G.PublicObservation
  /-- Public-observation forgetting commutes with history transport. -/
  forget_publicObserve :
    ∀ history : G.base.History,
      forgetPublic
          (H.publicObserve (historyIso.stateEquiv history)) =
        G.publicObserve history
  /-- Private-to-public projection commutes with forgetting. -/
  forget_publicOf :
    ∀ (i : N) (observation : H.Observation i),
      forgetPublic (H.publicOf i observation) =
        G.publicOf i (forgetObservation i observation)
  /-- Forget fine decision information. -/
  forgetInfo :
    (i : N) → H.InfoState i → G.InfoState i
  /-- Information-to-observation projection commutes with forgetting. -/
  forget_infoObserve :
    ∀ (i : N) (information : H.InfoState i),
      forgetObservation i (H.infoObserve i information) =
        G.infoObserve i (forgetInfo i information)
  /-- Lift coarse information actions to each fine information fiber. -/
  infoActionEquiv :
    ∀ (i : N) (information : H.InfoState i),
      G.InfoAction i (forgetInfo i information) ≃
        H.InfoAction i information
  /-- Forgetting represented fine information recovers source information. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1),
      G.infoAt history i hsource hsource_nonterminal =
        forgetInfo i
          (H.infoAt (historyIso.stateEquiv history) i htarget
            htarget_nonterminal)
  /-- Lifting and realizing a coarse action commutes with strict concrete
  history-action transport. -/
  map_infoActionAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1)
      (action :
        G.InfoAction i
          (G.infoAt history i hsource hsource_nonterminal)),
      H.actionEquiv (historyIso.stateEquiv history) i htarget
          htarget_nonterminal
          (infoActionEquiv i
            (H.infoAt
              (historyIso.stateEquiv history) i htarget
              htarget_nonterminal)
            (cast
              (congrArg (G.InfoAction i)
                (map_infoAt history i hsource
                  hsource_nonterminal htarget
                  htarget_nonterminal))
              action)) =
        historyIso.actionEquiv history
          (G.actionEquiv history i hsource
            hsource_nonterminal action)

namespace InformationRefinement

variable {G H : ControlledObservedGame N}

/-- Forgetting fine information sends represented fine coordinates to
represented coarse coordinates. -/
def forgetRepresentedInfo
    (r : G.InformationRefinement H) (i : N) :
    H.RepresentedInfo i → G.RepresentedInfo i := by
  intro information
  refine ⟨r.forgetInfo i information.1, ?_⟩
  rcases information.2 with ⟨targetWitness⟩
  let sourceHistory :=
    r.historyIso.stateEquiv.symm targetWitness.history
  have hsourceMover :
      G.base.mover sourceHistory.1 = some i := by
    rw [← r.map_mover sourceHistory]
    simpa [sourceHistory] using targetWitness.mover
  have hsourceDecision :
      G.base.toArena.IsDecision sourceHistory.1 :=
    (r.historyIso.isDecision_iff sourceHistory).2 (by
      simpa [sourceHistory] using targetWitness.decision)
  have htargetMover :
      H.base.mover (r.historyIso.stateEquiv sourceHistory).1 = some i := by
    rw [r.map_mover sourceHistory]
    exact hsourceMover
  have htargetDecision :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv sourceHistory).1 :=
    (r.historyIso.isDecision_iff sourceHistory).1 hsourceDecision
  refine ⟨{
    history := sourceHistory
    mover := hsourceMover
    decision := hsourceDecision
    infoAt_eq := ?_
  }⟩
  calc
    G.infoAt sourceHistory i hsourceMover hsourceDecision =
        r.forgetInfo i
          (H.infoAt (r.historyIso.stateEquiv sourceHistory) i
            htargetMover htargetDecision) :=
      r.map_infoAt sourceHistory i hsourceMover hsourceDecision
        htargetMover htargetDecision
    _ = r.forgetInfo i information.1 := by
      apply congrArg (r.forgetInfo i)
      simpa [sourceHistory] using targetWitness.infoAt_eq

/-- A refinement maps selected coarse roots into selected fine roots. -/
def MapsRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history →
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Exact external root correspondence along an information refinement. -/
def PreservesRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history ↔
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Lift a coarse payoff-free pure strategy to the finer information
presentation. -/
def mapStrategy
    (r : G.InformationRefinement H) (i : N)
    (strategy : G.PureStrategy i) :
    H.PureStrategy i :=
  fun information =>
    r.infoActionEquiv i information.1
      (strategy (r.forgetRepresentedInfo i information))

/-- Lift a payoff-free pure profile componentwise. -/
def mapProfile
    (r : G.InformationRefinement H)
    (profile : G.PureProfile) :
    H.PureProfile :=
  fun i => r.mapStrategy i (profile i)

/-- Lifted and coarse profiles choose corresponding concrete actions at every
player-controlled history. -/
theorem map_actionAt
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (r.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (r.historyIso.stateEquiv history).1) :
    PureProfile.actionAt H (r.mapProfile profile)
        (r.historyIso.stateEquiv history) i htarget
        htarget_nonterminal =
      r.historyIso.actionEquiv history
        (PureProfile.actionAt G profile history i hsource
          hsource_nonterminal) := by
  let sourceInformation :=
    G.representedInfoAt history i hsource hsource_nonterminal
  let targetInformation :=
    H.representedInfoAt (r.historyIso.stateEquiv history) i
      htarget htarget_nonterminal
  have hrepresented :
      r.forgetRepresentedInfo i targetInformation =
        sourceInformation :=
    Subtype.ext
      (r.map_infoAt history i hsource hsource_nonterminal
        htarget htarget_nonterminal).symm
  unfold PureProfile.actionAt PureStrategy.actionAt mapProfile mapStrategy
  change
    H.actionEquiv (r.historyIso.stateEquiv history) i htarget
        htarget_nonterminal
        (r.infoActionEquiv i targetInformation.1
          (profile i (r.forgetRepresentedInfo i targetInformation))) =
      r.historyIso.actionEquiv history
        (G.actionEquiv history i hsource hsource_nonterminal
          (profile i sourceInformation))
  have hchoice :
      profile i (r.forgetRepresentedInfo i targetInformation) =
        cast
          (congrArg (G.InfoAction i)
            (r.map_infoAt history i hsource hsource_nonterminal
              htarget htarget_nonterminal))
          (profile i sourceInformation) := by
    simpa [sourceInformation, targetInformation,
      forgetRepresentedInfo] using
      dependent_apply_eq_cast
        (profile i) hrepresented.symm
  rw [hchoice]
  exact
    r.map_infoActionAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal (profile i sourceInformation)

/-- Coverage of all target strategies is an additional hypothesis, not part
of a genuine information refinement. -/
def StrategySurjective
    (r : G.InformationRefinement H) : Prop :=
  ∀ i : N, Function.Surjective (r.mapStrategy i)

/-- Refinement strategy lifting commutes with unilateral update. -/
theorem mapProfile_update [DecidableEq N]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (who : N) (deviation : G.PureStrategy who) :
    r.mapProfile (Function.update profile who deviation) =
      Function.update (r.mapProfile profile) who
        (r.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

/-- Identity payoff-free information refinement. -/
def refl (G : ControlledObservedGame N) :
    G.InformationRefinement G where
  historyIso := Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  forgetObservation := fun _ observation => observation
  forget_observe := by intro i history; rfl
  forgetPublic := id
  forget_publicObserve := by intro history; rfl
  forget_publicOf := by intro i observation; rfl
  forgetInfo := fun _ information => information
  forget_infoObserve := by intro i information; rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    congr
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    rfl

end InformationRefinement

/-! ## Strict structural isomorphisms -/

/-- A strict payoff-free observed-game isomorphism.

Besides equivalences of all carriers, the final square states that mapping an
abstract information action and then realizing it is exactly the strict
history-action map. No payoff compatibility is present. -/
structure Iso (G H : ControlledObservedGame N) where
  /-- Strict isomorphism of complete-history arenas. -/
  historyIso : G.base.unfold.toArena.Iso H.base.unfold.toArena
  /-- Empty histories correspond. -/
  map_init :
    historyIso.stateEquiv
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Mover labels correspond. -/
  map_mover :
    ∀ history : G.base.History,
      H.base.mover (historyIso.stateEquiv history).1 =
        G.base.mover history.1
  /-- Equivalence of private-observation carriers. -/
  observationEquiv :
    (i : N) → G.Observation i ≃ H.Observation i
  /-- Private observation commutes. -/
  map_observe :
    ∀ (i : N) (history : G.base.History),
      observationEquiv i (G.observe i history) =
        H.observe i (historyIso.stateEquiv history)
  /-- Equivalence of public-observation carriers. -/
  publicEquiv : G.PublicObservation ≃ H.PublicObservation
  /-- Public observation commutes. -/
  map_publicObserve :
    ∀ history : G.base.History,
      publicEquiv (G.publicObserve history) =
        H.publicObserve (historyIso.stateEquiv history)
  /-- Private-to-public projection commutes. -/
  map_publicOf :
    ∀ (i : N) (observation : G.Observation i),
      publicEquiv (G.publicOf i observation) =
        H.publicOf i (observationEquiv i observation)
  /-- Equivalence of decision-information carriers. -/
  infoStateEquiv :
    (i : N) → G.InfoState i ≃ H.InfoState i
  /-- Information-to-observation projection commutes. -/
  map_infoObserve :
    ∀ (i : N) (information : G.InfoState i),
      observationEquiv i (G.infoObserve i information) =
        H.infoObserve i (infoStateEquiv i information)
  /-- Equivalence of dependent information-action fibers. -/
  infoActionEquiv :
    ∀ (i : N) (information : G.InfoState i),
      G.InfoAction i information ≃
        H.InfoAction i (infoStateEquiv i information)
  /-- Represented decision information commutes. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1),
      infoStateEquiv i
          (G.infoAt history i hsource hsource_nonterminal) =
        H.infoAt (historyIso.stateEquiv history) i htarget
          htarget_nonterminal
  /-- Abstract-action realization commutes with the history action map. -/
  map_infoActionAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (hsource_nonterminal : G.base.toArena.IsDecision history.1)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (htarget_nonterminal :
        H.base.toArena.IsDecision (historyIso.stateEquiv history).1)
      (action :
        G.InfoAction i
          (G.infoAt history i hsource hsource_nonterminal)),
      H.actionEquiv (historyIso.stateEquiv history) i htarget
          htarget_nonterminal
          (cast
            (congrArg (H.InfoAction i)
              (map_infoAt history i hsource
                hsource_nonterminal htarget
                htarget_nonterminal))
            (infoActionEquiv i
              (G.infoAt history i hsource hsource_nonterminal)
              action)) =
        historyIso.actionEquiv history
          (G.actionEquiv history i hsource
            hsource_nonterminal action)

namespace Iso

variable {G H : ControlledObservedGame N}

/-- Strict isomorphisms are determined by their carrier equivalences. -/
@[ext]
theorem ext (e f : G.Iso H)
    (hhistory : e.historyIso = f.historyIso)
    (hobservation : e.observationEquiv = f.observationEquiv)
    (hpublic : e.publicEquiv = f.publicEquiv)
    (hinfoState : e.infoStateEquiv = f.infoStateEquiv)
    (hinfoAction : HEq e.infoActionEquiv f.infoActionEquiv) :
    e = f := by
  cases e
  cases f
  cases hhistory
  cases hobservation
  cases hpublic
  cases hinfoState
  cases hinfoAction
  rfl

/-- Exact correspondence of external root presentations. -/
def PreservesRootPresentations
    (e : G.Iso H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history ↔
      targetRoots.IsRoot (e.historyIso.stateEquiv history)

/-- Forget invertibility while retaining the directional carrier map. -/
def toHom (e : G.Iso H) : G.Hom H where
  historyHom := e.historyIso.toHom
  map_init := e.map_init
  map_mover := e.map_mover
  mapObservation := fun i => e.observationEquiv i
  map_observe := e.map_observe
  mapPublic := e.publicEquiv
  map_publicObserve := e.map_publicObserve
  mapInfo := fun i => e.infoStateEquiv i
  map_infoAt := e.map_infoAt
  mapInfoAction := fun i information =>
    e.infoActionEquiv i information

/-- Exact root correspondence implies directional root mapping. -/
theorem mapsRootPresentations
    (e : G.Iso H)
    {sourceRoots : G.ContinuationRootPresentation}
    {targetRoots : H.ContinuationRootPresentation}
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots) :
    e.toHom.MapsRootPresentations sourceRoots targetRoots :=
  fun history hroot => (hroots history).mp hroot

/-- The information-state equivalence of a strict game isomorphism restricts
to represented strategy coordinates. -/
def representedInfoEquiv (e : G.Iso H) (i : N) :
    G.RepresentedInfo i ≃ H.RepresentedInfo i where
  toFun information := by
    refine ⟨e.infoStateEquiv i information.1, ?_⟩
    rcases information.2 with ⟨witness⟩
    let targetHistory := e.historyIso.stateEquiv witness.history
    have htargetMover :
        H.base.mover targetHistory.1 = some i := by
      rw [e.map_mover witness.history]
      exact witness.mover
    have htargetDecision :
        H.base.toArena.IsDecision targetHistory.1 :=
      (e.historyIso.isDecision_iff witness.history).1 witness.decision
    refine ⟨{
      history := targetHistory
      mover := htargetMover
      decision := htargetDecision
      infoAt_eq := ?_
    }⟩
    exact
      (e.map_infoAt witness.history i witness.mover witness.decision
        htargetMover htargetDecision).symm.trans
        (congrArg (e.infoStateEquiv i) witness.infoAt_eq)
  invFun information := by
    refine ⟨(e.infoStateEquiv i).symm information.1, ?_⟩
    rcases information.2 with ⟨witness⟩
    let sourceHistory := e.historyIso.stateEquiv.symm witness.history
    have hsourceMover :
        G.base.mover sourceHistory.1 = some i := by
      rw [← e.map_mover sourceHistory]
      simpa [sourceHistory] using witness.mover
    have hsourceDecision :
        G.base.toArena.IsDecision sourceHistory.1 :=
      (e.historyIso.isDecision_iff sourceHistory).2 (by
        simpa [sourceHistory] using witness.decision)
    have htargetMover :
        H.base.mover (e.historyIso.stateEquiv sourceHistory).1 = some i := by
      rw [e.map_mover sourceHistory]
      exact hsourceMover
    have htargetDecision :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv sourceHistory).1 :=
      (e.historyIso.isDecision_iff sourceHistory).1 hsourceDecision
    refine ⟨{
      history := sourceHistory
      mover := hsourceMover
      decision := hsourceDecision
      infoAt_eq := ?_
    }⟩
    apply (e.infoStateEquiv i).injective
    calc
      e.infoStateEquiv i
          (G.infoAt sourceHistory i hsourceMover hsourceDecision) =
          H.infoAt (e.historyIso.stateEquiv sourceHistory) i
            htargetMover htargetDecision :=
        e.map_infoAt sourceHistory i hsourceMover hsourceDecision
          htargetMover htargetDecision
      _ = information.1 := by
        simpa [sourceHistory] using witness.infoAt_eq
      _ = e.infoStateEquiv i ((e.infoStateEquiv i).symm information.1) := by
        simp
  left_inv information := by
    apply Subtype.ext
    simp
  right_inv information := by
    apply Subtype.ext
    simp

/-- The pure-strategy equivalence induced by information fibers. -/
def strategyEquiv (e : G.Iso H) (i : N) :
    G.PureStrategy i ≃ H.PureStrategy i :=
  (e.representedInfoEquiv i).piCongr fun information =>
    e.infoActionEquiv i information.1

/-- Cast-stable information-action equivalence at corresponding decision
histories. -/
def infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1) :
    G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal) ≃
      H.InfoAction i
        (H.infoAt (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal) :=
  Equiv.fiberEquivAt
    (e.infoStateEquiv i)
    (e.infoActionEquiv i)
    (G.infoAt history i hsource hsource_nonterminal)
    (H.infoAt (e.historyIso.stateEquiv history) i htarget
      htarget_nonterminal)
    (e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal)

@[simp]
theorem infoActionEquivAt_apply
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    e.infoActionEquivAt history i hsource hsource_nonterminal
        htarget htarget_nonterminal action =
      cast
        (congrArg (H.InfoAction i)
          (e.map_infoAt history i hsource hsource_nonterminal
            htarget htarget_nonterminal))
        (e.infoActionEquiv i
          (G.infoAt history i hsource hsource_nonterminal)
          action) :=
  rfl

/-- Realization of the local information-action equivalence commutes with
the strict concrete history-action equivalence. -/
theorem map_infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1)
    (action :
      G.InfoAction i
        (G.infoAt history i hsource hsource_nonterminal)) :
    H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget
        htarget_nonterminal
        (e.infoActionEquivAt
          history i hsource hsource_nonterminal htarget
          htarget_nonterminal action) =
      e.historyIso.actionEquiv history
        (G.actionEquiv history i hsource
          hsource_nonterminal action) :=
  e.map_infoActionAt history i hsource hsource_nonterminal
    htarget htarget_nonterminal action

/-- Map a complete payoff-free pure profile. -/
def mapProfile (e : G.Iso H)
    (profile : G.PureProfile) : H.PureProfile :=
  fun i => e.strategyEquiv i (profile i)

/-- Mapping a pure profile and selecting its concrete action commutes exactly
with the history-Arena action equivalence. -/
theorem map_actionAt
    (e : G.Iso H)
    (profile : G.PureProfile)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1) :
    PureProfile.actionAt H (e.mapProfile profile)
        (e.historyIso.stateEquiv history) i htarget
        htarget_nonterminal =
      e.historyIso.actionEquiv history
        (PureProfile.actionAt G profile history i hsource
          hsource_nonterminal) := by
  unfold PureProfile.actionAt PureStrategy.actionAt
  let sourceInformation :=
    G.representedInfoAt history i hsource hsource_nonterminal
  let targetInformation :=
    H.representedInfoAt (e.historyIso.stateEquiv history) i
      htarget htarget_nonterminal
  have hinfo :
      e.infoStateEquiv i
          (G.infoAt history i hsource hsource_nonterminal) =
        H.infoAt (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal :=
    e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal
  have hrepresented :
      e.representedInfoEquiv i sourceInformation = targetInformation :=
    Subtype.ext hinfo
  have hchoice :
      e.mapProfile profile i
          targetInformation =
        e.infoActionEquivAt history i hsource
          hsource_nonterminal htarget htarget_nonterminal
          (profile i sourceInformation) := by
    rw [infoActionEquivAt_apply]
    simpa [sourceInformation, targetInformation,
      representedInfoEquiv] using
      Equiv.piCongr_apply_of_eq
        (W := fun information : G.RepresentedInfo i =>
          G.InfoAction i information.1)
        (Z := fun information : H.RepresentedInfo i =>
          H.InfoAction i information.1)
        (e.representedInfoEquiv i)
        (fun information => e.infoActionEquiv i information.1)
        (profile i)
        sourceInformation targetInformation hrepresented
  rw [hchoice]
  exact
    e.map_infoActionEquivAt history i hsource
      hsource_nonterminal htarget htarget_nonterminal
      (profile i sourceInformation)

/-- Mapping a unilateral update commutes with strict profile transport. -/
theorem mapProfile_update [DecidableEq N]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (who : N) (deviation : G.PureStrategy who) :
    e.mapProfile (Function.update profile who deviation) =
      Function.update (e.mapProfile profile) who
        (e.strategyEquiv who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

/-- Identity strict payoff-free isomorphism. -/
def refl (G : ControlledObservedGame N) : G.Iso G where
  historyIso := Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  observationEquiv := fun _ => Equiv.refl _
  map_observe := by intro i history; rfl
  publicEquiv := Equiv.refl _
  map_publicObserve := by intro history; rfl
  map_publicOf := by intro i observation; rfl
  infoStateEquiv := fun _ => Equiv.refl _
  map_infoObserve := by intro i information; rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    congr
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    rfl

/-- The information equality used by strict-isomorphism composition. -/
def transInfoAt {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (hmiddle :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (hmiddle_nonterminal :
      H.base.toArena.IsDecision (e.historyIso.stateEquiv history).1)
    (htarget :
      K.base.mover
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)).1 = some i)
    (htarget_nonterminal :
      K.base.toArena.IsDecision
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)).1) :
    (e.infoStateEquiv i).trans (f.infoStateEquiv i)
        (G.infoAt history i hsource hsource_nonterminal) =
      K.infoAt
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)) i htarget
          htarget_nonterminal :=
  (congrArg (f.infoStateEquiv i)
    (e.map_infoAt history i hsource hsource_nonterminal
      hmiddle hmiddle_nonterminal)).trans
      (f.map_infoAt
        (e.historyIso.stateEquiv history)
        i hmiddle hmiddle_nonterminal htarget
        htarget_nonterminal)

/-- Compose strict payoff-free observed-game isomorphisms. -/
def trans {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K) : G.Iso K where
  historyIso := e.historyIso.trans f.historyIso
  map_init := by
    change
      f.historyIso.stateEquiv
          (e.historyIso.stateEquiv
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        Arena.HistoryFrom.nil K.base.toArena K.base.init
    rw [e.map_init, f.map_init]
  map_mover := by
    intro history
    change
      K.base.mover
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history)).1 =
        G.base.mover history.1
    rw [f.map_mover, e.map_mover]
  observationEquiv := fun i =>
    (e.observationEquiv i).trans (f.observationEquiv i)
  map_observe := by
    intro i history
    change
      f.observationEquiv i
          (e.observationEquiv i (G.observe i history)) =
        K.observe i
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_observe, f.map_observe]
  publicEquiv := e.publicEquiv.trans f.publicEquiv
  map_publicObserve := by
    intro history
    change
      f.publicEquiv (e.publicEquiv (G.publicObserve history)) =
        K.publicObserve
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_publicObserve, f.map_publicObserve]
  map_publicOf := by
    intro i observation
    change
      f.publicEquiv
          (e.publicEquiv (G.publicOf i observation)) =
        K.publicOf i
          (f.observationEquiv i
            (e.observationEquiv i observation))
    rw [e.map_publicOf, f.map_publicOf]
  infoStateEquiv := fun i =>
    (e.infoStateEquiv i).trans (f.infoStateEquiv i)
  map_infoObserve := by
    intro i information
    change
      f.observationEquiv i
          (e.observationEquiv i
            (G.infoObserve i information)) =
        K.infoObserve i
          (f.infoStateEquiv i
            (e.infoStateEquiv i information))
    rw [e.map_infoObserve, f.map_infoObserve]
  infoActionEquiv := fun i information =>
    (e.infoActionEquiv i information).trans
      (f.infoActionEquiv i
        (e.infoStateEquiv i information))
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    let hmiddle :
        H.base.mover
            (e.historyIso.stateEquiv history).1 =
          some i := by
      rw [e.map_mover history]
      exact hsource
    let hmiddle_nonterminal :
        H.base.toArena.IsDecision
          (e.historyIso.stateEquiv history).1 :=
      (e.historyIso.isDecision_iff history).mp hsource_nonterminal
    exact
      e.transInfoAt f history i hsource hsource_nonterminal
        hmiddle hmiddle_nonterminal htarget htarget_nonterminal
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    let middleHistory :=
      e.historyIso.stateEquiv history
    let hmiddle :
        H.base.mover middleHistory.1 = some i := by
      rw [e.map_mover history]
      exact hsource
    let hmiddle_nonterminal :
        H.base.toArena.IsDecision middleHistory.1 :=
      (e.historyIso.isDecision_iff history).mp hsource_nonterminal
    let sourceInformation :=
      G.infoAt history i hsource hsource_nonterminal
    let middleInformation :=
      H.infoAt middleHistory i hmiddle hmiddle_nonterminal
    have hFirst :
        e.infoStateEquiv i sourceInformation =
          middleInformation :=
      e.map_infoAt history i hsource hsource_nonterminal
        hmiddle hmiddle_nonterminal
    have hSecond :
        f.infoStateEquiv i middleInformation =
          K.infoAt
            (f.historyIso.stateEquiv middleHistory)
            i htarget htarget_nonterminal :=
      f.map_infoAt middleHistory i hmiddle hmiddle_nonterminal
        htarget htarget_nonterminal
    let middleAction :=
      cast
        (congrArg (H.InfoAction i) hFirst)
        (e.infoActionEquiv i sourceInformation action)
    let targetAction :=
      cast
        (congrArg (K.InfoAction i) hSecond)
        (f.infoActionEquiv i middleInformation middleAction)
    have hcast :
        cast
            (congrArg (K.InfoAction i)
              (e.transInfoAt f history i
                hsource hsource_nonterminal
                hmiddle hmiddle_nonterminal
                htarget htarget_nonterminal))
            (f.infoActionEquiv i
              (e.infoStateEquiv i sourceInformation)
              (e.infoActionEquiv i sourceInformation action)) =
          targetAction := by
      exact
        Equiv.fiberEquivAt_trans_apply
          (W := G.InfoAction i)
          (Z := H.InfoAction i)
          (V := K.InfoAction i)
          (e.infoStateEquiv i)
          (f.infoStateEquiv i)
          (e.infoActionEquiv i)
          (f.infoActionEquiv i)
          sourceInformation middleInformation
          (K.infoAt
            (f.historyIso.stateEquiv middleHistory)
            i htarget htarget_nonterminal)
          hFirst hSecond action
    change
      K.actionEquiv
          (f.historyIso.stateEquiv middleHistory)
          i htarget htarget_nonterminal
          (cast
            (congrArg (K.InfoAction i)
              (e.transInfoAt f history i
                hsource hsource_nonterminal
                hmiddle hmiddle_nonterminal
                htarget htarget_nonterminal))
            (f.infoActionEquiv i
              (e.infoStateEquiv i sourceInformation)
              (e.infoActionEquiv i sourceInformation action))) =
        f.historyIso.actionEquiv middleHistory
          (e.historyIso.actionEquiv history
            (G.actionEquiv history i hsource
              hsource_nonterminal action))
    rw [hcast]
    calc
      K.actionEquiv
          (f.historyIso.stateEquiv middleHistory)
          i htarget htarget_nonterminal targetAction =
        f.historyIso.actionEquiv middleHistory
          (H.actionEquiv middleHistory i hmiddle
            hmiddle_nonterminal
            middleAction) := by
              exact
                f.map_infoActionAt
                  middleHistory i hmiddle hmiddle_nonterminal
                  htarget htarget_nonterminal middleAction
      _ = f.historyIso.actionEquiv middleHistory
          (e.historyIso.actionEquiv history
            (G.actionEquiv history i hsource
              hsource_nonterminal action)) := by
              exact congrArg
                (f.historyIso.actionEquiv middleHistory)
                (e.map_infoActionAt
                  history i hsource hsource_nonterminal
                  hmiddle hmiddle_nonterminal action)

/-- Strict composition preserves exact external-root correspondence. -/
theorem trans_preservesRootPresentations
    {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K)
    {sourceRoots : G.ContinuationRootPresentation}
    {middleRoots : H.ContinuationRootPresentation}
    {targetRoots : K.ContinuationRootPresentation}
    (he : e.PreservesRootPresentations sourceRoots middleRoots)
    (hf : f.PreservesRootPresentations middleRoots targetRoots) :
    (e.trans f).PreservesRootPresentations
      sourceRoots targetRoots := by
  intro history
  exact (he history).trans
    (hf (e.historyIso.stateEquiv history))

/-! ### Inverse strict isomorphisms -/

/-- Inverse equivalence of one dependent information-action fiber. -/
def inverseInfoActionEquiv
    (e : G.Iso H) (i : N)
    (targetInformation : H.InfoState i) :
    H.InfoAction i targetInformation ≃
      G.InfoAction i
        ((e.infoStateEquiv i).symm targetInformation) :=
  (Equiv.cast
      (congrArg (H.InfoAction i)
        ((e.infoStateEquiv i).apply_symm_apply
          targetInformation))).symm.trans
    (e.infoActionEquiv i
      ((e.infoStateEquiv i).symm targetInformation)).symm

/-- Reverse the information square at one mapped history. -/
theorem inverseInfoAt
    (e : G.Iso H)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover
          (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1) :
    (e.infoStateEquiv i).symm
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal) =
      G.infoAt history i hsource hsource_nonterminal := by
  apply (e.infoStateEquiv i).injective
  simpa using
    (e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal).symm

private theorem cast_inverseFiber
    {α β : Type*} {W : α → Type*} {Z : β → Type*}
    (base : α ≃ β)
    (fiber : ∀ source, W source ≃ Z (base source))
    (source sourceBack : α) (target : β)
    (hforward : base source = target)
    (hright : base sourceBack = target)
    (hleft : sourceBack = source)
    (value : Z target) :
    cast (congrArg W hleft)
        ((fiber sourceBack).symm
          (cast (congrArg Z hright).symm value)) =
      (fiber source).symm
        (cast (congrArg Z hforward).symm value) := by
  subst sourceBack
  rfl

private theorem cast_inverseInfoActionEquiv
    (e : G.Iso H) (i : N)
    (sourceInformation : G.InfoState i)
    (targetInformation : H.InfoState i)
    (hforward :
      e.infoStateEquiv i sourceInformation =
        targetInformation)
    (hback :
      (e.infoStateEquiv i).symm targetInformation =
        sourceInformation)
    (action : H.InfoAction i targetInformation) :
    cast
        (congrArg (G.InfoAction i) hback)
        (e.inverseInfoActionEquiv i targetInformation action) =
      (e.infoActionEquiv i sourceInformation).symm
        (cast
          (congrArg (H.InfoAction i) hforward).symm
          action) := by
  exact
    cast_inverseFiber
      (e.infoStateEquiv i) (e.infoActionEquiv i)
      sourceInformation
      ((e.infoStateEquiv i).symm targetInformation)
      targetInformation hforward
      ((e.infoStateEquiv i).apply_symm_apply targetInformation)
      hback action

private theorem cast_inverseHistoryActionEquiv
    {A B : Arena} (e : A.Iso B)
    (source : A.State) (target : B.State)
    (hforward : e.stateEquiv source = target)
    (hback : e.stateEquiv.symm target = source)
    (action : B.Action target) :
    cast (congrArg A.Action hback)
        (e.inverseActionEquiv target action) =
      (e.actionEquiv source).symm
        (cast (congrArg B.Action hforward).symm action) := by
  exact
    cast_inverseFiber e.stateEquiv e.actionEquiv
      source (e.stateEquiv.symm target) target
      hforward (e.stateEquiv.apply_symm_apply target)
      hback action

private theorem actionEquiv_heq_of_history_eq
    (G : ControlledObservedGame N) (i : N)
    {first second : G.base.History}
    (hhistory : first = second)
    (hfirst : G.base.mover first.1 = some i)
    (hfirst_nonterminal : G.base.toArena.IsDecision first.1)
    (hsecond : G.base.mover second.1 = some i)
    (hsecond_nonterminal : G.base.toArena.IsDecision second.1)
    (firstAction :
      G.InfoAction i
        (G.infoAt first i hfirst hfirst_nonterminal))
    (secondAction :
      G.InfoAction i
        (G.infoAt second i hsecond hsecond_nonterminal))
    (haction : firstAction ≍ secondAction) :
    G.actionEquiv first i hfirst hfirst_nonterminal
        firstAction ≍
      G.actionEquiv second i hsecond hsecond_nonterminal
        secondAction := by
  subst second
  have hmover : hsecond = hfirst :=
    Subsingleton.elim _ _
  cases hmover
  have hnonterminal : hsecond_nonterminal = hfirst_nonterminal :=
    Subsingleton.elim _ _
  cases hnonterminal
  cases haction
  rfl

private theorem inverse_infoActionAt
    (e : G.Iso H)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hsource_nonterminal : G.base.toArena.IsDecision history.1)
    (htarget :
      H.base.mover
          (e.historyIso.stateEquiv history).1 = some i)
    (htarget_nonterminal :
      H.base.toArena.IsDecision
        (e.historyIso.stateEquiv history).1)
    (action :
      H.InfoAction i
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal)) :
    G.actionEquiv history i hsource hsource_nonterminal
        (cast
          (congrArg (G.InfoAction i)
            (e.inverseInfoAt history i hsource
              hsource_nonterminal htarget htarget_nonterminal))
          (e.inverseInfoActionEquiv i
            (H.infoAt
              (e.historyIso.stateEquiv history) i htarget
              htarget_nonterminal)
            action)) =
      cast
        (congrArg G.base.unfold.Action
          (e.historyIso.stateEquiv.symm_apply_apply history))
        (e.historyIso.inverseActionEquiv
            (e.historyIso.stateEquiv history)
          (H.actionEquiv
            (e.historyIso.stateEquiv history)
            i htarget htarget_nonterminal action)) := by
  have hinfo :
      e.infoStateEquiv i
          (G.infoAt history i hsource hsource_nonterminal) =
        H.infoAt
          (e.historyIso.stateEquiv history) i htarget
          htarget_nonterminal :=
    e.map_infoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal
  rw [cast_inverseInfoActionEquiv e i
    (G.infoAt history i hsource hsource_nonterminal)
    (H.infoAt
      (e.historyIso.stateEquiv history) i htarget
      htarget_nonterminal)
    hinfo
    (e.inverseInfoAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal)]
  rw [cast_inverseHistoryActionEquiv e.historyIso
    history (e.historyIso.stateEquiv history)
    rfl (e.historyIso.stateEquiv.symm_apply_apply history)]
  apply (e.historyIso.actionEquiv history).injective
  simpa using
    (e.map_infoActionAt history i hsource hsource_nonterminal
      htarget htarget_nonterminal
      ((e.infoActionEquiv i
        (G.infoAt history i hsource hsource_nonterminal)).symm
          (cast
            (congrArg (H.InfoAction i) hinfo).symm
            action))).symm

/-- Reverse a strict payoff-free observed-game isomorphism. -/
def symm (e : G.Iso H) : H.Iso G where
  historyIso := e.historyIso.symm
  map_init := by
    change
      e.historyIso.stateEquiv.symm
          (Arena.HistoryFrom.nil
            H.base.toArena H.base.init) =
        Arena.HistoryFrom.nil G.base.toArena G.base.init
    apply e.historyIso.stateEquiv.injective
    rw [e.historyIso.stateEquiv.apply_symm_apply, e.map_init]
  map_mover := by
    intro history
    simpa using
      (e.map_mover
        (e.historyIso.stateEquiv.symm history)).symm
  observationEquiv := fun i => (e.observationEquiv i).symm
  map_observe := by
    intro i history
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_observe i
        (e.historyIso.stateEquiv.symm history)).symm
  publicEquiv := e.publicEquiv.symm
  map_publicObserve := by
    intro history
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicObserve
        (e.historyIso.stateEquiv.symm history)).symm
  map_publicOf := by
    intro i observation
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicOf i
        ((e.observationEquiv i).symm observation)).symm
  infoStateEquiv := fun i => (e.infoStateEquiv i).symm
  map_infoObserve := by
    intro i information
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_infoObserve i
        ((e.infoStateEquiv i).symm information)).symm
  infoActionEquiv := e.inverseInfoActionEquiv
  map_infoAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource hsource_nonterminal
      htarget htarget_nonterminal
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    have htarget_nonterminal' :
        G.base.toArena.IsDecision sourceHistory.1 := by
      simpa [Arena.Iso.symm] using htarget_nonterminal
    simpa [Arena.Iso.symm] using
      e.inverseInfoAt sourceHistory i
        htarget' htarget_nonterminal'
        hsource hsource_nonterminal
  map_infoActionAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    have htarget_nonterminal' :
        G.base.toArena.IsDecision sourceHistory.1 := by
      simpa [Arena.Iso.symm] using htarget_nonterminal
    have hcore :=
      e.inverse_infoActionAt
        sourceHistory i htarget' htarget_nonterminal'
        hsource hsource_nonterminal action
    apply eq_of_heq
    refine HEq.trans ?_ ((heq_iff_eq.mpr hcore).trans ?_)
    · apply actionEquiv_heq_of_history_eq G i
        (e.historyIso.stateEquiv.symm_apply_apply sourceHistory)
        htarget htarget_nonterminal
        htarget' htarget_nonterminal'
      exact
        (cast_heq _ _).trans
          (cast_heq _ _).symm
    · exact cast_heq _ _

/-- Inverting exact root correspondence reverses its direction. -/
theorem symm_preservesRootPresentations
    (e : G.Iso H)
    {sourceRoots : G.ContinuationRootPresentation}
    {targetRoots : H.ContinuationRootPresentation}
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots) :
    e.symm.PreservesRootPresentations
      targetRoots sourceRoots := by
  intro targetHistory
  let sourceHistory :=
    e.historyIso.stateEquiv.symm targetHistory
  have hmap :
      e.historyIso.stateEquiv sourceHistory =
        targetHistory :=
    e.historyIso.stateEquiv.apply_symm_apply targetHistory
  simpa [symm, sourceHistory, hmap] using
    (hroots sourceHistory).symm

/-- Identity is a left unit for strict composition. -/
@[simp]
theorem refl_trans (e : G.Iso H) :
    (refl G).trans e = e := by
  apply Iso.ext
  · exact Arena.Iso.refl_trans e.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Identity is a right unit for strict composition. -/
@[simp]
theorem trans_refl (e : G.Iso H) :
    e.trans (refl H) = e := by
  apply Iso.ext
  · exact Arena.Iso.trans_refl e.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Strict composition is associative. -/
theorem trans_assoc
    {K L : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K) (g : K.Iso L) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply Iso.ext
  · exact Arena.Iso.trans_assoc
      e.historyIso f.historyIso g.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

end Iso

end ExtensiveGame.ControlledObservedGame
