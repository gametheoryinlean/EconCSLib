/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.MorphismHierarchy

Conversions between strict observed-EFG isomorphisms and information
refinements.

The structural APIs deliberately expose different strengths:

* `ObservedGame.Iso` identifies histories, observations, public states,
  decision information, and indexed actions by equivalences;
* `ObservedGame.InformationRefinement` keeps history dynamics strict but only
  asks for forgetful maps on observations and decision information.

A strict isomorphism is therefore a special information refinement.  This
module makes that inclusion explicit, rather than requiring every theorem to
support the two structures independently.  Forgetful maps are the inverses of
the isomorphism's observation and information equivalences, while the action
lift is the original indexed action equivalence transported to the requested
target information state.

The induced pure and behavioral strategy maps are proved equal to the
pre-existing strict-isomorphism maps.  Hence their strategy-surjectivity
hypotheses hold automatically.  The same conversion is lifted to observed
chance games, where chance-kernel naturality is inherited exactly.

Private bounded-Nash derivations through information refinement serve as
hierarchy regressions, not alternative downstream entry points.
Strict-isomorphism clients should use
`ObservedGame.Iso.isPureNashOnRootsAtFuel_iff` and
`ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`.

## Main definitions

* `ObservedGame.Iso.toInformationRefinement`.
* `ObservedChanceGame.Iso.toInformationRefinement`.

## Main results

* `ObservedGame.Iso.toInformationRefinement_mapStrategy`.
* `ObservedGame.Iso.toInformationRefinement_strategySurjective`.
* `ObservedGame.Iso.toInformationRefinement_mapBehavioralStrategy`.
* `ObservedGame.Iso.toInformationRefinement_behavioralStrategySurjective`.
-/

namespace ExtensiveGame

namespace ObservedGame.Iso

variable {N U : Type*}
variable {G H : ObservedGame N U}

/-- A dependent family of equivalences commutes with transport of the common
base index. -/
private theorem dependent_equiv_apply_cast
    {α : Type*}
    {sourceFiber targetFiber : α → Type*}
    (fiberEquiv :
      ∀ index, sourceFiber index ≃ targetFiber index)
    {source target : α}
    (hindex : source = target)
    (value : sourceFiber source) :
    fiberEquiv target
        (cast
          (congrArg sourceFiber hindex)
          value) =
      cast
        (congrArg targetFiber hindex)
        (fiberEquiv source value) := by
  subst target
  rfl

/-- The strict information-action equivalence reindexed over an arbitrary
target information state.

The source information state is recovered with the inverse information
equivalence; the target action type is then transported along
`apply_symm_apply`. -/
def infoActionEquivOverTarget
    (e : G.Iso H) (i : N)
    (information : H.InfoState i) :
    G.InfoAction i
        ((e.infoStateEquiv i).symm information) ≃
      H.InfoAction i information :=
  Equiv.fiberEquivAt
    (e.infoStateEquiv i)
    (e.infoActionEquiv i)
    ((e.infoStateEquiv i).symm information)
    information
    ((e.infoStateEquiv i).apply_symm_apply information)

/-- Reindexing an action over a target information state agrees with first
mapping it at a corresponding source information state and then casting the
result to the target index. -/
private theorem infoActionEquivOverTarget_apply_of_eq
    (e : G.Iso H) (i : N)
    (source : G.InfoState i)
    (target : H.InfoState i)
    (hinfo :
      e.infoStateEquiv i source = target)
    (action : G.InfoAction i source) :
    e.infoActionEquivOverTarget i target
        (cast
          (congrArg (G.InfoAction i)
            ((e.infoStateEquiv i).eq_symm_apply.mpr
              hinfo))
          action) =
      cast
        (congrArg (H.InfoAction i) hinfo)
        (e.infoActionEquiv i source action) := by
  subst target
  unfold infoActionEquivOverTarget
  let hback :
      (e.infoStateEquiv i).symm
          (e.infoStateEquiv i source) =
        source :=
    (e.infoStateEquiv i).symm_apply_apply source
  let hforward :
      source =
        (e.infoStateEquiv i).symm
          (e.infoStateEquiv i source) :=
    hback.symm
  have hcanonical :
      (e.infoStateEquiv i).eq_symm_apply.mpr
          (Eq.refl
            (e.infoStateEquiv i source)) =
        hforward :=
    Subsingleton.elim _ _
  rw [hcanonical]
  have hnatural :=
    dependent_equiv_apply_cast
      (sourceFiber := G.InfoAction i)
      (targetFiber := fun information =>
        H.InfoAction i
          (e.infoStateEquiv i information))
      (e.infoActionEquiv i)
      hforward action
  simp only [Equiv.fiberEquivAt_apply]
  rw [hnatural]
  rw [cast_cast]

/-- Every strict observed-EFG isomorphism is, in particular, an information
refinement.

The target is viewed as the fine presentation.  Its observations and decision
information forget through the inverse strict equivalences.  Since those maps
are bijective, the resulting refinement has no genuine information gain. -/
def toInformationRefinement
    (e : G.Iso H) :
    G.InformationRefinement H where
  historyIso := e.historyIso
  map_init := e.map_init
  map_mover := e.map_mover
  map_payoff := e.map_payoff
  forgetObservation := fun i =>
    (e.observationEquiv i).symm
  forget_observe := by
    intro i history
    rw [← e.map_observe i history]
    exact
      (e.observationEquiv i).symm_apply_apply
        (G.observe i history)
  forgetPublic := e.publicEquiv.symm
  forget_publicObserve := by
    intro history
    rw [← e.map_publicObserve history]
    exact
      e.publicEquiv.symm_apply_apply
        (G.publicObserve history)
  forget_publicOf := by
    intro i observation
    apply e.publicEquiv.injective
    rw [e.publicEquiv.apply_symm_apply]
    rw [e.map_publicOf]
    rw [(e.observationEquiv i).apply_symm_apply]
  forgetInfo := fun i =>
    (e.infoStateEquiv i).symm
  forget_infoObserve := by
    intro i information
    apply (e.observationEquiv i).injective
    rw [(e.observationEquiv i).apply_symm_apply]
    rw [e.map_infoObserve]
    rw [(e.infoStateEquiv i).apply_symm_apply]
  infoActionEquiv :=
    e.infoActionEquivOverTarget
  map_infoAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal
    apply (e.infoStateEquiv i).injective
    rw [(e.infoStateEquiv i).apply_symm_apply]
    exact
      e.map_infoAt
        history i hsource hsource_nonterminal
        htarget htarget_nonterminal
  map_infoActionAt := by
    intro history i hsource hsource_nonterminal
      htarget htarget_nonterminal action
    let sourceInformation :=
      G.infoAt history i hsource hsource_nonterminal
    let targetInformation :=
      H.infoAt
        (e.historyIso.stateEquiv history)
        i htarget htarget_nonterminal
    have hinfo :
        e.infoStateEquiv i sourceInformation =
          targetInformation :=
      e.map_infoAt
        history i hsource hsource_nonterminal
        htarget htarget_nonterminal
    have hforget :
        sourceInformation =
          (e.infoStateEquiv i).symm
            targetInformation := by
      exact
        (e.infoStateEquiv i).eq_symm_apply.mpr
          hinfo
    have haction :
        e.infoActionEquivOverTarget
            i targetInformation
            (cast
              (congrArg (G.InfoAction i)
                hforget)
              action) =
          cast
            (congrArg (H.InfoAction i) hinfo)
            (e.infoActionEquiv
              i sourceInformation action) := by
      exact
        e.infoActionEquivOverTarget_apply_of_eq
          i sourceInformation targetInformation
          hinfo action
    rw [haction]
    exact
      e.map_infoActionAt
        history i hsource hsource_nonterminal
        htarget htarget_nonterminal action

/-- The refinement action lift induced by a strict isomorphism is exactly the
strict dependent action equivalence, evaluated through its inverse information
index. -/
theorem toInformationRefinement_mapStrategy
    (e : G.Iso H) (i : N)
    (strategy : G.PureStrategy i) :
    e.toInformationRefinement.mapStrategy
        i strategy =
      e.strategyEquiv i strategy := by
  funext information
  let sourceInformation :=
    e.toInformationRefinement.toControlled.forgetRepresentedInfo
      i information
  have hinformation :
      e.representedInfoEquiv i sourceInformation =
        information := by
    apply Subtype.ext
    exact (e.infoStateEquiv i).apply_symm_apply information.1
  change
    e.infoActionEquivOverTarget
        i information.1
        (strategy
          (e.toInformationRefinement.toControlled.forgetRepresentedInfo
            i information)) =
      e.strategyEquiv i strategy information
  symm
  exact
    Equiv.piCongr_apply_of_eq
      (W := fun information : G.RepresentedInfo i =>
        G.InfoAction i information.1)
      (Z := fun information : H.RepresentedInfo i =>
        H.InfoAction i information.1)
      (e.representedInfoEquiv i)
      (fun information =>
        e.representedInfoActionEquiv i information)
      strategy sourceInformation information
      hinformation

/-- Pure profile lifting through the induced refinement agrees with strict
profile transport. -/
theorem toInformationRefinement_mapProfile
    (e : G.Iso H)
    (profile : G.PureProfile) :
    e.toInformationRefinement.mapProfile profile =
      e.mapProfile profile := by
  funext i
  exact
    e.toInformationRefinement_mapStrategy
      i (profile i)

/-- A strict observed-EFG isomorphism, regarded as an information refinement,
automatically lifts every target pure strategy. -/
theorem toInformationRefinement_strategySurjective
    (e : G.Iso H) :
    e.toInformationRefinement.StrategySurjective := by
  intro i targetStrategy
  refine
    ⟨(e.strategyEquiv i).symm targetStrategy, ?_⟩
  rw [e.toInformationRefinement_mapStrategy]
  exact
    (e.strategyEquiv i).apply_symm_apply
      targetStrategy

/-- Behavioral strategy lifting through the induced refinement agrees with
strict behavioral strategy transport. -/
theorem toInformationRefinement_mapBehavioralStrategy
    (e : G.Iso H) (i : N)
    (strategy : G.BehavioralStrategy i) :
    e.toInformationRefinement.mapBehavioralStrategy
        i strategy =
      e.behavioralStrategyEquiv i strategy := by
  funext information
  let sourceInformation :=
    e.toInformationRefinement.toControlled.forgetRepresentedInfo
      i information
  have hinformation :
      e.representedInfoEquiv i sourceInformation =
        information := by
    apply Subtype.ext
    exact (e.infoStateEquiv i).apply_symm_apply information.1
  change
    (strategy
      (e.toInformationRefinement.toControlled.forgetRepresentedInfo
        i information)).map
        (e.infoActionEquivOverTarget
          i information.1) =
      e.behavioralStrategyEquiv i
        strategy information
  symm
  have hpi :=
    Equiv.piCongr_apply_of_eq
      (W := fun information : G.RepresentedInfo i =>
        FiniteLaw (G.InfoAction i information.1))
      (Z := fun information : H.RepresentedInfo i =>
        FiniteLaw (H.InfoAction i information.1))
      (e.representedInfoEquiv i)
      (fun information =>
        FiniteLaw.mapEquiv
          (e.representedInfoActionEquiv i information))
      strategy sourceInformation information
      hinformation
  unfold behavioralStrategyEquiv
  refine hpi.trans ?_
  change
    cast
        (congrArg
          (fun information =>
            FiniteLaw (H.InfoAction i information.1))
          hinformation)
        ((strategy sourceInformation).map
          (e.representedInfoActionEquiv
            i sourceInformation)) =
      (strategy sourceInformation).map
        (e.infoActionEquivOverTarget
          i information.1)
  rw [FiniteLaw.cast_map]
  apply congrArg
    (fun actionMap =>
      (strategy sourceInformation).map actionMap)
  funext action
  rfl

/-- Behavioral profile lifting through the induced refinement agrees with
strict behavioral profile transport. -/
theorem toInformationRefinement_mapBehavioralProfile
    (e : G.Iso H)
    (profile : G.BehavioralProfile) :
    e.toInformationRefinement.mapBehavioralProfile
        profile =
      e.mapBehavioralProfile profile := by
  funext i
  exact
    e.toInformationRefinement_mapBehavioralStrategy
      i (profile i)

/-- A strict observed-EFG isomorphism, regarded as an information refinement,
automatically lifts every target behavioral strategy. -/
theorem
    toInformationRefinement_behavioralStrategySurjective
    (e : G.Iso H) :
    e.toInformationRefinement.BehavioralStrategySurjective := by
  intro i targetStrategy
  refine
    ⟨(e.behavioralStrategyEquiv i).symm
        targetStrategy, ?_⟩
  rw [e.toInformationRefinement_mapBehavioralStrategy]
  exact
    (e.behavioralStrategyEquiv i).apply_symm_apply
      targetStrategy

end ObservedGame.Iso

namespace ObservedChanceGame.Iso

variable {N U : Type*}
variable {G H : ObservedChanceGame N U}

/-- Every strict observed chance-EFG isomorphism is a chance-aware
information refinement. -/
def toInformationRefinement
    (e : G.Iso H) :
    G.InformationRefinement H where
  observedRefinement :=
    e.observedIso.toInformationRefinement
  map_chanceKernel := by
    intro history hchance
    exact e.map_chanceKernel history hchance

/-- The chance-aware refinement induced by a strict isomorphism automatically
lifts every target behavioral strategy. -/
theorem
    toInformationRefinement_behavioralStrategySurjective
    (e : G.Iso H) :
    (e.toInformationRefinement.observedRefinement
      ).BehavioralStrategySurjective :=
  e.observedIso.toInformationRefinement_behavioralStrategySurjective

end ObservedChanceGame.Iso

end ExtensiveGame
