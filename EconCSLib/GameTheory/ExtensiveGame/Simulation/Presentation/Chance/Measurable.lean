/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized
import EconCSLib.Math.Probability.PMF.ToMeasure

/-!
# Presentation.Chance.Measurable — realized-information presentations

This module is the explicit measurable extension of the automatic
countable-discrete presentation.

A `MeasurablePresentation` is parameterized by a
`MeasurableHistoryModel`.  It supplies:

* a measurable event-information statistic;
* a fixed measurable realization kernel from abstract actions to dependent
  concrete history/action bundles;
* a measurable realized policy for every original behavioral profile;
* factorization through original player information at player histories;
* exact local player and chance action-kernel equations.

The two local equations replace a monolithic whole-policy equality.  Terminal
zero mass, normalization, legality, information consistency, and complete
joint/state path laws are inherited from the reusable realized-policy
executor.  This is a certificate-to-semantics constructor: once the explicitly
measurable local obligations are discharged, no additional global compilation
proof is required.

No countability or standard-Borel assumption is imposed by the generic
interface.  Standard-Borel models are a principal use case, while more general
measurable spaces remain valid when their kernels are supplied.  Conversely,
the interface does not claim that an arbitrary `BehavioralProfile` over an
uncountable information space is automatically measurable; `toPolicy` is
exactly where a model must establish that fact or choose a suitably measurable
information presentation.
-/

open MeasureTheory ProbabilityTheory

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uI uC

variable {N : Type uN} {U : Type uU}

/-- A local measurable compilation certificate for an observed chance game
over an explicitly measurable complete-history model.

The profile-independent `information` and `realization` fields make the
information partition and dependent interpretation of actions structural.
Only the abstract law inside `toPolicy` may vary with a behavioral profile. -/
structure MeasurablePresentation
    (G : ObservedChanceGame N U)
    (model : MeasurableHistoryModel G) where
  /-- Fixed measurable information statistic on finite joint event prefixes. -/
  information :
    MeasurableKernelArena.EventInformation.{uI} model.toArena
  /-- Fixed measurable interpretation of abstract actions. -/
  realization :
    MeasurableKernelArena.EventInformation.ActionRealization.{uC}
      information
  /-- Compile each original behavioral profile to a measurable abstract
  information policy. -/
  toPolicy :
    G.observed.BehavioralProfile →
      MeasurableKernelArena.EventInformation.RealizedActionPolicy
        realization
  /-- Supplied profile-independent concrete chance kernel. -/
  chanceKernel : (time : ℕ) →
    Kernel (model.toArena.EventPrefix time) model.toArena.ActionBundle
  /-- The supplied chance kernel is globally s-finite. -/
  chanceKernel_isSFinite : ∀ time, IsSFiniteKernel (chanceKernel time)
  /-- Every behavioral profile agrees with the supplied law at chance prefixes.
  No reference profile or default law is selected. -/
  chanceKernel_eq : ∀ (profile : G.observed.BehavioralProfile)
    (time : ℕ) (events : model.toArena.EventPrefix time)
    (_hnonterminal : ¬ G.observed.base.isTerminal
      (MeasurableKernelArena.latestEventState time events).1)
    (_hmover : G.observed.base.mover
      (MeasurableKernelArena.latestEventState time events).1 = none),
    chanceKernel time events = (toPolicy profile).realizedKernel time events
  /-- Map original player information into every time-indexed analytic
  information carrier. -/
  playerInformation :
    (time : ℕ) →
      (Σ i : N, G.observed.InfoState i) →
        information.Information time
  /-- At a player-controlled prefix, analytic information is exactly the image
  of the original player information state. -/
  player_informationAt :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (hmover :
        G.observed.base.mover
            (MeasurableKernelArena.latestEventState
              time events).1 =
          some i)
      (hnonterminal :
        ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState
            time events).1),
      information.informationAt time events =
        playerInformation time
          ⟨i,
            G.observed.infoAt
              (MeasurableKernelArena.latestEventState
                time events)
              i hmover
              (G.observed.base.toArena.isDecision_of_not_isTerminal
                _ hnonterminal)⟩
  /-- At a nonterminal player prefix, abstract selection followed by
  realization is exactly the original behavioral finite law on concrete legal
  history/action bundles. -/
  player_realizedKernel :
    ∀ (profile : G.observed.BehavioralProfile)
      (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (hnonterminal :
        ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (i : N)
      (hmover :
        G.observed.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          some i),
      (toPolicy profile).realizedKernel time events =
        finiteLawMeasure(
          (profile.actionLawAt G.observed
              (MeasurableKernelArena.latestEventState time events)
              i hmover hnonterminal).map
            (fun action =>
              (⟨MeasurableKernelArena.latestEventState time events,
                action⟩ :
                model.toArena.ActionBundle)))
  /-- At a nonterminal chance prefix, abstract selection followed by
  realization is exactly the declared chance finite law on concrete legal
  history/action bundles. -/
  chance_realizedKernel :
    ∀ (profile : G.observed.BehavioralProfile)
      (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (hnonterminal :
        ¬ G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (hmover :
        G.observed.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      (toPolicy profile).realizedKernel time events =
        finiteLawMeasure(
          (G.chanceKernel
              (MeasurableKernelArena.latestEventState time events)
              ⟨hmover, hnonterminal⟩).map
            (fun action =>
              (⟨MeasurableKernelArena.latestEventState time events,
                action⟩ :
                model.toArena.ActionBundle)))

namespace MeasurablePresentation

variable
  {G : ObservedChanceGame N U}
  {model : MeasurableHistoryModel G}

/-- Compile a measurable presentation to the reusable raw joint-event policy. -/
noncomputable def compiledPolicy
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile) :
    model.toArena.EventHistoryActionPolicy :=
  (presentation.toPolicy profile).toEventHistoryActionPolicy

@[simp]
theorem compiledPolicy_kernel
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time) :
    (presentation.compiledPolicy profile).kernel time events =
      (presentation.toPolicy profile).realizedKernel time events :=
  rfl

/-- Equal original player information states force equal abstract action
laws, independently of the concrete histories realizing those actions. -/
theorem abstractKernel_eq_of_player_infoAt_eq
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events₁ events₂ : model.toArena.EventPrefix time)
    (i : N)
    (hmover₁ :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState
            time events₁).1 =
        some i)
    (hnonterminal₁ :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₁).1)
    (hmover₂ :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState
            time events₂).1 =
        some i)
    (hnonterminal₂ :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₂).1)
    (hsame :
      G.observed.infoAt
          (MeasurableKernelArena.latestEventState time events₁)
          i hmover₁
          (G.observed.base.toArena.isDecision_of_not_isTerminal
            _ hnonterminal₁) =
        G.observed.infoAt
          (MeasurableKernelArena.latestEventState time events₂)
          i hmover₂
          (G.observed.base.toArena.isDecision_of_not_isTerminal
            _ hnonterminal₂)) :
    (presentation.toPolicy profile).abstractKernel time
        (presentation.information.informationAt time events₁) =
      (presentation.toPolicy profile).abstractKernel time
        (presentation.information.informationAt time events₂) := by
  apply
    (presentation.toPolicy profile).abstractKernel_eq_of_informationAt_eq
  rw [
    presentation.player_informationAt time events₁ i hmover₁
      hnonterminal₁,
    presentation.player_informationAt time events₂ i hmover₂
      hnonterminal₂,
    hsame]

/-- Exact compiled concrete player-action law. -/
theorem compiledPolicy_kernel_of_mover
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (i : N)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i) :
    (presentation.compiledPolicy profile).kernel time events =
      finiteLawMeasure(
        (profile.actionLawAt G.observed
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              model.toArena.ActionBundle))) := by
  rw [compiledPolicy_kernel]
  exact
    presentation.player_realizedKernel
      profile time events hnonterminal i hmover

/-- Exact compiled concrete chance-action law. -/
theorem compiledPolicy_kernel_of_chance
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    (presentation.compiledPolicy profile).kernel time events =
      finiteLawMeasure(
        (G.chanceKernel
            (MeasurableKernelArena.latestEventState time events)
            ⟨hmover, hnonterminal⟩).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              model.toArena.ActionBundle))) := by
  rw [compiledPolicy_kernel]
  exact
    presentation.chance_realizedKernel
      profile time events hnonterminal hmover

/-- Complete joint state/action path law generated by a measurable
presentation. -/
noncomputable def eventPathMeasure
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  (presentation.compiledPolicy profile).pathMeasure
    model.toArena_terminalSet_measurable
    initialHistory

/-- Complete state-path law obtained by forgetting recorded actions. -/
noncomputable def statePathMeasure
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Measure (ℕ → model.toArena.State) :=
  (presentation.compiledPolicy profile).statePathMeasure
    model.toArena_terminalSet_measurable
    initialHistory

/-- The supplied profile-independent measurable chance law. -/
def fixedChanceKernel
    (presentation : MeasurablePresentation G model) (time : ℕ) :
    Kernel (model.toArena.EventPrefix time) model.toArena.ActionBundle :=
  presentation.chanceKernel time

instance fixedChanceKernel_isSFinite
    (presentation : MeasurablePresentation G model) (time : ℕ) :
    IsSFiniteKernel (presentation.fixedChanceKernel time) :=
  presentation.chanceKernel_isSFinite time

/-- At a represented chance prefix, the supplied fixed chance kernel is
exactly the original chance finite law packaged as a concrete bundle measure. -/
theorem fixedChanceKernel_of_chance
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    presentation.fixedChanceKernel time events =
      finiteLawMeasure(
        (G.chanceKernel
            (MeasurableKernelArena.latestEventState time events)
            ⟨hmover, hnonterminal⟩).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              model.toArena.ActionBundle))) :=
  (presentation.chanceKernel_eq profile time events hnonterminal hmover).trans
    (presentation.chance_realizedKernel profile time events hnonterminal hmover)

/-- Forget the finite-law-specific local equations and obtain the general structural
kernel presentation. -/
def toKernelPresentation
    (presentation : MeasurablePresentation G model) :
    G.observed.MeasurableKernelPresentation model where
  information := presentation.information
  realization := presentation.realization
  playerInformation := presentation.playerInformation
  player_informationAt := presentation.player_informationAt
  chanceKernel := presentation.fixedChanceKernel
  chanceKernel_isSFinite := by
    intro time
    infer_instance

/-- Embed one existing finite-law behavioral profile as a general measurable
kernel-valued profile.  Its player and chance laws are unchanged. -/
def toKernelBehavioralProfile
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile) :
    presentation.toKernelPresentation.KernelBehavioralProfile where
  policy := presentation.toPolicy profile
  chance_eq := by
    intro time events hnonterminal hmover
    change
      (presentation.toPolicy profile).realizedKernel time events =
        presentation.fixedChanceKernel time events
    exact
      (presentation.chance_realizedKernel
        profile time events hnonterminal hmover).trans
        (presentation.fixedChanceKernel_of_chance
          profile time events hnonterminal hmover).symm

/-- The general kernel-profile adapter compiles to definitionally the same raw
event policy as the existing finite-law presentation. -/
theorem toKernelBehavioralProfile_compiledPolicy
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile) :
    (presentation.toKernelBehavioralProfile profile).compiledPolicy =
      presentation.compiledPolicy profile :=
  rfl

/-- The general adapter preserves the complete joint event-path law
definitionally. -/
theorem toKernelBehavioralProfile_eventPathMeasure
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (initialHistory : CompleteHistory G) :
    (presentation.toKernelBehavioralProfile profile).eventPathMeasure
        initialHistory =
      presentation.eventPathMeasure profile initialHistory :=
  rfl

/-- The general adapter preserves the complete state-path law
definitionally. -/
theorem toKernelBehavioralProfile_statePathMeasure
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (initialHistory : CompleteHistory G) :
    (presentation.toKernelBehavioralProfile profile).statePathMeasure
        initialHistory =
      presentation.statePathMeasure profile initialHistory :=
  rfl

end MeasurablePresentation

namespace AnalyticPresentation

variable {G : ObservedChanceGame N U}

/-- Every established top-measurable `AnalyticPresentation` is an exact
special case of the explicit measurable-history presentation.

The conversion changes no carrier, information statistic, realization
kernel, abstract policy, or concrete law.  It only replaces the old
monolithic raw-policy equality field by the new local player/chance equations,
which follow from that equality. The caller also supplies the fixed chance
kernel, its s-finiteness, and agreement at every represented chance prefix. -/
def toMeasurablePresentation
    (presentation : AnalyticPresentation G)
    (chanceKernel : (time : ℕ) → Kernel
      ((MeasurableHistoryModel.discrete G).toArena.EventPrefix time)
      (MeasurableHistoryModel.discrete G).toArena.ActionBundle)
    (chanceKernel_isSFinite : ∀ time, IsSFiniteKernel (chanceKernel time))
    (chanceKernel_eq : ∀ (profile : G.observed.BehavioralProfile)
      (time : ℕ)
      (events : (MeasurableHistoryModel.discrete G).toArena.EventPrefix time)
      (_hnonterminal : ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
      (_hmover : G.observed.base.mover
        (MeasurableKernelArena.latestEventState time events).1 = none),
      chanceKernel time events = (presentation.toPolicy profile).realizedKernel time events) :
    MeasurablePresentation G
      (MeasurableHistoryModel.discrete G) where
  information := presentation.information
  realization := presentation.realization
  toPolicy := presentation.toPolicy
  chanceKernel := chanceKernel
  chanceKernel_isSFinite := chanceKernel_isSFinite
  chanceKernel_eq := chanceKernel_eq
  playerInformation := presentation.playerInformation
  player_informationAt :=
    presentation.player_informationAt
  player_realizedKernel := by
    intro profile time events hnonterminal i hmover
    exact
      presentation.compiled_kernel_of_mover
        profile time events hnonterminal i hmover
  chance_realizedKernel := by
    intro profile time events hnonterminal hmover
    exact
      presentation.compiled_kernel_of_chance
        profile time events hnonterminal hmover

end AnalyticPresentation

end ExtensiveGame.ObservedChanceGame
