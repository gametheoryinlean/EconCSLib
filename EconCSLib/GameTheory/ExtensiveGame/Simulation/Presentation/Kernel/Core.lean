/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory

/-!
# Presentation.Kernel.Core — kernel-valued observed-game presentations

This module separates the structural `ObservedGame` from its stochastic laws.
Player randomization and the fixed chance law are supplied as measurable
kernels. The finite-law `ObservedChanceGame` interface is connected through
separate presentation certificates.

A `MeasurableKernelPresentation` fixes:

* an explicit measurable complete-history model;
* measurable event information;
* a history-dependent measurable realization of abstract actions;
* the embedding of original player information;
* a concrete measurable chance-action kernel.

A `KernelBehavioralProfile` then supplies a measurable abstract-action kernel
indexed by the fixed information statistic.  At chance prefixes its realized
law must equal the presentation's fixed chance kernel.  At player prefixes the
abstract kernel is the strategic choice and may be atomic, non-atomic, or
mixed.

The fixed chance law is stated on concrete dependent action bundles.  This is
intentional: distinct abstract laws can induce the same concrete law through a
non-injective realization kernel, so demanding abstract equality would be
stronger than behavioral equivalence and would prevent an exact embedding of
some existing presentations.

The module reuses the established realized-information compiler and
Ionescu--Tulcea event executor.  It does not assert automatic measurability of
arbitrary function-valued strategies or measurable selection for arbitrary
dependent action families.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedGame

universe uN uU uI uC

variable {N : Type uN} {U : Type uU}

/-- Structural measurable data and a fixed chance law for an observed game.

Player stochastic laws are deliberately absent.  The chance kernel is allowed
to inspect the complete event prefix; this covers history-dependent nature
moves without pretending that nature has a player information state. -/
structure MeasurableKernelPresentation
    (G : ObservedGame N U)
    (model : MeasurableHistoryModel G) where
  /-- Fixed measurable information statistic on finite joint event prefixes. -/
  information :
    MeasurableKernelArena.EventInformation.{uI} model.toArena
  /-- Fixed measurable interpretation of abstract actions. -/
  realization :
    MeasurableKernelArena.EventInformation.ActionRealization.{uC}
      information
  /-- Map original player information into the analytic information carrier. -/
  playerInformation :
    (time : ℕ) →
      (Σ i : N, G.InfoState i) →
        information.Information time
  /-- At a player-controlled prefix, analytic information is exactly the image
  of the original player information state. -/
  player_informationAt :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (i : N)
      (hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState
              time events).1 =
          some i)
      (hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState
            time events).1),
      information.informationAt time events =
        playerInformation time
          ⟨i,
            G.infoAt
              (MeasurableKernelArena.latestEventState
                time events)
              i hmover
              (G.base.toArena.isDecision_of_not_isTerminal _
                hnonterminal)⟩
  /-- Fixed realized chance-action law.  Values away from chance prefixes are
  semantically irrelevant. -/
  chanceKernel :
    (time : ℕ) →
      Kernel
        (model.toArena.EventPrefix time)
        model.toArena.ActionBundle
  /-- The fixed chance kernel is globally s-finite. -/
  chanceKernel_isSFinite :
    ∀ time, IsSFiniteKernel (chanceKernel time)

namespace MeasurableKernelPresentation

variable
  {G : ObservedGame N U}
  {model : MeasurableHistoryModel G}

instance instChanceKernelIsSFinite
    (presentation : MeasurableKernelPresentation G model)
    (time : ℕ) :
    IsSFiniteKernel (presentation.chanceKernel time) :=
  presentation.chanceKernel_isSFinite time

/-- A measurable kernel-valued behavioral profile.

The underlying realized policy supplies terminal zero mass, normalization, and
almost-sure legality.  `chance_eq` prevents a strategic profile from changing
the presentation's fixed nature law. -/
structure KernelBehavioralProfile
    (presentation : MeasurableKernelPresentation G model) where
  /-- Information-indexed measurable abstract action laws. -/
  policy :
    MeasurableKernelArena.EventInformation.RealizedActionPolicy
      presentation.realization
  /-- The realized law agrees exactly with the fixed chance kernel at every
  nonterminal chance prefix. -/
  chance_eq :
    ∀ (time : ℕ)
      (events : model.toArena.EventPrefix time)
      (_hnonterminal :
        ¬ G.base.isTerminal
          (MeasurableKernelArena.latestEventState time events).1)
      (_hmover :
        G.base.mover
            (MeasurableKernelArena.latestEventState time events).1 =
          none),
      policy.realizedKernel time events =
        presentation.chanceKernel time events

namespace KernelBehavioralProfile

variable
  {presentation : MeasurableKernelPresentation G model}

/-- Compile a kernel-valued behavioral profile to the reusable raw joint-event
policy. -/
noncomputable def compiledPolicy
    (profile : presentation.KernelBehavioralProfile) :
    model.toArena.EventHistoryActionPolicy :=
  profile.policy.toEventHistoryActionPolicy

@[simp]
theorem compiledPolicy_kernel
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time) :
    profile.compiledPolicy.kernel time events =
      profile.policy.realizedKernel time events :=
  rfl

/-- Exact fixed chance law after compilation. -/
theorem compiledPolicy_kernel_of_chance
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    profile.compiledPolicy.kernel time events =
      presentation.chanceKernel time events := by
  rw [compiledPolicy_kernel]
  exact profile.chance_eq time events hnonterminal hmover

/-- Once a behavioral profile inhabits the presentation, the fixed chance law
is normalized at every represented nonterminal chance prefix.  Keeping this
certificate on profiles permits an exact compatibility adapter even when an
older raw profile type is empty. -/
theorem chance_isProbability
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    IsProbabilityMeasure
      (presentation.chanceKernel time events) := by
  rw [← profile.chance_eq time events hnonterminal hmover]
  exact
    profile.compiledPolicy.nonterminal_isProbability
      time events hnonterminal

/-- Once a behavioral profile inhabits the presentation, the fixed chance law
lies in the current concrete action fiber almost surely. -/
theorem chance_ae_legal
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    ∀ᵐ stateAction ∂presentation.chanceKernel time events,
      stateAction ∈
        model.toArena.actionFiber
          (MeasurableKernelArena.latestEventState time events) := by
  rw [← profile.chance_eq time events hnonterminal hmover]
  exact profile.compiledPolicy.legal time events hnonterminal

/-- With measurable state singletons, almost-sure chance legality recovers
the legacy measure-one action-fiber equation. -/
theorem chance_legal
    [MeasurableSingletonClass model.toArena.State]
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    presentation.chanceKernel time events
        (model.toArena.actionFiber
          (MeasurableKernelArena.latestEventState time events)) =
      1 := by
  rw [← profile.chance_eq time events hnonterminal hmover]
  exact
    profile.compiledPolicy.legal_mass_one
      time events hnonterminal

/-- Any two profiles in one presentation induce the same concrete chance law.
-/
theorem compiledPolicy_kernel_of_chance_eq
    (first second : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (hnonterminal :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    first.compiledPolicy.kernel time events =
      second.compiledPolicy.kernel time events := by
  rw [
    first.compiledPolicy_kernel_of_chance
      time events hnonterminal hmover,
    second.compiledPolicy_kernel_of_chance
      time events hnonterminal hmover]

/-- Equal original player information forces equal abstract action laws.

The result is stated before realization, which is the correct level for
information-set consistency when concrete dependent action fibers differ. -/
theorem abstractKernel_eq_of_player_infoAt_eq
    (profile : presentation.KernelBehavioralProfile)
    (time : ℕ)
    (events₁ events₂ : model.toArena.EventPrefix time)
    (i : N)
    (hmover₁ :
      G.base.mover
          (MeasurableKernelArena.latestEventState
            time events₁).1 =
        some i)
    (hnonterminal₁ :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₁).1)
    (hmover₂ :
      G.base.mover
          (MeasurableKernelArena.latestEventState
            time events₂).1 =
        some i)
    (hnonterminal₂ :
      ¬ G.base.isTerminal
        (MeasurableKernelArena.latestEventState time events₂).1)
    (hsame :
      G.infoAt
          (MeasurableKernelArena.latestEventState time events₁)
          i hmover₁
          (G.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal₁) =
        G.infoAt
          (MeasurableKernelArena.latestEventState time events₂)
          i hmover₂
          (G.base.toArena.isDecision_of_not_isTerminal _
            hnonterminal₂)) :
    profile.policy.abstractKernel time
        (presentation.information.informationAt time events₁) =
      profile.policy.abstractKernel time
        (presentation.information.informationAt time events₂) := by
  apply profile.policy.abstractKernel_eq_of_informationAt_eq
  rw [
    presentation.player_informationAt time events₁ i hmover₁
      hnonterminal₁,
    presentation.player_informationAt time events₂ i hmover₂
      hnonterminal₂,
    hsame]

/-- `after` is a unilateral deviation by `who` when every other player's
abstract decision law is unchanged at every represented decision prefix.

Chance consistency is structural because both profiles already agree with the
fixed `presentation.chanceKernel`.  No equality between concrete laws at
different histories is asserted. -/
def IsUnilateralDeviation
    (who : N)
    (before after : presentation.KernelBehavioralProfile) :
    Prop :=
  ∀ (time : ℕ)
    (events : model.toArena.EventPrefix time)
    (i : N)
    (_hmover :
      G.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i),
    i ≠ who →
      before.policy.abstractKernel time
          (presentation.information.informationAt time events) =
        after.policy.abstractKernel time
          (presentation.information.informationAt time events)

/-- A profile is a unilateral deviation from itself. -/
theorem isUnilateralDeviation_refl
    (who : N)
    (profile : presentation.KernelBehavioralProfile) :
    profile.IsUnilateralDeviation who profile := by
  intro _time _events _i _hmover _hne
  rfl

/-- Unilateral-deviation agreement away from one player is transitive. -/
theorem IsUnilateralDeviation.trans
    {who : N}
    {first second third : presentation.KernelBehavioralProfile}
    (hfirst : first.IsUnilateralDeviation who second)
    (hsecond : second.IsUnilateralDeviation who third) :
    first.IsUnilateralDeviation who third := by
  intro time events i hmover hne
  exact
    (hfirst time events i hmover hne).trans
      (hsecond time events i hmover hne)

/-- Complete joint state/action path law generated by a measurable
kernel-valued behavioral profile. -/
noncomputable def eventPathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Measure (ℕ → model.toArena.PathEvent) :=
  profile.compiledPolicy.pathMeasure
    model.toArena_terminalSet_measurable
    initialHistory

/-- Complete state-path law obtained by forgetting recorded actions. -/
noncomputable def statePathMeasure
    (profile : presentation.KernelBehavioralProfile)
    (initialHistory : CompleteHistory G) :
    Measure (ℕ → model.toArena.State) :=
  profile.compiledPolicy.statePathMeasure
    model.toArena_terminalSet_measurable
    initialHistory

end KernelBehavioralProfile

end MeasurableKernelPresentation

end ExtensiveGame.ObservedGame
