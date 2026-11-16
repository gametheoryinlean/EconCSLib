/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation

/-!
# Executable finite kernel-valued behavioral profiles

This module is the measure-free effective subdomain of the analytic
`KernelBehavioralProfile` interface.  It keeps the same two-stage decision
model while replacing both stages by exact rational finite laws:

1. an information-indexed law selects an abstract action;
2. a prefix-dependent realization law selects a concrete dependent action.

`EffectiveKernelPresentation` owns the fixed information statistic, action
realization, executable terminal test, chance classifier, and concrete chance
law.  `EffectiveKernelBehavioralProfile` supplies only the abstract strategy
laws and proves that their concrete realization agrees with the fixed chance
law at chance prefixes.

The profile compiles through `EventInformation.RealizedActionPolicy`, then
reuses the ordinary finite event-history executor and coherent effective path
law.  No path law or expected value is supplied as an input to the algorithm.

Finite support at each input does not imply measurable dependence on a
general information carrier.  Consequently, the local weighted-Dirac
representation certificates and the exact bridge to the analytic
`KernelBehavioralProfile.compiledPolicy` live in
`Simulation.Presentation.Kernel.EffectiveBehavioralProfile`.

## Main definitions

* `KernelArena.EffectiveKernelPresentation` — fixed executable presentation
  data, including chance and terminal queries;
* `KernelArena.EffectiveKernelBehavioralProfile` — finite abstract strategy
  laws with exact realized-chance compatibility;
* `toRealizedActionPolicy` and `compiledPolicy` — the A06 finite realization
  compiler and its raw action-recording policy;
* `finitePrefixLawFrom` and `effectivePathLawFrom` — exact bounded and
  coherent finite-horizon execution.
-/

namespace KernelArena

universe uI uC

/-- Fixed executable data for a finite-law kernel-valued presentation.

The chance classifier is a Boolean so callers can query it directly.  Its
interpretation as a particular game's `mover = none` branch belongs to a
semantic representation certificate.  The chance law is typed in the
current dependent action fiber, making concrete legality structural. -/
structure EffectiveKernelPresentation (A : KernelArena) where
  /-- Executable statistic through which abstract strategy laws factor. -/
  information : EventInformation.{uI} A
  /-- Prefix-dependent finite realization of abstract actions. -/
  realization :
    EventInformation.ActionRealization.{uC} information
  /-- Explicit decision procedure for terminal states. -/
  terminalDecision :
    (state : A.State) → Decidable (IsEmpty (A.Action state))
  /-- Executable classifier for nonterminal chance prefixes. -/
  isChance :
    (time : ℕ) → A.EventPrefix time → Bool
  /-- Fixed concrete chance law at a represented nonterminal prefix. -/
  chanceLaw :
    (time : ℕ) →
      (history : A.EventPrefix time) →
      ¬ IsEmpty (A.Action history.latestState) →
      FiniteLaw (A.Action history.latestState)

/-- An executable behavioral profile over a fixed finite-law presentation.

`abstractLaw?` is killed at represented terminal information and normalized
at every represented nonterminal information value.  At a chance prefix its
finite abstract law, after the fixed history-dependent realization, must be
exactly the presentation's concrete chance law.  No equality of abstract
chance laws is imposed: distinct abstract laws may have the same concrete
realization, matching the analytic interface. -/
structure EffectiveKernelBehavioralProfile
    {A : KernelArena}
    (presentation : A.EffectiveKernelPresentation) where
  /-- Optional exact finite abstract-action law at each information value. -/
  abstractLaw? :
    (time : ℕ) →
      presentation.information.Information time →
      Option
        (FiniteLaw
          (presentation.realization.AbstractAction time))
  /-- Every represented terminal prefix has killed abstract action mass. -/
  terminal_none :
    ∀ time history,
      IsEmpty (A.Action history.latestState) →
        abstractLaw? time
          (presentation.information.informationAt time history) = none
  /-- Every represented nonterminal prefix has a finite abstract law. -/
  nonterminal_isSome :
    ∀ time history,
      ¬ IsEmpty (A.Action history.latestState) →
        (abstractLaw? time
          (presentation.information.informationAt time history)).isSome
  /-- Realization of the selected abstract law equals the fixed concrete
  chance law at every represented nonterminal chance prefix. -/
  chance_eq :
    ∀ (time : ℕ)
      (history : A.EventPrefix time)
      (hnonterminal : ¬ IsEmpty (A.Action history.latestState)),
      presentation.isChance time history = true →
        ((abstractLaw? time
            (presentation.information.informationAt time history)).get
              (nonterminal_isSome time history hnonterminal)).bind
            (presentation.realization.realizationLaw time history) =
          presentation.chanceLaw time history hnonterminal

namespace EffectiveKernelBehavioralProfile

variable
  {A : KernelArena}
  {presentation : A.EffectiveKernelPresentation}

variable (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)

/-- The finite abstract law selected at a represented nonterminal prefix. -/
def abstractLawAt
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    FiniteLaw (presentation.realization.AbstractAction time) :=
  (profile.abstractLaw? time
      (presentation.information.informationAt time history)).get
    (profile.nonterminal_isSome time history hnonterminal)

@[simp]
theorem some_abstractLawAt
    (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    some (profile.abstractLawAt time history hnonterminal) =
      profile.abstractLaw? time
        (presentation.information.informationAt time history) := by
  exact Option.some_get _

/-- Assemble the profile's finite abstract laws and the presentation's fixed
realization into the reusable A06 finite realized-action policy. -/
def toRealizedActionPolicy :
    EventInformation.RealizedActionPolicy presentation.realization where
  abstractLaw? := profile.abstractLaw?
  terminal_none := profile.terminal_none
  nonterminal_isSome := profile.nonterminal_isSome

@[simp]
theorem toRealizedActionPolicy_abstractLawAt
    (profile : KernelArena.EffectiveKernelBehavioralProfile presentation)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    profile.toRealizedActionPolicy.abstractLawAt
        time history hnonterminal =
      profile.abstractLawAt time history hnonterminal :=
  rfl

/-- Compile to the ordinary action-recording finite event-history policy. -/
def compiledPolicy :
    A.EventHistoryPolicy :=
  profile.toRealizedActionPolicy.toEventHistoryPolicy

@[simp]
theorem compiledPolicy_apply
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    profile.compiledPolicy time history hnonterminal =
      (profile.abstractLawAt time history hnonterminal).bind
        (presentation.realization.realizationLaw time history) :=
  rfl

/-- At a chance prefix the compiled concrete action algorithm is exactly the
presentation's fixed chance law. -/
theorem compiledPolicy_of_chance
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState))
    (hchance : presentation.isChance time history = true) :
    profile.compiledPolicy time history hnonterminal =
      presentation.chanceLaw time history hnonterminal := by
  exact profile.chance_eq time history hnonterminal hchance

/-- Terminal-aware query for the compiled concrete action-bundle law. -/
def finiteActionLaw?
    (time : ℕ) (history : A.EventPrefix time) :
    Option (FiniteLaw A.ActionBundle) := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  exact profile.compiledPolicy.actionLaw? time history

@[simp]
theorem finiteActionLaw?_eq_none_iff
    (time : ℕ) (history : A.EventPrefix time) :
    profile.finiteActionLaw? time history = none ↔
      IsEmpty (A.Action history.latestState) := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  exact profile.compiledPolicy.actionLaw?_eq_none_iff time history

/-- Execute the compiled profile for a bounded number of transitions while
retaining every state and selected-action occurrence. -/
def finitePrefixLawFrom
    (start : ℕ) (initialPrefix : A.EventPrefix start)
    (steps : ℕ) :
    FiniteLaw (A.EventPrefix (start + steps)) := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  exact profile.compiledPolicy.prefixLawFrom start initialPrefix steps

@[simp]
theorem finitePrefixLawFrom_zero
    (start : ℕ) (initialPrefix : A.EventPrefix start) :
    profile.finitePrefixLawFrom start initialPrefix 0 =
      FiniteLaw.pure initialPrefix :=
  rfl

@[simp]
theorem finitePrefixLawFrom_succ
    (start : ℕ) (initialPrefix : A.EventPrefix start)
    (steps : ℕ) :
    profile.finitePrefixLawFrom start initialPrefix (steps + 1) =
      (profile.finitePrefixLawFrom start initialPrefix steps).bind
        fun history =>
          (by
            letI (state : A.State) :
                Decidable (IsEmpty (A.Action state)) :=
              presentation.terminalDecision state
            exact
              (profile.compiledPolicy.stoppedStepLaw
                (start + steps) history).map history.snoc) :=
  rfl

/-- Coherent finite-horizon path law generated by the compiled profile from
an arbitrary absolute time and complete event prefix. -/
def effectivePathLawFrom
    (start : ℕ) (initialPrefix : A.EventPrefix start) :
    EventEffectivePathLawFrom A start initialPrefix := by
  letI (state : A.State) : Decidable (IsEmpty (A.Action state)) :=
    presentation.terminalDecision state
  exact profile.compiledPolicy.effectivePathLawFrom start initialPrefix

/-- Time-zero rooted coherent finite-horizon path law. -/
def effectivePathLaw
    (root : A.State) : EventEffectivePathLaw A root :=
  profile.effectivePathLawFrom 0 (EventPrefix.initial root)

@[simp]
theorem effectivePathLawFrom_prefixLaw
    (start : ℕ) (initialPrefix : A.EventPrefix start)
    (steps : ℕ) :
    (profile.effectivePathLawFrom start initialPrefix).prefixLaw steps =
      profile.finitePrefixLawFrom start initialPrefix steps :=
  rfl

@[simp]
theorem effectivePathLaw_prefixLaw_zero
    (root : A.State) :
    (profile.effectivePathLaw root).prefixLaw 0 =
      FiniteLaw.pure (EventPrefix.initial root) :=
  rfl

end EffectiveKernelBehavioralProfile

end KernelArena
