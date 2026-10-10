/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel

/-!
# Executable realization of finite abstract action laws

This module is the exact finite-law counterpart of the analytic realized
information interface.  An information policy first selects an abstract
action with a rational `FiniteLaw`; a fixed realization then selects a
concrete action in the dependent action fiber of the current state.  The two
finite choices compile by `FiniteLaw.bind`.

The abstract policy uses `Option (FiniteLaw ...)`.  `none` is required at
represented terminal prefixes, while a represented nonterminal prefix must
have a normalized finite law.  This is the executable analogue of a killed
analytic kernel: a normalized `FiniteLaw` is never used to pretend that a
probability law exists on an empty action type.

Concrete legality is enforced by the result type of `realizationLaw`.  It
returns `FiniteLaw (A.Action history.latestState)`, so compilation cannot put
mass in another state's dependent action fiber.  Mapping to
`A.ActionBundle` happens only after this typed realization.

This owner module is measure-free.  The weighted-Dirac interpretation and
the exact bridge to `MeasurableKernelArena.EventInformation.RealizedActionPolicy`
live in `Simulation.Kernel.FiniteRealizedInformation`.

## Main definitions

* `KernelArena.EventInformation` — an executable statistic of finite event
  prefixes;
* `EventInformation.ActionRealization` — finite concrete realization in the
  current dependent action fiber;
* `EventInformation.RealizedActionPolicy` — optional finite abstract laws at
  information values;
* `RealizedActionPolicy.abstractLawAt` and `realizedActionLaw` — the two local
  stages of executable action selection;
* `RealizedActionPolicy.realizedBundleLaw` — their exact `bind`/`map`
  compilation;
* `RealizedActionPolicy.toEventHistoryPolicy` — compilation to the ordinary
  action-recording finite executor.
-/

namespace KernelArena

universe uI uC

/-- A fixed, executable information statistic of finite event prefixes.

No enumeration of the information carrier is required: execution only
evaluates `informationAt` on the prefix currently being processed. -/
structure EventInformation (A : KernelArena) where
  /-- Information values available at each absolute event time. -/
  Information : ℕ → Type uI
  /-- Information represented by one complete finite event prefix. -/
  informationAt :
    (time : ℕ) → A.EventPrefix time → Information time

namespace EventInformation

variable {A : KernelArena}

/-- Fixed finite realization of abstract actions as concrete actions.

The result type records the latest state of the supplied prefix.  Hence every
atom is legal by construction and no decidable equality on states is needed. -/
structure ActionRealization
    (information : A.EventInformation) where
  /-- Common abstract action carrier at each absolute event time. -/
  AbstractAction : ℕ → Type uC
  /-- Exact finite concrete-action law at a prefix and abstract action. -/
  realizationLaw :
    (time : ℕ) →
      (history : A.EventPrefix time) →
      AbstractAction time →
      FiniteLaw (A.Action history.latestState)

/-- A finite abstract-action policy indexed by a fixed information statistic.

The optional law is defined on every information value.  The two certificates
constrain only values represented by concrete prefixes: terminal prefixes
must see `none`, and nonterminal prefixes must see `some` finite law. -/
structure RealizedActionPolicy
    {information : A.EventInformation}
    (realization : ActionRealization information) where
  /-- Exact abstract action law, killed with `none` where no move is made. -/
  abstractLaw? :
    (time : ℕ) →
      information.Information time →
      Option (FiniteLaw (realization.AbstractAction time))
  /-- Every represented terminal prefix has killed abstract action mass. -/
  terminal_none :
    ∀ time history,
      IsEmpty (A.Action history.latestState) →
        abstractLaw? time (information.informationAt time history) = none
  /-- Every represented nonterminal prefix has a normalized finite abstract
  action law. -/
  nonterminal_isSome :
    ∀ time history,
      ¬ IsEmpty (A.Action history.latestState) →
        (abstractLaw? time
          (information.informationAt time history)).isSome

namespace RealizedActionPolicy

variable
  {information : A.EventInformation}
  {realization : ActionRealization information}

/-- The finite abstract law selected at a represented nonterminal prefix. -/
def abstractLawAt
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    FiniteLaw (realization.AbstractAction time) :=
  (policy.abstractLaw? time
      (information.informationAt time history)).get
    (policy.nonterminal_isSome time history hnonterminal)

@[simp]
theorem some_abstractLawAt
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    some (policy.abstractLawAt time history hnonterminal) =
      policy.abstractLaw? time
        (information.informationAt time history) := by
  exact Option.some_get _

/-- Select an abstract action and realize it as a concrete action in the
current dependent action fiber.  This is executable `List.flatMap` through
`FiniteLaw.bind`. -/
def realizedActionLaw
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    FiniteLaw (A.Action history.latestState) :=
  (policy.abstractLawAt time history hnonterminal).bind
    (realization.realizationLaw time history)

/-- Bundle the structurally legal concrete action with its current state.

This is the finite-law value denoted by the corresponding analytic realized
kernel. -/
def realizedBundleLaw
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    FiniteLaw A.ActionBundle :=
  (policy.realizedActionLaw time history hnonterminal).map
    fun action => ⟨history.latestState, action⟩

/-- Compile finite abstract selection and finite realization to the ordinary
action-recording event-history executor. -/
def toEventHistoryPolicy
    (policy : RealizedActionPolicy realization) :
    A.EventHistoryPolicy :=
  fun time history hnonterminal =>
    policy.realizedActionLaw time history hnonterminal

@[simp]
theorem toEventHistoryPolicy_apply
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    policy.toEventHistoryPolicy time history hnonterminal =
      policy.realizedActionLaw time history hnonterminal :=
  rfl

/-- The compiled concrete algorithm is literally the product-weight
`flatMap` of abstract atoms and their realization atoms. -/
@[simp]
theorem realizedActionLaw_atoms
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    (policy.realizedActionLaw time history hnonterminal).atoms =
      (policy.abstractLawAt time history hnonterminal).atoms.flatMap
        (fun abstractAtom =>
          (realization.realizationLaw time history abstractAtom.1).atoms.map
            fun concreteAtom =>
              (concreteAtom.1, abstractAtom.2 * concreteAtom.2)) :=
  rfl

/-- The bundled compiler is exactly abstract selection, concrete realization,
then bundling with the current state. -/
theorem realizedBundleLaw_eq_bind_map
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState)) :
    policy.realizedBundleLaw time history hnonterminal =
      (policy.abstractLawAt time history hnonterminal).bind
        (fun abstractAction =>
          (realization.realizationLaw time history abstractAction).map
            fun action => ⟨history.latestState, action⟩) := by
  rw [realizedBundleLaw, realizedActionLaw, FiniteLaw.map_bind]

/-- Every positive atom of the bundled compiled law belongs to the current
state's action fiber, expressed without any state equality decision. -/
theorem realizedBundleLaw_atom_state
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history : A.EventPrefix time)
    (hnonterminal : ¬ IsEmpty (A.Action history.latestState))
    (bundle : A.ActionBundle)
    (hpositive :
      (policy.realizedBundleLaw time history hnonterminal).HasPositiveAtom
        bundle) :
    bundle.1 = history.latestState := by
  rw [realizedBundleLaw, FiniteLaw.hasPositiveAtom_map_iff] at hpositive
  obtain ⟨action, _haction, hbundle⟩ := hpositive
  exact (congrArg Sigma.fst hbundle).symm

/-- Equal information values force exactly equal optional abstract laws.
Concrete laws may still differ because realization is prefix-dependent. -/
theorem abstractLaw?_eq_of_informationAt_eq
    (policy : RealizedActionPolicy realization)
    (time : ℕ) (history₁ history₂ : A.EventPrefix time)
    (hsame :
      information.informationAt time history₁ =
        information.informationAt time history₂) :
    policy.abstractLaw? time
        (information.informationAt time history₁) =
      policy.abstractLaw? time
        (information.informationAt time history₂) := by
  rw [hsame]

end RealizedActionPolicy

end EventInformation

end KernelArena
