/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.FiniteLaw.Coupling

/-!
# Discrete probability-kernel arenas

Executable discrete stochastic transition systems and coupling-based
simulations.

This module is the implementation leaf for finite discrete execution.
`KernelArena` is the discrete stochastic analogue of `Arena`: an action
selects a normalized `FiniteLaw` of successor states rather than one deterministic
successor.
The simulation relation uses an explicit coupling of source and target
successor laws. Consequently it preserves probability mass, not merely the
existence of support paths.

This layer is representation-neutral. In particular, a FOSG macro step can
use a joint action here, while a serialized extensive-form implementation may
use a different state space and action presentation.

For non-atomic successor laws and genuine Mathlib Markov kernels, use
`MeasurableKernelArena`. `KernelArena.toMeasurable` embeds this discrete layer
there exactly.

## Main definitions

* `KernelArena` — dependent actions and normalized stochastic transitions.
* `KernelArena.Hom` — a functional transition-kernel morphism.
* `KernelArena.Simulation` — action matching by relational finite-law couplings.

## Main result

* `KernelArena.Hom.toSimulation` — strict kernel morphisms induce stochastic
  simulations.
-/

/-- A discrete stochastic transition arena.

`next s a` is a `FiniteLaw`, so normalization is enforced by construction. -/
structure KernelArena where
  /-- The stochastic state space. -/
  State : Type*
  /-- Available actions at a state. -/
  Action : State → Type*
  /-- The normalized successor-state law after choosing an action. -/
  next : (s : State) → Action s → FiniteLaw State

namespace KernelArena

/-- A strict morphism of probability-kernel Arenas. -/
structure Hom (A B : KernelArena) where
  /-- Map source states to target states. -/
  state : A.State → B.State
  /-- Map each dependent source action to a target action. -/
  action : (s : A.State) → A.Action s → B.Action (state s)
  /-- Pushing the source successor law through the state map gives exactly the
  target successor law. -/
  map_next :
    ∀ (s : A.State) (a : A.Action s),
      (A.next s a).map state =
        B.next (state s) (action s a)

namespace Hom

variable {A B : KernelArena}

/-- Identity strict kernel-Arena morphism. -/
def id (A : KernelArena) : A.Hom A where
  state := _root_.id
  action := fun _ => _root_.id
  map_next := by
    intro s a
    exact FiniteLaw.map_id (A.next s a)

end Hom

/-- A stochastic forward simulation.

At related states, every source action has a target action such that the two
successor laws admit a coupling supported on the state relation. -/
structure Simulation (A B : KernelArena) where
  /-- Relation between source and target macro states. -/
  Rel : A.State → B.State → Prop
  /-- Match every source action and all of its probability mass. -/
  match_action :
    ∀ {s : A.State} {t : B.State}, Rel s t →
      ∀ a : A.Action s,
        Σ b : B.Action t,
          FiniteLaw.RelCoupling Rel (A.next s a) (B.next t b)

/-- Every strict kernel-Arena morphism induces a stochastic simulation on the
graph of its state map. -/
def Hom.toSimulation {A B : KernelArena} (f : A.Hom B) :
    A.Simulation B where
  Rel := fun source target => f.state source = target
  match_action := by
    intro source target hrelated action
    subst target
    let graph : A.State →
        {pair : A.State × B.State // f.state pair.1 = pair.2} :=
      fun nextSource =>
        ⟨(nextSource, f.state nextSource), rfl⟩
    let joint := (A.next source action).map graph
    have hleft :
        (joint.map fun pair => pair.1.1) = A.next source action := by
      simp only [joint]
      rw [FiniteLaw.map_comp]
      simpa [graph, Function.comp_def] using
        FiniteLaw.map_id (A.next source action)
    have hright :
        (joint.map fun pair => pair.1.2) =
          B.next (f.state source) (f.action source action) := by
      simp only [joint]
      rw [FiniteLaw.map_comp]
      calc
        (A.next source action).map
            ((fun pair => pair.1.2) ∘ graph) =
            (A.next source action).map f.state := by
          rfl
        _ = B.next (f.state source) (f.action source action) :=
          f.map_next source action
    exact
      ⟨f.action source action,
        { joint := joint
          leftEquivalent := FiniteLaw.Equivalent.of_eq hleft
          rightEquivalent := FiniteLaw.Equivalent.of_eq hright
          leftPositive := fun outcome => by rw [hleft]
          rightPositive := fun outcome => by rw [hright] }⟩

end KernelArena
