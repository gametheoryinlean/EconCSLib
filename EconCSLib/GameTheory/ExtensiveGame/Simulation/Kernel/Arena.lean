/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Kernel.Arena — measurable probability-kernel arenas

`KernelArena` is the executable discrete stochastic arena: its transitions are
`FiniteLaw` values with finite support and exact rational weights.
`MeasurableKernelArena` is the analytic extension boundary. It stores
a genuine Mathlib Markov kernel from the dependent state/action bundle to the
state space, so successor laws may be non-atomic.

The measurable space on the total action bundle

```lean
Σ state, Action state
```

is explicit data.  This avoids pretending that an arbitrary dependent family
of measurable action spaces automatically gives the intended measurable
structure on legal state/action pairs.

## Main definitions

* `MeasurableKernelArena` — dependent actions and a normalized measurable
  transition kernel.
* `MeasurableKernelArena.Hom` — measurable strict transition morphisms.
* `KernelArena.toMeasurable` — the exact discrete-to-analytic embedding.
* `KernelArena.Hom.toMeasurable` — reuse of strict discrete morphisms.

This module does not yet define measure-valued policies or trajectory laws.
Those require an explicit measurable legality condition for policy kernels and
belong in a subsequent execution layer.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

/-- A stochastic arena whose transition law is a genuine Markov kernel.

The kernel domain is the total bundle of legal state/action pairs.  Its Markov
property makes normalization structural while allowing atomic, continuous, or
mixed successor laws. -/
structure MeasurableKernelArena where
  /-- Measurable state space. -/
  State : Type uS
  /-- Legal actions at each state. -/
  Action : State → Type uA
  /-- Sigma algebra on states. -/
  stateMeasurable : MeasurableSpace State
  /-- Sigma algebra on the total bundle of legal state/action pairs. -/
  actionBundleMeasurable : MeasurableSpace (Σ state, Action state)
  /-- Forgetting the action from a legal state/action pair is measurable. -/
  stateProjection_measurable :
    @Measurable (Σ state, Action state) State
      actionBundleMeasurable stateMeasurable Sigma.fst
  /-- Measurable normalized successor law for every legal state/action pair. -/
  transition :
    @Kernel (Σ state, Action state) State
      actionBundleMeasurable stateMeasurable
  /-- Every transition law has total mass one. -/
  transition_isMarkov :
    @IsMarkovKernel (Σ state, Action state) State
      actionBundleMeasurable stateMeasurable transition

namespace MeasurableKernelArena

/-- The total space of legal state/action pairs. -/
abbrev ActionBundle (A : MeasurableKernelArena) :=
  Σ state, A.Action state

instance (A : MeasurableKernelArena) : MeasurableSpace A.State :=
  A.stateMeasurable

instance (A : MeasurableKernelArena) : MeasurableSpace A.ActionBundle :=
  A.actionBundleMeasurable

instance (A : MeasurableKernelArena) : IsMarkovKernel A.transition :=
  A.transition_isMarkov

/-- The successor measure after one legal state/action pair. -/
abbrev nextMeasure (A : MeasurableKernelArena)
    (state : A.State) (action : A.Action state) :
    Measure A.State :=
  A.transition ⟨state, action⟩

instance nextMeasure_isProbability (A : MeasurableKernelArena)
    (state : A.State) (action : A.Action state) :
    IsProbabilityMeasure (A.nextMeasure state action) :=
  inferInstance

/-- A strict measurable morphism of analytic kernel arenas.

Both the state map and the induced map on dependent legal-action bundles must
be measurable.  Successor laws commute exactly by measure pushforward. -/
structure Hom (A B : MeasurableKernelArena) where
  /-- Map source states to target states. -/
  state : A.State → B.State
  /-- The state map is measurable. -/
  state_measurable : Measurable state
  /-- Map every legal source action to a legal target action. -/
  action :
    (source : A.State) → A.Action source → B.Action (state source)
  /-- The induced map on total legal-action bundles is measurable. -/
  actionBundle_measurable :
    Measurable fun sourceAction : A.ActionBundle =>
      (⟨state sourceAction.1,
        action sourceAction.1 sourceAction.2⟩ : B.ActionBundle)
  /-- Transition measures commute exactly with state pushforward. -/
  map_transition :
    ∀ (source : A.State) (sourceAction : A.Action source),
      (A.nextMeasure source sourceAction).map state =
        B.nextMeasure (state source) (action source sourceAction)

namespace Hom

variable {A B C : MeasurableKernelArena}

/-- Identity strict morphism of a measurable kernel arena. -/
def id (A : MeasurableKernelArena) : A.Hom A where
  state := _root_.id
  state_measurable := measurable_id
  action := fun _ action => action
  actionBundle_measurable := measurable_id
  map_transition := by
    intro state action
    exact Measure.map_id

/-- Compose strict measurable kernel-arena morphisms. -/
def trans (f : A.Hom B) (g : B.Hom C) : A.Hom C where
  state := g.state ∘ f.state
  state_measurable := g.state_measurable.comp f.state_measurable
  action := fun state action =>
    g.action (f.state state) (f.action state action)
  actionBundle_measurable :=
    g.actionBundle_measurable.comp f.actionBundle_measurable
  map_transition := by
    intro state action
    calc
      (A.nextMeasure state action).map (g.state ∘ f.state) =
          ((A.nextMeasure state action).map f.state).map g.state := by
            rw [Measure.map_map
              g.state_measurable f.state_measurable]
      _ =
          (B.nextMeasure
            (f.state state) (f.action state action)).map g.state := by
            rw [f.map_transition]
      _ =
          C.nextMeasure
            (g.state (f.state state))
            (g.action (f.state state) (f.action state action)) :=
        g.map_transition _ _

end Hom

end MeasurableKernelArena

namespace KernelArena

/-- Regard a finite-law kernel arena as a measurable Markov-kernel arena.

Both source measurable spaces are discrete.  No countability assumption is
needed: each transition is the finite weighted sum of its Dirac atom measures,
and discreteness makes this family measurable. The finite-law normalization
proof gives total mass one. This does not embed arbitrary countably supported
real-weighted PMFs. -/
noncomputable def toMeasurable (A : KernelArena) :
    MeasurableKernelArena :=
  letI : MeasurableSpace A.State := ⊤
  letI : MeasurableSpace (Σ state, A.Action state) := ⊤
  {
    State := A.State
    Action := A.Action
    stateMeasurable := inferInstance
    actionBundleMeasurable := inferInstance
    stateProjection_measurable := by
      exact fun _ _ => MeasurableSpace.measurableSet_top
    transition :=
      { toFun := fun stateAction =>
          (A.next stateAction.1 stateAction.2).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
            0
        measurable' := Measurable.of_discrete }
    transition_isMarkov := by
      constructor
      intro stateAction
      change
        IsProbabilityMeasure
          ((A.next stateAction.1 stateAction.2).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
            0)
      constructor
      change
        ((A.next stateAction.1 stateAction.2).atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0) Set.univ = 1
      have hsum :
          ((A.next stateAction.1 stateAction.2).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
            0) Set.univ =
          ((FiniteLaw.totalWeight
            (A.next stateAction.1 stateAction.2).atoms : ℚ≥0) : ENNReal) := by
        have hzero : ((0 : ℚ≥0) : ENNReal) = 0 := by
          change (((0 : ℚ≥0) : NNReal) : ENNReal) = 0
          simp
        have hadd (p q : ℚ≥0) :
            ((p + q : ℚ≥0) : ENNReal) =
              (p : ENNReal) + (q : ENNReal) := by
          change (((p + q : ℚ≥0) : NNReal) : ENNReal) =
            ((p : NNReal) : ENNReal) + ((q : NNReal) : ENNReal)
          simp
        induction (A.next stateAction.1 stateAction.2).atoms with
        | nil => simp [FiniteLaw.totalWeight, hzero]
        | cons atom atoms ih =>
            simp [FiniteLaw.totalWeight, ih, hadd]
      rw [hsum, FiniteLaw.totalWeight_atoms]
      change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
      norm_num
  }

@[simp]
theorem toMeasurable_nextMeasure (A : KernelArena)
    (state : A.State) (action : A.Action state) :
    A.toMeasurable.nextMeasure state action =
      (A.next state action).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac A.State ⊤ atom.1 + rest)
        0 :=
  rfl

namespace Hom

variable {A B : KernelArena}

/-- A strict discrete kernel morphism is a strict measurable kernel morphism
after the exact finite weighted-Dirac embedding. -/
def toMeasurable (f : A.Hom B) :
    A.toMeasurable.Hom B.toMeasurable where
  state := f.state
  state_measurable := by
    change @Measurable A.State B.State ⊤ ⊤ f.state
    exact fun _ _ => MeasurableSpace.measurableSet_top
  action := f.action
  actionBundle_measurable := by
    change
      @Measurable
        (Σ state, A.Action state)
        (Σ state, B.Action state)
        ⊤ ⊤
        (fun sourceAction =>
          (⟨f.state sourceAction.1,
            f.action sourceAction.1 sourceAction.2⟩ :
            Σ state, B.Action state))
    exact fun _ _ => MeasurableSpace.measurableSet_top
  map_transition := by
    letI : MeasurableSpace A.State := ⊤
    letI : MeasurableSpace B.State := ⊤
    intro state action
    change
      @Measure.map A.State B.State ⊤ ⊤
          f.state
          ((A.next state action).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
            0) =
        (B.next (f.state state) (f.action state action)).atoms.foldr
          (fun atom rest =>
            (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
          0
    have hstate :
        @Measurable A.State B.State ⊤ ⊤ f.state :=
      fun _ _ => MeasurableSpace.measurableSet_top
    rw [← f.map_next]
    change
      @Measure.map A.State B.State ⊤ ⊤ f.state
          ((A.next state action).atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest) 0) =
        ((A.next state action).atoms.map
          (fun atom => (f.state atom.1, atom.2))).foldr
            (fun atom rest =>
              (atom.2 : ENNReal) • Measure.dirac atom.1 + rest) 0
    induction (A.next state action).atoms with
    | nil => simp
    | cons atom atoms ih =>
        simp only [List.foldr_cons, List.map_cons]
        rw [Measure.map_add _ _ hstate, Measure.map_smul,
          Measure.map_dirac' hstate, ih]

end Hom

end KernelArena
