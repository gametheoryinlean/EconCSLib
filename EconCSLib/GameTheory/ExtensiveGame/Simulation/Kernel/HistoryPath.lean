/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath

/-!
# Kernel.HistoryPath — finite-history-dependent measurable-kernel paths

This module removes the stationary state-Markov restriction from analytic
state-path execution. A `HistoryActionPolicy` supplies a measurable legal
action kernel at every natural-number time and finite state prefix. Its
terminal-absorbing history step drives an Ionescu--Tulcea probability measure
on infinite state paths.

The existing `ActionPolicy` embeds by reading the latest state. The embedded
history step and entire path measure are proved exactly equal to the existing
state-Markov constructions.

## Main definitions

* `MeasurableKernelArena.HistoryActionPolicy` — time- and
  state-prefix-dependent legal action kernels.
* `HistoryActionPolicy.pathStepKernel` — terminal-absorbing next-state kernel
  on finite prefixes.
* `HistoryActionPolicy.pathMeasure` — the resulting infinite state-path law.

## Main results

* `HistoryActionPolicy.pathStepKernel_isMarkov` — every history step is
  normalized.
* `HistoryActionPolicy.coordinateMeasure_succ` — the next coordinate law is
  obtained by integrating the history step against the complete prefix law.
* `ActionPolicy.toHistoryActionPolicy_pathMeasure` — a stationary policy's new
  path law is exactly the previously audited path law.

The recorded history currently consists of states. This module does not yet
construct a joint state/action path or impose observed information-set
consistency.
-/

open MeasureTheory ProbabilityTheory

universe uS uA

namespace MeasurableKernelArena

variable {A : MeasurableKernelArena}

/-- Finite state prefixes whose latest state is terminal. -/
def prefixTerminalSet (A : MeasurableKernelArena) (time : ℕ) :
    Set (Π index : Finset.Iic time, StateAt A index) :=
  {history | latestState time history ∈ A.terminalSet}

/-- Terminal finite prefixes form a measurable set whenever terminal states
do. -/
theorem measurableSet_prefixTerminalSet
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    MeasurableSet (A.prefixTerminalSet time) :=
  measurable_latestState time hterminal

/-- A measurable action policy depending on time and the complete finite
state prefix.

At a prefix ending in a terminal state the action kernel is killed. At every
other prefix it is a probability measure concentrated on the dependent action
fiber of the latest state. -/
structure HistoryActionPolicy (A : MeasurableKernelArena) where
  /-- Measurable, possibly killed, action kernel at each finite prefix. -/
  kernel :
    (time : ℕ) →
      Kernel
        (Π index : Finset.Iic time, StateAt A index)
        A.ActionBundle
  /-- Terminal prefixes produce no action mass. -/
  terminal_zero :
    ∀ time history,
      IsEmpty (A.Action (latestState time history)) →
        kernel time history = 0
  /-- Action mass is normalized at every nonterminal prefix. -/
  nonterminal_isProbability :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestState time history)) →
        IsProbabilityMeasure (kernel time history)
  /-- At a nonterminal prefix, the selected action lies in the latest
  state's legal fiber almost surely. -/
  legal :
    ∀ time history,
      ¬ IsEmpty (A.Action (latestState time history)) →
        ∀ᵐ stateAction ∂kernel time history,
          stateAction ∈ A.actionFiber (latestState time history)

namespace HistoryActionPolicy

/-- A history policy chooses a bundled action in the latest state's fiber
almost surely at every nonterminal prefix. -/
theorem ae_mem_actionFiber (policy : A.HistoryActionPolicy)
    (time : ℕ)
    (history : Π index : Finset.Iic time, StateAt A index)
    (hnonterminal :
      ¬ IsEmpty (A.Action (latestState time history))) :
    ∀ᵐ stateAction ∂policy.kernel time history,
      stateAction ∈ A.actionFiber (latestState time history) := by
  exact policy.legal time history hnonterminal

/-- With measurable state singletons, genuine history-policy legality implies
the numerical measure-one fiber equation. -/
theorem legal_mass_one (policy : A.HistoryActionPolicy)
    [MeasurableSingletonClass A.State]
    (time : ℕ)
    (history : Π index : Finset.Iic time, StateAt A index)
    (hnonterminal :
      ¬ IsEmpty (A.Action (latestState time history))) :
    policy.kernel time history
        (A.actionFiber (latestState time history)) = 1 := by
  letI : IsProbabilityMeasure (policy.kernel time history) :=
    policy.nonterminal_isProbability time history hnonterminal
  have hmeasure :=
    (ae_mem_iff_measure_eq
      (A.measurableSet_actionFiber
        (latestState time history)).nullMeasurableSet).mp
      (policy.ae_mem_actionFiber time history hnonterminal)
  simpa using hmeasure

/-- Select an action from a finite prefix and then apply the arena transition.
-/
noncomputable def actionStepKernel (policy : A.HistoryActionPolicy)
    (time : ℕ) :
    Kernel
      (Π index : Finset.Iic time, StateAt A index)
      (StateAt A (time + 1)) :=
  A.transition ∘ₖ policy.kernel time

/-- Terminal-absorbing next-state kernel for a finite state prefix. -/
noncomputable def pathStepKernel (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    Kernel
      (Π index : Finset.Iic time, StateAt A index)
      (StateAt A (time + 1)) := by
  classical
  exact Kernel.piecewise
    (A.measurableSet_prefixTerminalSet hterminal time)
    (Kernel.deterministic
      (latestState time) (measurable_latestState time))
    (policy.actionStepKernel time)

/-- Every history-dependent, terminal-absorbing next-state kernel is Markov.
-/
instance pathStepKernel_isMarkov (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    IsMarkovKernel (policy.pathStepKernel hterminal time) := by
  classical
  constructor
  intro history
  rw [pathStepKernel, Kernel.piecewise_apply]
  split_ifs with hhistory
  · infer_instance
  · have hnonterminal :
        ¬ IsEmpty (A.Action (latestState time history)) := by
      simpa only [prefixTerminalSet, terminalSet, Set.mem_setOf_eq]
        using hhistory
    change
      IsProbabilityMeasure
        ((policy.kernel time history).bind A.transition)
    letI : IsProbabilityMeasure (policy.kernel time history) :=
      policy.nonterminal_isProbability time history hnonterminal
    exact MeasureTheory.isProbabilityMeasure_bind
      A.transition.aemeasurable
      (Filter.Eventually.of_forall fun stateAction => inferInstance)

/-- A terminal prefix produces the Dirac law at its latest state. -/
@[simp]
theorem pathStepKernel_apply_terminal
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ)
    (history : Π index : Finset.Iic time, StateAt A index)
    (hstate : IsEmpty (A.Action (latestState time history))) :
    policy.pathStepKernel hterminal time history =
      Measure.dirac (latestState time history) := by
  classical
  rw [pathStepKernel, Kernel.piecewise_apply, if_pos]
  · exact Kernel.deterministic_apply
      (measurable_latestState time) history
  · simpa only [prefixTerminalSet, terminalSet, Set.mem_setOf_eq]
      using hstate

/-- A nonterminal prefix selects an action and binds it with the arena
transition. -/
@[simp]
theorem pathStepKernel_apply_nonterminal
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ)
    (history : Π index : Finset.Iic time, StateAt A index)
    (hstate : ¬ IsEmpty (A.Action (latestState time history))) :
    policy.pathStepKernel hterminal time history =
      (policy.kernel time history).bind A.transition := by
  classical
  rw [pathStepKernel, Kernel.piecewise_apply, if_neg]
  · rfl
  · simpa only [prefixTerminalSet, terminalSet, Set.mem_setOf_eq]
      using hstate

/-- Infinite discrete-event state-path law for a history-dependent policy. -/
noncomputable def pathMeasure (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    Measure (ℕ → A.State) :=
  Kernel.traj (policy.pathStepKernel hterminal) 0
    (fun _ => initialState)

/-- The history-dependent state-path law is a probability measure. -/
instance pathMeasure_isProbability (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    IsProbabilityMeasure
      (policy.pathMeasure hterminal initialState) := by
  rw [pathMeasure]
  infer_instance

/-- Joint law of the state prefix through `time`. -/
noncomputable def prefixMeasure (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure (Π _index : Finset.Iic time, A.State) :=
  (policy.pathMeasure hterminal initialState).map
    (Preorder.frestrictLe time)

/-- Marginal state law at one path coordinate. -/
noncomputable def coordinateMeasure (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    Measure A.State :=
  (policy.pathMeasure hterminal initialState).map
    (fun path => path time)

/-- Every finite-prefix marginal is the corresponding Mathlib partial
trajectory. -/
theorem prefixMeasure_eq_partialTraj
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.prefixMeasure hterminal initialState time =
      Kernel.partialTraj
        (policy.pathStepKernel hterminal) 0 time
        (fun _ => initialState) := by
  rw [prefixMeasure, pathMeasure]
  exact
    @Kernel.traj_map_frestrictLe_apply
      (StateAt A) (fun _ => inferInstance)
      (policy.pathStepKernel hterminal)
      (fun _ => inferInstance)
      0 time (fun _ => initialState)

/-- A coordinate marginal is the latest-state pushforward of its prefix law.
-/
theorem coordinateMeasure_eq_map_prefix
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time =
      (policy.prefixMeasure hterminal initialState time).map
        (latestState time) := by
  rw [coordinateMeasure, prefixMeasure]
  rw [Measure.map_map
    (measurable_latestState time)
    (by fun_prop)]
  rfl

/-- The time-zero coordinate is the supplied initial state. -/
@[simp]
theorem coordinateMeasure_zero (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) :
    policy.coordinateMeasure hterminal initialState 0 =
      Measure.dirac initialState := by
  rw [coordinateMeasure_eq_map_prefix]
  rw [prefixMeasure_eq_partialTraj]
  rw [Kernel.partialTraj_self, Kernel.id_apply]
  rw [Measure.map_dirac' (measurable_latestState 0)]
  rfl

/-- Pushing the next partial trajectory to its newest coordinate is exactly
one history step after the preceding complete prefix. -/
theorem map_partialTraj_latest_succ
    (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestState time.succ) =
      policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time := by
  rw [← Kernel.partialTraj_comp_partialTraj
    (κ := policy.pathStepKernel hterminal)
    (a := 0) (b := time) (c := time.succ)
    (Nat.zero_le time) (Nat.le_succ time)]
  rw [Kernel.map_comp]
  have hlatest :
      (Kernel.partialTraj
        (policy.pathStepKernel hterminal)
        time time.succ).map (latestState time.succ) =
          policy.pathStepKernel hterminal time := by
    simpa only [Nat.succ_eq_add_one, latestState] using
      (@Kernel.map_partialTraj_succ_self
        (StateAt A) (fun _ => inferInstance)
        (policy.pathStepKernel hterminal)
        (fun _ => inferInstance)
        time)
  rw [hlatest]

/-- The next coordinate law integrates the time-indexed history step against
the complete preceding prefix law. It generally cannot be reduced to a
kernel acting only on the preceding one-coordinate marginal. -/
theorem coordinateMeasure_succ (policy : A.HistoryActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    (initialState : A.State) (time : ℕ) :
    policy.coordinateMeasure hterminal initialState time.succ =
      policy.pathStepKernel hterminal time ∘ₘ
        policy.prefixMeasure hterminal initialState time := by
  rw [coordinateMeasure_eq_map_prefix,
    prefixMeasure_eq_partialTraj]
  have hstep := congrArg
    (fun kernel =>
      kernel (fun _ : Finset.Iic 0 => initialState))
    (policy.map_partialTraj_latest_succ hterminal time)
  change
    (Kernel.partialTraj
      (policy.pathStepKernel hterminal) 0 time.succ).map
        (latestState time.succ)
        (fun _ : Finset.Iic 0 => initialState) =
      (policy.pathStepKernel hterminal time ∘ₖ
        Kernel.partialTraj
          (policy.pathStepKernel hterminal) 0 time)
        (fun _ : Finset.Iic 0 => initialState) at hstep
  rw [Kernel.map_apply _
    (measurable_latestState time.succ)] at hstep
  rw [Kernel.comp_apply] at hstep
  rw [hstep]
  rw [← prefixMeasure_eq_partialTraj]

end HistoryActionPolicy

namespace ActionPolicy

/-- Regard a stationary state-Markov action policy as a finite-history policy
by reading only the latest state. -/
def toHistoryActionPolicy (policy : A.ActionPolicy) :
    A.HistoryActionPolicy where
  kernel := fun time =>
    Kernel.comap policy.kernel
      (latestState time) (measurable_latestState time)
  terminal_zero := by
    intro time history hterminal
    change policy.kernel (latestState time history) = 0
    exact policy.terminal_zero _ hterminal
  nonterminal_isProbability := by
    intro time history hnonterminal
    change IsProbabilityMeasure
      (policy.kernel (latestState time history))
    exact policy.nonterminal_isProbability _ hnonterminal
  legal := by
    intro time history hnonterminal
    change
      ∀ᵐ stateAction
          ∂policy.kernel (latestState time history),
        stateAction ∈ A.actionFiber (latestState time history)
    exact policy.legal _ hnonterminal

/-- The embedded history policy's action kernel is the stationary kernel at
the latest state. -/
@[simp]
theorem toHistoryActionPolicy_kernel_apply
    (policy : A.ActionPolicy) (time : ℕ)
    (history : Π index : Finset.Iic time, StateAt A index) :
    policy.toHistoryActionPolicy.kernel time history =
      policy.kernel (latestState time history) :=
  rfl

/-- The embedded history policy has exactly the previously defined
state-Markov finite-history step kernel. -/
theorem toHistoryActionPolicy_pathStepKernel
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet) (time : ℕ) :
    policy.toHistoryActionPolicy.pathStepKernel hterminal time =
      policy.pathStepKernel hterminal time := by
  apply Kernel.ext
  intro history
  by_cases hstate :
      IsEmpty (A.Action (latestState time history))
  · rw [HistoryActionPolicy.pathStepKernel_apply_terminal
      _ hterminal time history hstate]
    change
      Measure.dirac (latestState time history) =
        policy.stepKernel hterminal (latestState time history)
    rw [policy.stepKernel_apply_terminal
      hterminal (latestState time history) hstate]
  · rw [HistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ hterminal time history hstate]
    change
      (policy.kernel (latestState time history)).bind A.transition =
        policy.stepKernel hterminal (latestState time history)
    rw [policy.stepKernel_apply_nonterminal
      hterminal (latestState time history) hstate]

/-- A stationary action policy has exactly the same infinite state-path law
when routed through the more general history-dependent policy interface. -/
theorem toHistoryActionPolicy_pathMeasure
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [PathExecution policy hterminal]
    (initialState : A.State) :
    policy.toHistoryActionPolicy.pathMeasure hterminal initialState =
      policy.pathMeasure hterminal initialState := by
  rw [HistoryActionPolicy.pathMeasure, ActionPolicy.pathMeasure, PathExecution.path_eq]
  congr 1

/-- The more general executor also preserves every stationary
one-coordinate marginal exactly. -/
theorem toHistoryActionPolicy_coordinateMeasure
    (policy : A.ActionPolicy)
    (hterminal : MeasurableSet A.terminalSet)
    [PathExecution policy hterminal]
    (initialState : A.State) (time : ℕ) :
    policy.toHistoryActionPolicy.coordinateMeasure
        hterminal initialState time =
      policy.coordinateMeasure hterminal initialState time := by
  rw [HistoryActionPolicy.coordinateMeasure,
    ActionPolicy.coordinateMeasure, PathExecution.coordinate_eq,
    policy.toHistoryActionPolicy_pathMeasure]
  rfl

end ActionPolicy

end MeasurableKernelArena
