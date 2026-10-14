/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.FiniteLawIntegral
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath

/-!
# Strict history-dependent measurable-policy boundary

A finite discrete measurable-kernel arena whose history action policy first
merges every initial state at `false`, then chooses the first state recorded
in the finite prefix. Two reachable prefixes can therefore end at the same
current state but receive different deterministic actions.

The main reverse theorem proves that no stationary `ActionPolicy`, embedded
through `toHistoryActionPolicy`, agrees with this policy on every prefix. This
is an interface-expressiveness regression; it does not yet claim a
state/action joint path law or observed information semantics.

`transitionLaw`, `actionLaw`, and `stepLaw` compute the original transition,
action selection, and history step as finite rational laws. Exact kernel
equalities and `stepLaw_eventMass` connect every Boolean event query to the
original analytic semantics, preserving the complete incoming state prefix.
-/

open MeasureTheory ProbabilityTheory

namespace EconCSLib.Examples.ExtensiveGame.HistoryDependentKernelBoundary

/-- A two-state analytic arena with a Boolean action at every state. The next
state is the selected action. -/
noncomputable def historyArena : MeasurableKernelArena where
  State := Bool
  Action := fun _ => Bool
  stateMeasurable := ⊤
  actionBundleMeasurable := ⊤
  stateProjection_measurable := by
    change
      @Measurable (Σ _state : Bool, Bool) Bool
        ⊤ ⊤ Sigma.fst
    exact fun _ _ => MeasurableSpace.measurableSet_top
  transition :=
    @Kernel.deterministic
      (Σ _state : Bool, Bool) Bool ⊤ ⊤
      (fun stateAction => stateAction.2)
      (fun _ _ => MeasurableSpace.measurableSet_top)
  transition_isMarkov := by
    infer_instance

instance historyArena_stateFintype :
    Fintype historyArena.State := by
  change Fintype Bool
  infer_instance

instance historyArena_stateMeasurableSingleton :
    MeasurableSingletonClass historyArena.State where
  measurableSet_singleton _ :=
    MeasurableSpace.measurableSet_top

/-- Read coordinate zero from a nonempty finite prefix. -/
def firstState (time : ℕ)
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.StateAt historyArena index) :
    Bool :=
  history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le time)⟩

/-- A history-dependent action policy that chooses the prefix's first state
after time zero. At time zero it chooses `false`, so all initial states merge
at `false` before the policy remembers which initial state led there. -/
def chosenAction (time : ℕ)
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.StateAt historyArena index) :
    Bool :=
  if time = 0 then false else firstState time history

/-- A history-dependent action policy that chooses `chosenAction`. -/
noncomputable def historyPolicy : historyArena.HistoryActionPolicy where
  kernel := fun time =>
    Kernel.deterministic
      (fun history =>
        (⟨MeasurableKernelArena.latestState time history,
          chosenAction time history⟩ :
          historyArena.ActionBundle))
      (measurable_of_finite _)
  terminal_zero := by
    intro time history hterminal
    exact (hterminal.false false).elim
  nonterminal_isProbability := by
    intro time history hnonterminal
    infer_instance
  legal := by
    intro time history hnonterminal
    rw [Kernel.deterministic_apply]
    apply
      (ae_dirac_iff
        (show
          MeasurableSet
            (historyArena.actionFiber
              (MeasurableKernelArena.latestState time history)) from
          historyArena.measurableSet_actionFiber _)).2
    simp

/-- The history policy's selected action measure is a Dirac mass at the
latest state bundled with the prefix's first state. -/
@[simp]
theorem historyPolicy_kernel_apply
    (time : ℕ)
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.StateAt historyArena index) :
    historyPolicy.kernel time history =
      Measure.dirac
        (⟨MeasurableKernelArena.latestState time history,
          chosenAction time history⟩ :
          historyArena.ActionBundle) := by
  exact Kernel.deterministic_apply
    (measurable_of_finite _) history

/-- A length-one prefix that starts and ends at `false`. -/
def falseFalsePrefix :
    Π _index : Finset.Iic 1, historyArena.State :=
  fun _ => false

/-- A length-one prefix that starts at `true` and ends at `false`. -/
def trueFalsePrefix :
    Π _index : Finset.Iic 1, historyArena.State :=
  fun index => if index.1 = 0 then true else false

@[simp]
theorem latestState_falseFalsePrefix :
    MeasurableKernelArena.latestState 1 falseFalsePrefix = false :=
  rfl

@[simp]
theorem latestState_trueFalsePrefix :
    MeasurableKernelArena.latestState 1 trueFalsePrefix = false := by
  simp [MeasurableKernelArena.latestState, trueFalsePrefix]

@[simp]
theorem firstState_falseFalsePrefix :
    firstState 1 falseFalsePrefix = false :=
  rfl

@[simp]
theorem firstState_trueFalsePrefix :
    firstState 1 trueFalsePrefix = true := by
  simp [firstState, trueFalsePrefix]

@[simp]
theorem chosenAction_falseFalsePrefix :
    chosenAction 1 falseFalsePrefix = false := by
  simp [chosenAction]

@[simp]
theorem chosenAction_trueFalsePrefix :
    chosenAction 1 trueFalsePrefix = true := by
  simp [chosenAction]

/-- Terminal states are absent and hence form a measurable set. -/
theorem historyArena_measurableSet_terminalSet :
    MeasurableSet historyArena.terminalSet := by
  change
    @MeasurableSet historyArena.State ⊤
      historyArena.terminalSet
  exact MeasurableSpace.measurableSet_top

/-- In this deterministic arena, the history step reaches the Boolean action
selected from the complete prefix. -/
@[simp]
theorem historyPolicy_pathStepKernel_apply
    (time : ℕ)
    (history : Π index : Finset.Iic time,
      MeasurableKernelArena.StateAt historyArena index) :
    historyPolicy.pathStepKernel
        historyArena_measurableSet_terminalSet time history =
      Measure.dirac (chosenAction time history) := by
  have hnonterminal :
      ¬ IsEmpty
        (historyArena.Action
          (MeasurableKernelArena.latestState time history)) := by
    intro hempty
    exact hempty.false false
  rw [MeasurableKernelArena.HistoryActionPolicy.pathStepKernel_apply_nonterminal
      _ historyArena_measurableSet_terminalSet
      time history hnonterminal]
  rw [historyPolicy_kernel_apply]
  rw [Measure.dirac_bind historyArena.transition.measurable]
  change
    (@Kernel.deterministic
      (Σ _state : Bool, Bool) Bool ⊤ ⊤
      (fun stateAction => stateAction.2)
      (fun _ _ => MeasurableSpace.measurableSet_top))
      ⟨MeasurableKernelArena.latestState time history,
        chosenAction time history⟩ =
      Measure.dirac (chosenAction time history)
  rfl

/-- The unique time-zero prefix at `initialState`. -/
def initialPrefix (initialState : historyArena.State) :
    Π _index : Finset.Iic 0, historyArena.State :=
  fun _ => initialState

/-- Every initial state moves to `false` at the first event, so both witness
prefixes below are operationally reachable from their respective initial
states. -/
@[simp]
theorem historyPolicy_pathStepKernel_zero
    (initialState : historyArena.State) :
    historyPolicy.pathStepKernel
        historyArena_measurableSet_terminalSet
        0 (initialPrefix initialState) =
      Measure.dirac false := by
  rw [historyPolicy_pathStepKernel_apply]
  simp [chosenAction]

@[simp]
theorem historyPolicy_pathStepKernel_falseFalsePrefix :
    historyPolicy.pathStepKernel
        historyArena_measurableSet_terminalSet
        1 falseFalsePrefix =
      Measure.dirac false := by
  rw [historyPolicy_pathStepKernel_apply]
  exact congrArg Measure.dirac chosenAction_falseFalsePrefix

@[simp]
theorem historyPolicy_pathStepKernel_trueFalsePrefix :
    historyPolicy.pathStepKernel
        historyArena_measurableSet_terminalSet
        1 trueFalsePrefix =
      Measure.dirac true := by
  rw [historyPolicy_pathStepKernel_apply]
  exact congrArg Measure.dirac chosenAction_trueFalsePrefix

/-- No stationary state-Markov policy agrees with `historyPolicy` on all
finite prefixes. The two witness prefixes have the same latest state but force
different deterministic action laws. -/
theorem no_stationary_policy_representation :
    ¬ ∃ stationary : historyArena.ActionPolicy,
      ∀ time history,
        stationary.toHistoryActionPolicy.kernel time history =
          historyPolicy.kernel time history := by
  rintro ⟨stationary, hstationary⟩
  have hfalse := hstationary 1 falseFalsePrefix
  have htrue := hstationary 1 trueFalsePrefix
  rw [MeasurableKernelArena.ActionPolicy.toHistoryActionPolicy_kernel_apply,
    historyPolicy_kernel_apply] at hfalse htrue
  rw [latestState_falseFalsePrefix,
    chosenAction_falseFalsePrefix] at hfalse
  rw [latestState_trueFalsePrefix,
    chosenAction_trueFalsePrefix] at htrue
  have hdirac :
      Measure.dirac
          (⟨false, false⟩ : historyArena.ActionBundle) =
        Measure.dirac
          (⟨false, true⟩ : historyArena.ActionBundle) :=
    hfalse.symm.trans htrue
  have hsingleton :
      MeasurableSet
        ({(⟨false, false⟩ : historyArena.ActionBundle)} :
          Set historyArena.ActionBundle) := by
    change
      @MeasurableSet historyArena.ActionBundle ⊤
        {(⟨false, false⟩ : historyArena.ActionBundle)}
    exact MeasurableSpace.measurableSet_top
  have happly := congrArg
    (fun measure : Measure historyArena.ActionBundle =>
      measure {(⟨false, false⟩ : historyArena.ActionBundle)})
    hdirac
  change
    Measure.dirac
        (⟨false, false⟩ : historyArena.ActionBundle)
        {(⟨false, false⟩ : historyArena.ActionBundle)} =
      Measure.dirac
        (⟨false, true⟩ : historyArena.ActionBundle)
        {(⟨false, false⟩ : historyArena.ActionBundle)}
    at happly
  rw [Measure.dirac_apply' _ hsingleton,
    Measure.dirac_apply' _ hsingleton] at happly
  simp at happly

section FiniteExecution

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace historyArena.ActionBundle := ⊤
local instance : DecidableEq historyArena.State := by
  change DecidableEq Bool
  infer_instance
local instance : BEq historyArena.State := by
  change BEq Bool
  infer_instance

/-- Executable successor law of the original deterministic transition. -/
def transitionLaw (bundle : historyArena.ActionBundle) : FiniteLaw historyArena.State :=
  FiniteLaw.pure bundle.2

/-- Exact action law retaining the complete finite state prefix. -/
def actionLaw (time : ℕ)
    (history : Π _index : Finset.Iic time, historyArena.State) :
    FiniteLaw historyArena.ActionBundle :=
  FiniteLaw.pure ⟨history ⟨time, Finset.mem_Iic.mpr le_rfl⟩, chosenAction time history⟩

/-- Execute the existing history-dependent policy and its transition using
finite rational laws. -/
def stepLaw (time : ℕ)
    (history : Π _index : Finset.Iic time, historyArena.State) :
    FiniteLaw historyArena.State :=
  (actionLaw time history).bind transitionLaw

/-- The finite successor law denotes exactly the original transition kernel. -/
theorem transitionLaw_eq_kernel (bundle : historyArena.ActionBundle) :
    μ[(transitionLaw bundle).atoms] = historyArena.transition bundle := by
  simp only [transitionLaw, FiniteLaw.pure_atoms, List.foldr_cons, List.foldr_nil]
  rw [show ((1 : ℚ≥0) : ENNReal) = 1 by
    change (((1 : ℚ≥0) : NNReal) : ENNReal) = 1
    norm_num, one_smul, add_zero]
  rfl

/-- The finite action law denotes exactly the original history policy. -/
theorem actionLaw_eq_kernel (time : ℕ)
    (history : Π _index : Finset.Iic time, historyArena.State) :
    μ[(actionLaw time history).atoms] = historyPolicy.kernel time history := by
  simp [actionLaw, FiniteLaw.pure_atoms, historyPolicy_kernel_apply, ← ENNReal.coe_nnratCast]
  rfl

/-- The executable one-step result equals the original analytic history step. -/
theorem stepLaw_eq_kernel (time : ℕ)
    (history : Π _index : Finset.Iic time, historyArena.State) :
    μ[(stepLaw time history).atoms] =
      historyPolicy.pathStepKernel historyArena_measurableSet_terminalSet time history := by
  rw [historyPolicy_pathStepKernel_apply]
  simp [stepLaw, actionLaw, transitionLaw, FiniteLaw.pure_bind,
    FiniteLaw.pure_atoms, ← ENNReal.coe_nnratCast]
  rfl

/-- Any executable Boolean successor query computes the original kernel's
probability of that event. -/
theorem stepLaw_eventMass (time : ℕ)
    (history : Π _index : Finset.Iic time, historyArena.State)
    (test : historyArena.State → Bool) :
    historyPolicy.pathStepKernel historyArena_measurableSet_terminalSet time history
      {x | test x} = ((stepLaw time history).eventMass test : ENNReal) := by
  rw [← stepLaw_eq_kernel]
  exact _root_.Examples.ExtensiveGame.FiniteLawIntegral.measure_eventMass _ _
    (MeasurableSpace.measurableSet_top)

/-- A shared current state still gives distinct computed successor laws;
the initial transition merges both initial states at false. -/
theorem stepLaw_regression :
    (stepLaw 0 (initialPrefix true)).atoms = [(false, 1)] ∧
    (stepLaw 1 falseFalsePrefix).atoms = [(false, 1)] ∧
    (stepLaw 1 trueFalsePrefix).atoms = [(true, 1)] := by
  simp [stepLaw, actionLaw, transitionLaw, FiniteLaw.pure_bind,
    FiniteLaw.pure_atoms, chosenAction, firstState, initialPrefix, trueFalsePrefix,
    falseFalsePrefix]
  exact ⟨rfl, rfl⟩

#eval show IO Unit from do
  unless (stepLaw 1 falseFalsePrefix).atoms == [(false, 1)] &&
      (stepLaw 1 trueFalsePrefix).atoms == [(true, 1)] do
    throw (IO.userError "history-dependent finite execution regression")

end FiniteExecution

end EconCSLib.Examples.ExtensiveGame.HistoryDependentKernelBoundary
