/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.ObservedChance
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.FiniteExecution

/-!
# Presentation.Chance.FiniteExecution — executable chance presentations

This analytic compatibility leaf relates the measure-free direct executor in
`Execution.Discrete.ObservedChance` to
`MeasurablePresentation.compiledPolicy`. The executable policy is assembled
directly from the original behavioral `FiniteLaw` at player histories and the
original chance `FiniteLaw` at chance histories. It never evaluates the
presentation's realized measure kernel.

The measurable presentation remains a semantic certificate.  Its player and
chance realization equations prove that the direct finite policy denotes the
same local action measure as `compiledPolicy`, for every represented event
prefix.  Terminal detection is supplied explicitly to the bounded executor;
it is not hidden behind classical decidability.

## Main results

* `compiledPolicy_kernel_eq_finiteEventPolicy` proves exact local equality
  with the original analytic compilation;
* `compiledPolicy_kernel_eq_finiteActionLaw?` includes the terminal branch;
* `measure_finitePrefixLawFrom_eq_partialTraj` lifts local correctness to
  every bounded action-recording prefix law;
* `measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe`
  identifies the corresponding complete finite state-prefix marginals.
-/

open MeasureTheory ProbabilityTheory

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) •
      Measure.dirac (Prod.fst atom) + rest) 0 atoms

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

namespace MeasurablePresentation

variable {N : Type uN} {U : Type uU}
variable {G : ObservedChanceGame N U}
variable {model : MeasurableHistoryModel G}

/-- Reindex an executable event prefix as the finite analytic prefix carrier
used by a measurable history presentation.  This changes only the finite
index representation (`Fin` versus `Finset.Iic`). -/
def toPresentationPrefix (model : MeasurableHistoryModel G) {time : ℕ}
    (history : (finiteHistoryArena G).EventPrefix time) :
    model.toArena.EventPrefix time :=
  fun index =>
    history ⟨index.1,
      Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp index.2)⟩

@[simp]
theorem latestEventState_toPresentationPrefix
    (model : MeasurableHistoryModel G) {time : ℕ}
    (history : (finiteHistoryArena G).EventPrefix time) :
    MeasurableKernelArena.latestEventState time
        (toPresentationPrefix model history) =
      history.latestState :=
  rfl

/-- At every nonterminal prefix, the original analytic compilation denotes
exactly the bundled finite action law selected by direct execution.

This theorem works for every measurable history model.  The measure uses that
model's action-bundle measurable space, while the algorithm itself remains
independent of the measurable presentation. -/
theorem compiledPolicy_kernel_eq_finiteEventPolicy
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ IsEmpty ((finiteHistoryArena G).Action history.latestState)) :
    (presentation.compiledPolicy profile).kernel time
        (toPresentationPrefix model history) =
      ((BehavioralProfile.toFiniteEventPolicy profile
          time history hnonterminal).map
          (fun action =>
            (⟨history.latestState, action⟩ :
              model.toArena.ActionBundle))).atoms.foldr
        (fun atom rest =>
          (atom.2 : ENNReal) •
            @Measure.dirac model.toArena.ActionBundle
              model.toArena.actionBundleMeasurable atom.1 + rest)
        0 := by
  cases hmover : G.observed.base.mover history.latestState.1 with
  | none =>
      rw [BehavioralProfile.toFiniteEventPolicy_of_chance
        profile time history hnonterminal hmover]
      exact presentation.compiledPolicy_kernel_of_chance
        profile time (toPresentationPrefix model history)
          hnonterminal hmover
  | some i =>
      rw [BehavioralProfile.toFiniteEventPolicy_of_mover
        profile time history hnonterminal i hmover]
      exact presentation.compiledPolicy_kernel_of_mover
        profile time (toPresentationPrefix model history)
          hnonterminal i hmover

/-- Total local correctness, including terminal prefixes: the analytic
compiled kernel is zero exactly when the executable query returns `none`, and
otherwise is the finite Dirac interpretation of the returned bundled action
law. -/
theorem compiledPolicy_kernel_eq_finiteActionLaw?
    (terminalDecision : TerminalDecision G)
    (presentation : MeasurablePresentation G model)
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (history : (finiteHistoryArena G).EventPrefix time) :
    (presentation.compiledPolicy profile).kernel time
        (toPresentationPrefix model history) =
      match BehavioralProfile.finiteActionLaw? terminalDecision
          profile time history with
      | none => 0
      | some law =>
          law.atoms.foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac model.toArena.ActionBundle
                  model.toArena.actionBundleMeasurable atom.1 + rest)
            0 := by
  letI := historyTerminalDecision terminalDecision
  by_cases hterminal :
      IsEmpty ((finiteHistoryArena G).Action history.latestState)
  · have hterminal' :
        IsEmpty
          (model.toArena.Action
            (MeasurableKernelArena.latestEventState time
              (toPresentationPrefix model history))) := by
        simpa only [latestEventState_toPresentationPrefix] using hterminal
    rw [(presentation.compiledPolicy profile).terminal_zero
      time (toPresentationPrefix model history) hterminal']
    simp [BehavioralProfile.finiteActionLaw?,
      KernelArena.EventHistoryPolicy.actionLaw?, hterminal]
  · rw [compiledPolicy_kernel_eq_finiteEventPolicy
      presentation profile time history hterminal]
    simp [BehavioralProfile.finiteActionLaw?,
      KernelArena.EventHistoryPolicy.actionLaw?, hterminal]
    rfl

/-- The direct history arena is the same discrete arena used by the existing
complete-history analytic compatibility model. -/
theorem finiteHistoryArena_toMeasurable_eq_discreteArena :
    (finiteHistoryArena G).toMeasurable =
      (MeasurableHistoryModel.discrete G).toArena :=
  rfl

/-- On the discrete measurable-history model, the direct finite policy is an
exact analytic realization of `compiledPolicy`, including zero action mass at
terminal prefixes. -/
theorem toFiniteEventPolicy_analyticallyRealizedBy
    (terminalDecision : TerminalDecision G)
    (presentation :
      MeasurablePresentation G (MeasurableHistoryModel.discrete G))
    (profile : G.observed.BehavioralProfile) :
    letI := historyTerminalDecision terminalDecision
    (BehavioralProfile.toFiniteEventPolicy profile).AnalyticallyRealizedBy
      (presentation.compiledPolicy profile) := by
  letI := historyTerminalDecision terminalDecision
  intro time history
  let finiteHistory :=
    KernelArena.EventPrefix.ofAnalytic
      (A := finiteHistoryArena G) history
  by_cases hterminal :
      IsEmpty ((finiteHistoryArena G).Action finiteHistory.latestState)
  · have hterminalFinite :
        IsEmpty
          ((finiteHistoryArena G).Action
            (MeasurableKernelArena.latestEventState time history)) := by
        simpa only [finiteHistory,
          KernelArena.EventPrefix.latestState_ofAnalytic] using hterminal
    have hterminal' :
        IsEmpty
          ((MeasurableHistoryModel.discrete G).toArena.Action
            (MeasurableKernelArena.latestEventState time history)) := by
        simpa only [finiteHistory,
          KernelArena.EventPrefix.latestState_ofAnalytic] using hterminal
    calc
      _ = 0 :=
        (presentation.compiledPolicy profile).terminal_zero
          time history hterminal'
      _ = _ := by
        simp [KernelArena.EventHistoryPolicy.actionLaw?, hterminalFinite]
        rfl
  · simp only [KernelArena.EventHistoryPolicy.actionLaw?,
      finiteHistory, hterminal, dite_false]
    simpa only [finiteHistory,
      KernelArena.EventPrefix.toAnalytic_ofAnalytic] using
      compiledPolicy_kernel_eq_finiteEventPolicy
        presentation profile time finiteHistory hterminal

/-- Every bounded run of the direct finite executor is exactly the analytic
partial trajectory generated by `compiledPolicy`. This is equality of the
whole action-recording event-prefix law, from any supplied absolute prefix and
for any finite number of additional steps. -/
theorem measure_finitePrefixLawFrom_eq_partialTraj
    (terminalDecision : TerminalDecision G)
    (presentation :
      MeasurablePresentation G (MeasurableHistoryModel.discrete G))
    (profile : G.observed.BehavioralProfile)
    (start : ℕ)
    (initialPrefix : (finiteHistoryArena G).EventPrefix start)
    (steps : ℕ) :
    μ[((BehavioralProfile.finitePrefixLawFrom terminalDecision profile
        start initialPrefix steps).map fun history =>
          KernelArena.EventPrefix.toAnalytic history).atoms] =
      Kernel.partialTraj
        ((presentation.compiledPolicy profile).pathStepKernel
          (finiteHistoryArena G).toMeasurable_measurableSet_terminalSet)
        start (start + steps)
        (KernelArena.EventPrefix.toAnalytic initialPrefix) := by
  letI := historyTerminalDecision terminalDecision
  have realizes :=
    toFiniteEventPolicy_analyticallyRealizedBy
      terminalDecision presentation profile
  simpa only [BehavioralProfile.finitePrefixLawFrom] using
    KernelArena.EventHistoryPolicy.measure_prefixLawFrom_eq_partialTraj
      (BehavioralProfile.toFiniteEventPolicy profile)
      (presentation.compiledPolicy profile)
      realizes start initialPrefix steps

/-- Starting from a complete history, direct finite event execution followed
by state projection is exactly the matching finite-prefix marginal of the
original analytic `MeasurablePresentation.statePathMeasure`.

The executor retains the complete event history, including selected actions,
until after it has generated the requested prefix.  The theorem identifies
every finite horizon separately and does not assert equality with an
executable infinite-path measure. -/
theorem measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe
    (terminalDecision : TerminalDecision G)
    (presentation :
      MeasurablePresentation G (MeasurableHistoryModel.discrete G))
    (profile : G.observed.BehavioralProfile)
    (initialHistory : CompleteHistory G)
    (horizon : ℕ) :
    letI : MeasurableSpace (finiteHistoryArena G).State :=
      (finiteHistoryArena G).toMeasurable.stateMeasurable
    μ[((BehavioralProfile.finitePrefixLawFrom terminalDecision profile
        0 (KernelArena.EventPrefix.initial initialHistory) horizon).map
          fun history (index : Finset.Iic horizon) =>
            history.states ⟨index.1, by
              have hindex := Finset.mem_Iic.mp index.2
              omega⟩).atoms] =
      (presentation.statePathMeasure profile initialHistory).map
        (Preorder.frestrictLe horizon) := by
  letI : MeasurableSpace (finiteHistoryArena G).State :=
    (finiteHistoryArena G).toMeasurable.stateMeasurable
  let initialPrefix : (finiteHistoryArena G).EventPrefix 0 :=
    KernelArena.EventPrefix.initial initialHistory
  let finitePrefixStates :
      (finiteHistoryArena G).EventPrefix (0 + horizon) →
        (Π _index : Finset.Iic horizon,
          (MeasurableHistoryModel.discrete G).toArena.State) :=
    fun history index =>
      history.states ⟨index.1, by
        have hindex := Finset.mem_Iic.mp index.2
        omega⟩
  let prefixStates :
      (Π _index : Finset.Iic (0 + horizon),
          (MeasurableHistoryModel.discrete G).toArena.PathEvent) →
        (Π _index : Finset.Iic horizon,
          (MeasurableHistoryModel.discrete G).toArena.State) :=
    fun history index =>
      (history ⟨index.1, Finset.mem_Iic.mpr (by
        have hindex := Finset.mem_Iic.mp index.2
        omega)⟩).state
  have hprefixStates_measurable : Measurable prefixStates := by
    exact measurable_pi_lambda _ fun index =>
      MeasurableKernelArena.PathEvent.measurable_state.comp
        (measurable_pi_apply
          (⟨index.1, Finset.mem_Iic.mpr (by
            have hindex := Finset.mem_Iic.mp index.2
            omega)⟩ : Finset.Iic (0 + horizon)))
  have hlaw :
      (BehavioralProfile.finitePrefixLawFrom terminalDecision profile
          0 initialPrefix horizon).map
            finitePrefixStates =
        ((BehavioralProfile.finitePrefixLawFrom terminalDecision profile
          0 initialPrefix horizon).map
            (fun history => history.toAnalytic)).map prefixStates := by
    simp only [FiniteLaw.map_comp]
    congr 1
  change
    μ[((BehavioralProfile.finitePrefixLawFrom terminalDecision profile
        0 initialPrefix horizon).map
          finitePrefixStates).atoms] = _
  rw [hlaw]
  rw [← FiniteLaw.measure_map _ _ hprefixStates_measurable]
  have hevent := measure_finitePrefixLawFrom_eq_partialTraj
    terminalDecision presentation profile 0 initialPrefix horizon
  refine (congrArg (Measure.map prefixStates) hevent).trans ?_
  unfold
    MeasurablePresentation.statePathMeasure
    MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe horizon)
    MeasurableKernelArena.measurable_eventPathStates]
  unfold MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure
  rw [← Kernel.traj_map_frestrictLe_apply
    (κ := (presentation.compiledPolicy profile).pathStepKernel
      (finiteHistoryArena G).toMeasurable_measurableSet_terminalSet)
    0 (0 + horizon) initialPrefix.toAnalytic]
  rw [Measure.map_map hprefixStates_measurable
    (Preorder.measurable_frestrictLe (0 + horizon))]
  congr 1

end MeasurablePresentation

end ExtensiveGame.ObservedChanceGame
