/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.RealizedInformationBoundary
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized

/-!
# Positive observed-chance realized-presentation regression

This example packages the absent-minded realized-information policy as a
genuine `ObservedChanceGame.AnalyticPresentation`.

The certificate is non-vacuous:

* its fixed Bool information statistic merges the two recurring player
  decisions and separates the terminal history;
* its fixed `Unit` realization reads the concrete latest complete history;
* every behavioral profile compiles to the same realized policy (all
  information-action types in this game are subsingletons);
* the compiled raw event policy is exactly the established
  observed-chance complete-history policy at every prefix, not just at the two
  displayed decisions;
* the generic presentation theorems therefore give one shared abstract law
  and exact finite stopped-history semantics.

This is a positive existence regression for the presentation interface. It
does not claim that an arbitrary `ObservedChanceGame` has such a presentation
without explicit measurability data.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ObservedChanceRealizedPresentationBoundary

open Examples.AbsentMinded
open Examples.ObservedChanceKernelBridgeBoundary
open Examples.RealizedInformationBoundary
open ExtensiveGame
open MeasurableKernelArena

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

private theorem finiteLawMeasureTop_map_const
    {α β : Type*} (law : FiniteLaw α) (value : β) :
    finiteLawMeasureTop(law.map (Function.const α value)) =
      @Measure.dirac β ⊤ value := by
  rw [FiniteLaw.map_atoms]
  have hfold :
      ∀ atoms : List (α × ℚ≥0),
        (atoms.map fun atom => (value, atom.2)).foldr
            (fun atom rest =>
              (atom.2 : ENNReal) •
                @Measure.dirac β ⊤ atom.1 + rest)
            0 =
          (((FiniteLaw.totalWeight atoms : ℚ≥0) : NNReal) : ENNReal) •
            @Measure.dirac β ⊤ value := by
    intro atoms
    induction atoms with
    | nil => simp [FiniteLaw.totalWeight]
    | cons atom atoms ih =>
        rcases atom with ⟨outcome, weight⟩
        simp only [List.map_cons, List.foldr_cons]
        rw [ih, ← add_smul]
        congr 1
        unfold FiniteLaw.totalWeight
        simp only [List.map_cons, List.sum_cons]
        change
          (((weight : ℚ≥0) : NNReal) : ENNReal) +
              ((((atoms.map Prod.snd).sum : ℚ≥0) : NNReal) : ENNReal) =
            (((weight + (atoms.map Prod.snd).sum : ℚ≥0) : NNReal) : ENNReal)
        simp
  simp only [Function.const_apply]
  rw [hfold, FiniteLaw.totalWeight_atoms]
  change
    (((1 : ℚ≥0) : NNReal) : ENNReal) •
        @Measure.dirac β ⊤ value =
      @Measure.dirac β ⊤ value
  simp

/-- The absent-minded observed chance game admits a realized analytic
presentation whose information statistic genuinely merges the two recurring
player histories. -/
noncomputable def presentation :
    game.AnalyticPresentation where
  information := terminalTaggedInformation
  realization := unitRealization
  toPolicy := fun _profile => unitPolicy
  compiled := by
    intro arbitraryProfile
    apply EventHistoryActionPolicy.ext
    funext time
    apply Kernel.ext
    intro events
    let current :=
      MeasurableKernelArena.latestEventState time events
    have hcurrent :
        MeasurableKernelArena.latestEventState time events = current :=
      rfl
    change
      unitPolicy.toEventHistoryActionPolicy.kernel time events =
        (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
          game arbitraryProfile).toMeasurable.kernel current
    by_cases hterminal : IsEmpty (liftedArena.Action current)
    · rw [unitPolicy_compiled_terminal time events hterminal]
      exact
        (KernelArena.Policy.toMeasurableKernel_apply_terminal
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
            game arbitraryProfile)
          current hterminal).symm
    · rw [unitPolicy_compiled_nonterminal time events hterminal]
      rw [
        KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
            game arbitraryProfile)
          current hterminal]
      rcases current with ⟨state, path⟩
      cases state with
      | s0 =>
          have hrealize :
              realizeBundle
                  (MeasurableKernelArena.latestEventState time events) =
                realizeBundle
                  (⟨Rung.s0, path⟩ : liftedArena.State) :=
            congrArg realizeBundle hcurrent
          rw [hrealize]
          have hfun :
              (fun action :
                  (game.observed.base.toArena.historyKernelArena
                    game.observed.base.init).Action
                      (⟨Rung.s0, path⟩ : liftedArena.State) =>
                    (⟨(⟨Rung.s0, path⟩ : liftedArena.State),
                      action⟩ : liftedArena.ActionBundle)) =
                Function.const _
                  (⟨(⟨Rung.s0, path⟩ : liftedArena.State),
                    ()⟩ : liftedArena.ActionBundle) := by
            funext action
            cases action
            rfl
          have hmap :=
            congrArg
              (fun actionMap =>
                (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                  game arbitraryProfile
                  (⟨Rung.s0, path⟩ : liftedArena.State)
                  hterminal).map actionMap)
              hfun
          calc
            Measure.dirac
                (realizeBundle
                  (⟨Rung.s0, path⟩ : liftedArena.State)) =
              finiteLawMeasureTop(
                (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                  game arbitraryProfile
                  (⟨Rung.s0, path⟩ : liftedArena.State)
                  hterminal).map
                    (Function.const _
                      (⟨(⟨Rung.s0, path⟩ : liftedArena.State),
                        ()⟩ : liftedArena.ActionBundle))) := by
              change
                Measure.dirac
                    (⟨(⟨Rung.s0, path⟩ : liftedArena.State),
                      ()⟩ : liftedArena.ActionBundle) = _
              exact
                (finiteLawMeasureTop_map_const
                  (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                    game arbitraryProfile
                    (⟨Rung.s0, path⟩ : liftedArena.State)
                    hterminal)
                  (⟨(⟨Rung.s0, path⟩ : liftedArena.State),
                    ()⟩ : liftedArena.ActionBundle)).symm
            _ = _ :=
              congrArg
                (fun law : FiniteLaw liftedArena.ActionBundle =>
                  finiteLawMeasureTop(law))
                hmap.symm
      | s1 =>
          have hrealize :
              realizeBundle
                  (MeasurableKernelArena.latestEventState time events) =
                realizeBundle
                  (⟨Rung.s1, path⟩ : liftedArena.State) :=
            congrArg realizeBundle hcurrent
          rw [hrealize]
          have hfun :
              (fun action :
                  (game.observed.base.toArena.historyKernelArena
                    game.observed.base.init).Action
                      (⟨Rung.s1, path⟩ : liftedArena.State) =>
                    (⟨(⟨Rung.s1, path⟩ : liftedArena.State),
                      action⟩ : liftedArena.ActionBundle)) =
                Function.const _
                  (⟨(⟨Rung.s1, path⟩ : liftedArena.State),
                    ()⟩ : liftedArena.ActionBundle) := by
            funext action
            cases action
            rfl
          have hmap :=
            congrArg
              (fun actionMap =>
                (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                  game arbitraryProfile
                  (⟨Rung.s1, path⟩ : liftedArena.State)
                  hterminal).map actionMap)
              hfun
          calc
            Measure.dirac
                (realizeBundle
                  (⟨Rung.s1, path⟩ : liftedArena.State)) =
              finiteLawMeasureTop(
                (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                  game arbitraryProfile
                  (⟨Rung.s1, path⟩ : liftedArena.State)
                  hterminal).map
                    (Function.const _
                      (⟨(⟨Rung.s1, path⟩ : liftedArena.State),
                        ()⟩ : liftedArena.ActionBundle))) := by
              change
                Measure.dirac
                    (⟨(⟨Rung.s1, path⟩ : liftedArena.State),
                      ()⟩ : liftedArena.ActionBundle) = _
              exact
                (finiteLawMeasureTop_map_const
                  (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy
                    game arbitraryProfile
                    (⟨Rung.s1, path⟩ : liftedArena.State)
                    hterminal)
                  (⟨(⟨Rung.s1, path⟩ : liftedArena.State),
                    ()⟩ : liftedArena.ActionBundle)).symm
            _ = _ :=
              congrArg
                (fun law : FiniteLaw liftedArena.ActionBundle =>
                  finiteLawMeasureTop(law))
                hmap.symm
      | s2 =>
          exact
            (hterminal
              (show IsEmpty
                  (liftedArena.Action
                    (⟨Rung.s2, path⟩ : liftedArena.State)) from
                ⟨PEmpty.elim⟩)).elim
  playerInformation := fun _time _playerInformation => false
  player_informationAt := by
    intro time events i hmover hnonterminal
    change
      terminalTag
          (MeasurableKernelArena.latestEventState time events).1 =
        false
    generalize hcurrent :
      MeasurableKernelArena.latestEventState time events = current at hmover ⊢
    rcases current with ⟨state, path⟩
    cases state with
    | s0 =>
        rfl
    | s1 =>
        rfl
    | s2 =>
        simp [
          game,
          ExtensiveGame.ObservedChanceGame.ofNoChance,
          absentMindedGame,
          base,
          rungMover] at hmover

/-- The two recurring player decisions use exactly one abstract law through
the generic observed-chance presentation theorem. -/
theorem recurring_player_abstract_law_eq :
    (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 firstPrefix) =
      (presentation.toPolicy profile).abstractKernel 0
        (presentation.information.informationAt 0 secondPrefix) := by
  exact
    presentation.abstractKernel_eq_of_player_infoAt_eq
      profile 0 firstPrefix secondPrefix 0
      rfl firstPrefix_nonterminal
      rfl secondPrefix_nonterminal
      infoState_recurs

/-- The realized presentation recovers the exact two-step stopped-history
finite-law measure through the generic finite-state theorem. -/
theorem realized_two_step_state_law_exact :
    Measure.map
        (fun path : ℕ → game.AnalyticHistoryArena.State => path 2)
        (EventHistoryActionPolicy.statePathMeasure
          (presentation.toPolicy profile).toEventHistoryActionPolicy
            (game.observed.base.toArena.historyKernelArena
              game.observed.base.init).toMeasurable_measurableSet_terminalSet
            firstDecision) =
      finiteLawMeasureTop(
        game.observed.base.toArena.stochasticHistoryLawFrom
          (ExtensiveGame.ObservedChanceGame.BehavioralProfile.toHistoryPolicy
            game profile)
          firstDecision 2) :=
  presentation.compiled_finite_state_law
    profile 2 firstDecision

end Examples.ObservedChanceRealizedPresentationBoundary
