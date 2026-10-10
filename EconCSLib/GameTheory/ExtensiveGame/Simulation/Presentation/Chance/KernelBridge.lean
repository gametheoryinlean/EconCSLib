/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint

/-!
# Presentation.Chance.KernelBridge — observed chance games as kernel arenas

This module connects the history-indexed behavioral semantics of
`ObservedChanceGame` to the analytic measurable-kernel executor.

The necessary state lift is explicit: states of `Arena.historyKernelArena` are
complete histories, actions are the legal actions at their endpoints, and a
transition deterministically appends the selected action. A stochastic history
policy is consequently a stationary `KernelArena.Policy` on the lifted state
space. The general discrete-to-analytic embedding then supplies the measurable
action policy and endpoint measures.

For an observed chance game, the lifted policy retains the original semantic
branching:

* player histories use the acting player's information-indexed behavioral law;
* chance histories use the declared chance kernel exactly.

The finite analytic endpoint law is proved equal to
the weighted-Dirac interpretation of `Arena.stochasticHistoryLawFrom`. This is
measure equality at every finite horizon.

The lift deliberately does **not** claim that the current
`EventInformation.ActionPolicy` represents a player's imperfect-information
partition. That interface has measures on concrete state/action bundles, so a
single information value cannot in general serve two distinct complete-history
state fibers. Player information consistency remains structural in the
abstract `ObservedGame.BehavioralProfile`; a later realization layer must
transport those abstract action laws to history-specific concrete fibers.

## Main definitions

* `Arena.historyKernelArena` — deterministic complete-history kernel arena.
* `Arena.StochasticHistoryPolicy.toKernelPolicy` — stationary policy on the
  history-state lift.
* `ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy` — the
  player/chance-aware lifted policy.

## Main results

* `Arena.historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom` — exact
  equality of finite stopped-history laws.
* `ObservedChanceGame.BehavioralProfile.toHistoryKernelPolicy_of_mover` and
  `toHistoryKernelPolicy_of_chance` — exact semantic branch equations.
* `ObservedChanceGame.BehavioralProfile.toMeasurable_endpointMeasure` — exact
  finite analytic stopped-history law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

namespace Arena

variable {A : Arena} {start : A.State}

/-- Turn complete histories from `start` into a discrete kernel arena.

The transition is deterministic but represented by a `FiniteLaw`, so the result can
reuse both the discrete stochastic trajectory API and its exact analytic
embedding. -/
def historyKernelArena (A : Arena) (start : A.State) :
    KernelArena where
  State := A.HistoryFrom start
  Action := fun history => A.Action history.1
  next := fun history action =>
    FiniteLaw.pure
      ⟨A.next history.1 action, history.2.snoc action⟩

/-- The history-kernel lift uses the source arena's executable terminal test. -/
local instance historyKernelActionEmptinessDecidable
    {A : Arena} {start : A.State}
    [(state : A.State) → Decidable (A.IsTerminal state)] :
    (history : (A.historyKernelArena start).State) →
      Decidable
        (IsEmpty ((A.historyKernelArena start).Action history)) :=
  fun history => inferInstanceAs (Decidable (A.IsTerminal history.1))

@[simp]
theorem historyKernelArena_next (A : Arena) (start : A.State)
    (history : A.HistoryFrom start) (action : A.Action history.1) :
    (A.historyKernelArena start).next history action =
      FiniteLaw.pure
        ⟨A.next history.1 action, history.2.snoc action⟩ :=
  rfl

@[simp]
theorem historyKernelArena_isTerminal_iff (A : Arena) (start : A.State)
    (history : A.HistoryFrom start) :
    IsEmpty ((A.historyKernelArena start).Action history) ↔
      A.IsTerminal history.1 :=
  Iff.rfl

namespace StochasticHistoryPolicy

/-- A history-dependent Arena policy is stationary after complete histories
are made the states of `Arena.historyKernelArena`. -/
def toKernelPolicy
    (policy : A.StochasticHistoryPolicy start) :
    (A.historyKernelArena start).Policy :=
  fun history hnonterminal => policy history hnonterminal

@[simp]
theorem toKernelPolicy_apply
    (policy : A.StochasticHistoryPolicy start)
    (history : A.HistoryFrom start)
    (hnonterminal : ¬ A.IsTerminal history.1) :
    policy.toKernelPolicy history hnonterminal =
      policy history hnonterminal :=
  rfl

end StochasticHistoryPolicy

/-- One lifted kernel-Arena step is the original action law pushed through
deterministic history append. -/
theorem historyKernelArena_stepLaw
    (policy : A.StochasticHistoryPolicy start)
    (history : A.HistoryFrom start)
    (hnonterminal : ¬ A.IsTerminal history.1) :
    (A.historyKernelArena start).stepLaw
        policy.toKernelPolicy history hnonterminal =
      (policy history hnonterminal).map fun action =>
        ⟨A.next history.1 action, history.2.snoc action⟩ := by
  exact (FiniteLaw.map_eq_bind_pure_comp _ _).symm

/-- The lifted finite state law is exactly the existing stopped stochastic
history executor.

This is equality of `FiniteLaw` values on complete histories at every finite horizon. -/
theorem historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (horizon : ℕ) (current : A.HistoryFrom start) :
    (A.historyKernelArena start).stateLawFrom
        policy.toKernelPolicy horizon current =
      A.stochasticHistoryLawFrom policy current horizon := by
  induction horizon generalizing current with
  | zero =>
      rfl
  | succ horizon ih =>
      by_cases hterminal : A.IsTerminal current.1
      · have hterminal' :
            IsEmpty
              ((A.historyKernelArena start).Action current) :=
          hterminal
        rw [KernelArena.stateLawFrom, dif_pos hterminal']
        exact
          (A.stochasticHistoryLawFrom_succ_of_terminal
            policy current horizon hterminal).symm
      · have hnonterminal' :
            ¬ IsEmpty
              ((A.historyKernelArena start).Action current) :=
          hterminal
        rw [KernelArena.stateLawFrom, dif_neg hnonterminal']
        rw [KernelArena.stepLaw, FiniteLaw.bind_bind]
        simp only [
          StochasticHistoryPolicy.toKernelPolicy,
          historyKernelArena_next, FiniteLaw.pure_bind]
        simp_rw [ih]
        exact
          (A.stochasticHistoryLawFrom_succ_of_not_terminal
            policy current horizon hterminal).symm

end Arena

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- The observed history lift reuses the game's executable terminal test. -/
local instance observedHistoryKernelActionEmptinessDecidable
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    (history : (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).State) →
      Decidable
        (IsEmpty ((G.observed.base.toArena.historyKernelArena
          G.observed.base.init).Action history)) :=
  fun history =>
    inferInstanceAs
      (Decidable (G.observed.base.isTerminal history.1))

namespace BehavioralProfile

/-- Lift an observed behavioral profile and its declared chance kernels to a
stationary policy on complete history states. -/
def toHistoryKernelPolicy
    (profile : G.observed.BehavioralProfile) :
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).Policy :=
  (toHistoryPolicy G profile).toKernelPolicy

@[simp]
theorem toHistoryKernelPolicy_apply
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1) :
    toHistoryKernelPolicy G profile history hnonterminal =
      toHistoryPolicy G profile history hnonterminal :=
  rfl

/-- At a player-controlled history, the lifted kernel policy is exactly the
acting player's concrete realization of the information-indexed law. -/
theorem toHistoryKernelPolicy_of_mover
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    toHistoryKernelPolicy G profile history hnonterminal =
      profile.actionLawAt G.observed history i hmover hnonterminal := by
  exact toHistoryPolicy_of_mover
    G profile history hnonterminal i hmover

/-- At a chance history, the lifted kernel policy is exactly the declared
chance action kernel. -/
theorem toHistoryKernelPolicy_of_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    toHistoryKernelPolicy G profile history hnonterminal =
      G.chanceKernel history ⟨hmover, hnonterminal⟩ := by
  exact toHistoryPolicy_of_chance
    G profile history hnonterminal hmover

/-- The one-step lifted state law at a player history is the player's concrete
action law pushed through deterministic history append. -/
theorem historyKernelArena_stepLaw_of_mover
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).stepLaw
        (toHistoryKernelPolicy G profile)
        history hnonterminal =
      (profile.actionLawAt G.observed history i hmover
        hnonterminal).map
        (fun action =>
          ⟨G.observed.base.next history.1 action,
            history.2.snoc action⟩) := by
  change
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).stepLaw
        (toHistoryPolicy G profile).toKernelPolicy
        history hnonterminal =
      _
  rw [Arena.historyKernelArena_stepLaw]
  rw [toHistoryPolicy_of_mover
    G profile history hnonterminal i hmover]

/-- The one-step lifted state law at a chance history is exactly the existing
chance-successor history law. -/
theorem historyKernelArena_stepLaw_of_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).stepLaw
        (toHistoryKernelPolicy G profile)
        history hnonterminal =
      G.chanceSuccessorLaw history
        ⟨hmover, hnonterminal⟩ := by
  change
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).stepLaw
        (toHistoryPolicy G profile).toKernelPolicy
        history hnonterminal =
      _
  rw [Arena.historyKernelArena_stepLaw]
  rw [toHistoryPolicy_of_chance
    G profile history hnonterminal hmover]
  rfl

/-- The finite lifted endpoint law is exactly the original behavioral/chance
stopped-history finite law. -/
theorem historyKernelArena_stateLawFrom_eq
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    (horizon : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    (G.observed.base.toArena.historyKernelArena
      G.observed.base.init).stateLawFrom
        (toHistoryKernelPolicy G profile) horizon current =
      G.observed.base.toArena.stochasticHistoryLawFrom
        (toHistoryPolicy G profile) current horizon :=
  Arena.historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom
    (toHistoryPolicy G profile) horizon current

/-- The analytic one-step law at a player history is exactly the measure
associated to the player's concrete successor-history finite law. -/
theorem toMeasurable_stepKernel_apply_of_mover
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    (toHistoryKernelPolicy G profile).toMeasurable.stepKernel
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        history =
      finiteLawMeasureTop(
        (profile.actionLawAt G.observed history i hmover
          hnonterminal).map
          (fun action =>
            ⟨G.observed.base.next history.1 action,
              history.2.snoc action⟩)) := by
  calc
    _ = finiteLawMeasureTop(
          (G.observed.base.toArena.historyKernelArena
            G.observed.base.init).stepLaw
              (toHistoryKernelPolicy G profile)
              history hnonterminal) :=
      KernelArena.Policy.toMeasurable_stepKernel_apply_nonterminal
        (A := G.observed.base.toArena.historyKernelArena
          G.observed.base.init)
        (toHistoryKernelPolicy G profile) history hnonterminal
    _ = _ := congrArg
      (fun law => finiteLawMeasureTop(law))
      (historyKernelArena_stepLaw_of_mover
        G profile history hnonterminal i hmover)

/-- The analytic one-step law at a chance history is exactly the measure
associated to the declared chance-successor kernel. -/
theorem toMeasurable_stepKernel_apply_of_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    (toHistoryKernelPolicy G profile).toMeasurable.stepKernel
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        history =
      finiteLawMeasureTop(
        G.chanceSuccessorLaw history ⟨hmover, hnonterminal⟩) := by
  calc
    _ = finiteLawMeasureTop(
          (G.observed.base.toArena.historyKernelArena
            G.observed.base.init).stepLaw
              (toHistoryKernelPolicy G profile)
              history hnonterminal) :=
      KernelArena.Policy.toMeasurable_stepKernel_apply_nonterminal
        (A := G.observed.base.toArena.historyKernelArena
          G.observed.base.init)
        (toHistoryKernelPolicy G profile) history hnonterminal
    _ = _ := congrArg
      (fun law => finiteLawMeasureTop(law))
      (historyKernelArena_stepLaw_of_chance
        G profile history hnonterminal hmover)

/-- Every finite analytic endpoint measure of the lifted observed behavior is
the weighted-Dirac measure of the stopped-history executor. -/
theorem toMeasurable_endpointMeasure
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    [MeasurableKernelArena.ActionPolicy.EndpointExecution
      (toHistoryKernelPolicy G profile).toMeasurable
      (G.observed.base.toArena.historyKernelArena
        G.observed.base.init).toMeasurable_measurableSet_terminalSet]
    (horizon : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    (toHistoryKernelPolicy G profile).toMeasurable.endpointMeasure
        (G.observed.base.toArena.historyKernelArena
          G.observed.base.init).toMeasurable_measurableSet_terminalSet
        horizon current =
      finiteLawMeasureTop(
        G.observed.base.toArena.stochasticHistoryLawFrom
          (toHistoryPolicy G profile) current horizon) := by
  calc
    _ = finiteLawMeasureTop(
          (G.observed.base.toArena.historyKernelArena
            G.observed.base.init).stateLawFrom
              (toHistoryKernelPolicy G profile)
              horizon current) :=
      KernelArena.Policy.toMeasurable_endpointMeasure
        (A := G.observed.base.toArena.historyKernelArena
          G.observed.base.init)
        (toHistoryKernelPolicy G profile) horizon current
    _ = _ := congrArg
      (fun law => finiteLawMeasureTop(law))
      (historyKernelArena_stateLawFrom_eq
        G profile horizon current)

end BehavioralProfile

end ExtensiveGame.ObservedChanceGame
