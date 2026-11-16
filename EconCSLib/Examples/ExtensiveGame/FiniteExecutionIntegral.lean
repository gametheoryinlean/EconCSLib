/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Examples.ExtensiveGame.FiniteLawIntegral
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.DiscreteBridge
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome

/-!
# Finite history execution and analytic stopped utility

This opt-in prototype connects executable rational finite history laws to the
actual Ionescu--Tulcea law of their existing complete-history kernel lift.
The path law appears only as an expression in theorems. No path measure or
target marginal equality is supplied by a caller.

`historyLaw_eq_coordinate` combines the existing horizon inductions for the
history lift and the finite weighted Dirac kernel embedding. `integral_historyPayoff`
then applies the finite-law integral theorem. `stoppedExpectedPayoff` executes
the original finite executor and exact rational expectation; nonterminal
coordinates contribute zero. `integral_stoppedUtility` specializes the result
to the existing terminal-payoff extension on a discrete observed-history model.

The complete-history sigma algebra is discrete; the path sigma algebra is its
countable product. No global finite or countable state/action enumeration,
termination bound, or global payoff bound is required for a finite horizon.
This is a semantic theorem about a general analytic path construction, not an
algorithm that constructs or numerically samples an entire infinite path.
-/

open MeasureTheory ProbabilityTheory

namespace Examples.ExtensiveGame.FiniteExecutionIntegral

local macro "historyPath(" arena:term ", " start:term ", " policy:term ", " current:term ")" :
    term =>
  `(Kernel.traj
    ((Arena.StochasticHistoryPolicy.toKernelPolicy $policy).toMeasurable.pathStepKernel
      (Arena.historyKernelArena $arena $start).toMeasurable_measurableSet_terminalSet)
    0 (fun _ => $current))

local notation "μ[" atoms "]" =>
  List.foldr (fun (atom : _ × ℚ≥0) rest =>
    ((Prod.snd atom : ℚ≥0) : ENNReal) • Measure.dirac (Prod.fst atom) + rest) 0 atoms

section HistoryExecution

variable {A : Arena} {start : A.State}
variable [(state : A.State) → Decidable (A.IsTerminal state)]

local instance : MeasurableSpace (A.HistoryFrom start) := ⊤

local instance : (history : (A.historyKernelArena start).State) →
    Decidable (IsEmpty ((A.historyKernelArena start).Action history)) :=
  fun history => inferInstanceAs (Decidable (A.IsTerminal history.1))

/-- Every coordinate of the actual analytic history path law is the finite
executor's weighted Dirac measure. The reused horizon inductions start at a
Dirac history, absorb terminal histories, and append the actual chosen action. -/
theorem historyLaw_eq_coordinate (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) :
    (historyPath(A, start, policy, current)).map (fun path => path horizon) =
      μ[(A.stochasticHistoryLawFrom policy current horizon).atoms] := by
  obtain ⟨execution⟩ := MeasurableKernelArena.ActionPolicy.PathExecution.nonempty
    policy.toKernelPolicy.toMeasurable
    (A.historyKernelArena start).toMeasurable_measurableSet_terminalSet
  letI := execution
  have h := policy.toKernelPolicy.toMeasurable_coordinateMeasure current horizon
  change MeasurableKernelArena.ActionPolicy.PathExecution.coordinate _ _ _ _ = _ at h
  rw [MeasurableKernelArena.ActionPolicy.PathExecution.coordinate_eq,
    MeasurableKernelArena.ActionPolicy.PathExecution.path_eq] at h
  refine h.trans ?_
  exact congrArg (fun law : FiniteLaw (A.HistoryFrom start) => μ[law.atoms])
    (Arena.historyKernelArena_stateLawFrom_eq_stochasticHistoryLawFrom policy horizon current)

/-- A finite-horizon observable is integrable even if its off-support values
are unbounded. The proof derives this from finite support of the coordinate. -/
theorem integrable_historyPayoff (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (payoff : A.HistoryFrom start → ℝ) :
    Integrable (fun path => payoff (path horizon)) historyPath(A, start, policy, current) := by
  have h : Integrable payoff
      ((historyPath(A, start, policy, current)).map (fun path => path horizon)) := by
    exact (historyLaw_eq_coordinate policy current horizon).symm ▸
      FiniteLawIntegral.integrable _ _
  exact h.comp_measurable (measurable_pi_apply horizon)

/-- Exact rational expected payoff equals the integral of that same complete
history observable under the actual analytic path law. -/
theorem integral_historyPayoff (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ) :
    (∫ path, (payoff (path horizon) : ℝ) ∂historyPath(A, start, policy, current)) =
      ((A.stochasticHistoryLawFrom policy current horizon).expectRat payoff : ℝ) := by
  have hmeasurable : Measurable (fun h : A.HistoryFrom start => (payoff h : ℝ)) :=
    fun _ _ => MeasurableSpace.measurableSet_top
  have hmap := integral_map (μ := historyPath(A, start, policy, current))
    (φ := fun path => path horizon) (measurable_pi_apply horizon).aemeasurable
    hmeasurable.aestronglyMeasurable
  refine hmap.symm.trans ?_
  exact (historyLaw_eq_coordinate policy current horizon).symm ▸
    FiniteLawIntegral.integral_eq_expectRat
      (α := A.HistoryFrom start) (A.stochasticHistoryLawFrom policy current horizon) payoff

/-- Compute stopped payoff at a finite horizon from the existing history
executor. A nonterminal result contributes zero, irrespective of its payoff. -/
def stoppedExpectedPayoff (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ) : ℚ :=
  (A.stochasticHistoryLawFrom policy current horizon).expectRat
    (fun history => if A.IsTerminal history.1 then payoff history else 0)

/-- An already terminal continuation retains its payoff at every horizon,
including horizon zero. No additional action is selected after termination. -/
theorem stoppedExpectedPayoff_of_terminal (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ)
    (hterminal : A.IsTerminal current.1) :
    stoppedExpectedPayoff policy current horizon payoff = payoff current := by
  rw [stoppedExpectedPayoff, A.stochasticHistoryLawFrom_of_terminal policy current hterminal]
  simp [hterminal]

/-- The stopped algorithm and analytic integral use the same terminal test
and rational history payoff, including when some paths remain unfinished. -/
theorem integral_stoppedPayoff (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) (horizon : ℕ) (payoff : A.HistoryFrom start → ℚ) :
    (∫ path, (if A.IsTerminal (path horizon).1 then (payoff (path horizon) : ℝ) else 0)
      ∂historyPath(A, start, policy, current)) =
      (stoppedExpectedPayoff policy current horizon payoff : ℝ) := by
  simpa only [stoppedExpectedPayoff, apply_ite Rat.cast, Rat.cast_zero] using
    integral_historyPayoff policy current horizon
      (fun history => if A.IsTerminal history.1 then payoff history else 0)

end HistoryExecution

section ObservedUtility

open _root_.ExtensiveGame.ObservedGame

variable {N : Type*} {G : _root_.ExtensiveGame.ObservedGame N ℝ}
variable [(state : G.base.State) → Decidable (G.base.isTerminal state)]

/-- The existing stopped utility agrees with the exact finite algorithm on
the discrete model. Only terminal payoff compatibility is required; auxiliary
off-terminal extension values are immaterial. No marginal certificate is assumed. -/
theorem integral_stoppedUtility
    (extension : MeasurableHistoryModel.TerminalPayoffExtension G
      (MeasurableHistoryModel.discrete G))
    (policy : G.base.toArena.StochasticHistoryPolicy G.base.init)
    (current : CompleteHistory G) (horizon : ℕ) (player : N)
    (payoff : CompleteHistory G → ℚ)
    (hpayoff : ∀ history, G.base.isTerminal history.1 →
      (payoff history : ℝ) = G.base.payoff history.1 player) :
    (∫ path, extension.stoppedUtility horizon player path
      ∂historyPath(G.base.toArena, G.base.init, policy, current)) =
      (stoppedExpectedPayoff policy current horizon payoff : ℝ) := by
  rw [← integral_stoppedPayoff]
  apply integral_congr_ae
  filter_upwards [] with path
  by_cases hterminal : G.base.isTerminal (path horizon).1
  · rw [extension.stoppedUtility_eq_base horizon player path hterminal,
      if_pos hterminal, hpayoff _ hterminal]
  · rw [extension.stoppedUtility_eq_zero horizon player path hterminal, if_neg hterminal]

end ObservedUtility

section Regression

/-- Compact world states; all three routes eventually merge at `terminal`. -/
inductive World
  | root
  | middle
  | terminal
  deriving DecidableEq

/-- One early-terminal route and two distinct actions through the same
intermediate state. The middle state has one further legal action. -/
def worldArena : Arena where
  State := World
  Action
    | .root => Fin 3
    | .middle => Unit
    | .terminal => PEmpty
  next
    | .root, action => if action = 0 then .terminal else .middle
    | .middle, _ => .terminal

/-- Terminal payoffs depend on the route. The auxiliary payoff at both
nonterminal world states is 17, making premature payoff evaluation observable. -/
def historyPayoff (history : worldArena.HistoryFrom .root) : ℚ :=
  match history.1 with
  | .root | .middle => 17
  | .terminal => if history.2.length = 1 then 3 / 2 else -3

/-- The existing occurrence unfolding makes a history payoff an ordinary
state payoff without identifying routes sharing a compact world endpoint. -/
def game : _root_.ExtensiveGame Unit ℝ where
  toArena := worldArena.unfoldFrom .root
  init := Arena.HistoryFrom.nil worldArena .root
  mover := fun _ => none
  payoff := fun history _ => (historyPayoff history : ℝ)

/-- The standard complete-information wrapper used by the existing analytic
stopped-utility interface. The stochastic policy below supplies all chance data. -/
abbrev observed : _root_.ExtensiveGame.ObservedGame Unit ℝ :=
  _root_.ExtensiveGame.ObservedGame.completeInformation game

local instance terminalDecidable :
    (state : game.State) → Decidable (game.isTerminal state)
  | ⟨.root, _⟩ => isFalse (fun h => h.false (0 : Fin 3))
  | ⟨.middle, _⟩ => isFalse (fun h => h.false ())
  | ⟨.terminal, _⟩ => isTrue ⟨PEmpty.elim⟩

/-- Exact, nonuniform chance weights for the three root actions. -/
def rootLaw : FiniteLaw (Fin 3) where
  atoms := [(0, 1 / 2), (1, 1 / 3), (2, 1 / 6)]
  normalized := by norm_num

/-- Executable chance policy: draw a root action and then take the sole
middle action. A terminal history never requests an action. -/
def policy : game.toArena.StochasticHistoryPolicy game.init := by
  intro current hnonterminal
  rcases current with ⟨⟨state, history⟩, fullHistory⟩
  cases state with
  | root => exact rootLaw
  | middle => exact FiniteLaw.pure ()
  | terminal => exact False.elim (hnonterminal ⟨PEmpty.elim⟩)

/-- Initial complete history in the occurrence game. -/
def rootHistory : game.toArena.HistoryFrom game.init := ⟨game.init, .nil⟩

/-- The early terminal history, reached by root action zero. -/
def directHistory : game.toArena.HistoryFrom game.init :=
  ⟨_, Arena.History.nil.snoc (0 : Fin 3)⟩

/-- The terminal history through root action one and the middle action. -/
def leftHistory : game.toArena.HistoryFrom game.init :=
  ⟨_, (Arena.History.nil.snoc (1 : Fin 3)).snoc ()⟩

/-- The terminal history through root action two and the middle action. -/
def rightHistory : game.toArena.HistoryFrom game.init :=
  ⟨_, (Arena.History.nil.snoc (2 : Fin 3)).snoc ()⟩

/-- The rational terminal observable is exactly the base game's payoff
before casting to real values, including its auxiliary nonterminal values. -/
def payoff (history : game.toArena.HistoryFrom game.init) : ℚ :=
  historyPayoff history.1

/-- The regression's terminal extension uses the same payoff, with its
measurability proved from the discrete complete-history sigma algebra. -/
def payoffExtension :
    _root_.ExtensiveGame.ObservedGame.MeasurableHistoryModel.TerminalPayoffExtension
      observed (_root_.ExtensiveGame.ObservedGame.MeasurableHistoryModel.discrete observed) where
  payoff := fun _ history => (payoff history : ℝ)
  payoff_measurable := fun _ _ _ => MeasurableSpace.measurableSet_top
  payoff_eq_base := fun _ _ _ => rfl

/-- The actual two-step executor retains each complete action history with
its own weight, including the two middle routes sharing one world endpoint. -/
theorem two_step_atoms :
    (game.toArena.stochasticHistoryLawFrom policy rootHistory 2).atoms =
      [(directHistory, 1 / 2), (leftHistory, 1 / 3), (rightHistory, 1 / 6)] := by
  change [(directHistory, (1 / 2 : ℚ≥0) * 1),
    (leftHistory, (1 / 3 : ℚ≥0) * (1 * 1)),
    (rightHistory, (1 / 6 : ℚ≥0) * (1 * 1))] = _
  norm_num

/-- Two terminal histories have the same compact endpoint but different
payoffs; the occurrence unfolding keeps the distinction in the base state. -/
theorem same_world_different_payoffs :
    directHistory.1.1 = leftHistory.1.1 ∧
      payoff directHistory = 3 / 2 ∧ payoff leftHistory = -3 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Horizon zero observes the nonterminal root and must return zero even
though the auxiliary root payoff is 17. -/
theorem stopped_zero : payoff rootHistory = 17 ∧
    stoppedExpectedPayoff policy rootHistory 0 payoff = 0 := by
  -- Kernel reduction, without a native-computation proof axiom.
  decide +kernel

/-- Only the early terminal branch contributes after one step. -/
theorem stopped_one : stoppedExpectedPayoff policy rootHistory 1 payoff = 3 / 4 := by
  decide +kernel

/-- At two steps all branches contribute, with both signs and nonuniform
weights: `(1/2)(3/2) + (1/3)(-3) + (1/6)(-3) = -3/4`. -/
theorem stopped_two : stoppedExpectedPayoff policy rootHistory 2 payoff = -3 / 4 := by
  decide +kernel

/-- The early branch is absorbed at its actual terminal history for every
remaining horizon, including zero. -/
theorem direct_absorbed (horizon : ℕ) :
    stoppedExpectedPayoff policy directHistory horizon payoff = 3 / 2 := by
  rw [stoppedExpectedPayoff_of_terminal policy directHistory horizon payoff
    (show game.isTerminal directHistory.1 from ⟨PEmpty.elim⟩)]
  rfl

/-- The existing analytic stopped utility equals the executable result at
every horizon in this concrete model. No supplied path-law instance is required. -/
theorem analytic_stopped (horizon : ℕ) :
    (∫ path, payoffExtension.stoppedUtility horizon () path
      ∂historyPath(game.toArena, game.init, policy, rootHistory)) =
      (stoppedExpectedPayoff policy rootHistory horizon payoff : ℝ) :=
  integral_stoppedUtility payoffExtension policy rootHistory horizon () payoff
    (fun _ _ => rfl)

/-- The actual analytic stopped expectation is zero at horizon zero. -/
theorem analytic_zero :
    (∫ path, payoffExtension.stoppedUtility 0 () path
      ∂historyPath(game.toArena, game.init, policy, rootHistory)) = 0 := by
  rw [analytic_stopped, stopped_zero.2]
  norm_num

/-- The actual analytic stopped expectation after one event is `3/4`. -/
theorem analytic_one :
    (∫ path, payoffExtension.stoppedUtility 1 () path
      ∂historyPath(game.toArena, game.init, policy, rootHistory)) =
      3 / 4 := by
  rw [analytic_stopped, stopped_one]
  norm_num

/-- The actual analytic stopped expectation after two events is `-3/4`. -/
theorem analytic_two :
    (∫ path, payoffExtension.stoppedUtility 2 () path
      ∂historyPath(game.toArena, game.init, policy, rootHistory)) = -3 / 4 := by
  rw [analytic_stopped, stopped_two]
  norm_num

/-- info: true -/
#guard_msgs in
#eval stoppedExpectedPayoff policy rootHistory 0 payoff == 0 &&
  stoppedExpectedPayoff policy rootHistory 1 payoff == (3 / 4 : ℚ) &&
  stoppedExpectedPayoff policy rootHistory 2 payoff == (-3 / 4 : ℚ) &&
  stoppedExpectedPayoff policy directHistory 5 payoff == (3 / 2 : ℚ) &&
  payoff leftHistory == -3 && payoff rightHistory == (-3 : ℚ)

end Regression

end Examples.ExtensiveGame.FiniteExecutionIntegral
