/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome
import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable
import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import Mathlib.Tactic

/-!
# Unbounded random-termination regression for measurable outcomes

At every nonterminal history, a fair chance move either stops or repeats.
Termination therefore occurs almost surely, but its time has unbounded
support: the unfinished mass at horizon `n` is exactly `2⁻ⁿ`, which is
strictly positive for every finite `n` and converges to zero.

The example uses a supplied analytic profile whose finite coordinate
marginals are certified against the executable chance process. Countability
alone no longer manufactures that analytic profile. It verifies both sides
of the outcome boundary:

* no fixed horizon satisfies `TerminatesBy`;
* `TerminatesAlmostSurely` does hold;
* bounded stopped terminal payoff converges in expectation to eventual
  terminal payoff.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary

open ExtensiveGame
open MeasurableKernelArena

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

local macro "finiteLawMeasureTop(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • @Measure.dirac _ ⊤ atom.1 + rest)
      0)

/-! ## A fair repeat-or-stop chance game -/

/-- The process is either active or terminal. -/
inductive Node
  | active
  | terminal
  deriving DecidableEq

/-- Proof-only countability via the explicit tags `active ↦ 0`, `terminal ↦ 1`.
The finite executor does not extract an encoding from this instance. -/
instance : Countable Node :=
  ⟨⟨(fun node => match node with
      | .active => 0 | .terminal => 1),
    by intro a b h; cases a <;> cases b <;> simp_all⟩⟩

/-- A Boolean chance action is available exactly while active. -/
abbrev nodeAction : Node → Type
  | .active => Bool
  | .terminal => Empty

/-- `true` terminates and `false` repeats. -/
def nodeNext : (state : Node) → nodeAction state → Node
  | .active, false => .active
  | .active, true => .terminal
  | .terminal, action => nomatch action

/-- Both states have no strategic mover. -/
def nodeMover : Node → Option Unit :=
  fun _ => none

/-- Terminal payoff is one. -/
def nodePayoff : Node → Unit → ℝ
  | .active, _ => 0
  | .terminal, _ => 1

/-- Compact underlying extensive game. -/
abbrev base : ExtensiveGame Unit ℝ where
  State := Node
  Action := nodeAction
  next := nodeNext
  init := .active
  mover := nodeMover
  payoff := nodePayoff

/-- Trivial observations; there are no reachable player decisions. -/
def observed : ObservedGame Unit ℝ where
  base := base
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := fun _ _ _ _ => ()
  infoAt_observe := fun _ _ _ _ => rfl
  InfoAction := fun _ _ => Unit
  actionEquiv := by
    intro history i hmover _hnonterminal
    change nodeMover history.1 = some i at hmover
    change none = some i at hmover
    contradiction

/-- Executable fair-coin law. -/
def fairCoin : FiniteLaw Bool where
  atoms := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

/-- Fair chance law at every active complete history. -/
def game : ObservedChanceGame Unit ℝ where
  observed := observed
  chanceKernel := by
    intro history hchance
    cases hstate : history.1 with
    | active =>
        simpa [base, nodeAction, hstate] using fairCoin
    | terminal =>
        exact
          (hchance.2 (by
            rw [hstate]
            change IsEmpty Empty
            exact ⟨Empty.elim⟩)).elim

abbrev History :=
  game.observed.base.toArena.HistoryFrom
    game.observed.base.init

/-- Empty active history. -/
def initialHistory : History :=
  Arena.HistoryFrom.nil base.toArena base.init

/-- Typed path of `n` consecutive repeat actions. -/
def activePath :
    (n : ℕ) →
      base.toArena.History base.init .active
  | 0 => Arena.History.nil
  | n + 1 => (activePath n).snoc false

/-- The history consisting of `n` consecutive repeat actions. -/
def activeHistory (n : ℕ) : History :=
  ⟨.active, activePath n⟩

/-- Stop after exactly `n` preceding repeat actions. -/
def terminalHistory (n : ℕ) : History :=
  ⟨.terminal,
    (activePath n).snoc true⟩

@[simp]
theorem activeHistory_state (n : ℕ) :
    (activeHistory n).1 = .active :=
  rfl

@[simp]
theorem terminalHistory_state (n : ℕ) :
    (terminalHistory n).1 = .terminal :=
  rfl

/-- Active and terminal complete histories are always distinct. -/
theorem activeHistory_ne_terminalHistory
    (activeIndex terminalIndex : ℕ) :
    activeHistory activeIndex ≠ terminalHistory terminalIndex := by
  intro heq
  have hstate := congrArg Sigma.fst heq
  change Node.active = Node.terminal at hstate
  contradiction

/-- Every finite complete history is either a run of repeats or such a run
followed by the stopping action. -/
theorem history_classify
    (history : History) :
    (∃ n, history = activeHistory n) ∨
      ∃ n, history = terminalHistory n := by
  rcases history with ⟨state, path⟩
  induction path with
  | nil =>
      exact Or.inl ⟨0, rfl⟩
  | @snoc previous path action ih =>
      rcases ih with ⟨n, hactive⟩ | ⟨n, hterminal⟩
      · cases hactive
        cases action
        · exact Or.inl ⟨n + 1, rfl⟩
        · exact Or.inr ⟨n, rfl⟩
      · cases hterminal
        exact Empty.elim action

/-- A countable cover of all complete histories. -/
def decodeHistory : ℕ ⊕ ℕ → History
  | .inl n => activeHistory n
  | .inr n => terminalHistory n

theorem decodeHistory_surjective :
    Function.Surjective decodeHistory := by
  intro history
  rcases history_classify history with
    ⟨n, hactive⟩ | ⟨n, hterminal⟩
  · exact ⟨.inl n, hactive.symm⟩
  · exact ⟨.inr n, hterminal.symm⟩

instance historyCountable :
    Countable History :=
  decodeHistory_surjective.countable

instance baseHistoryMeasurable :
    MeasurableSpace
      (base.toArena.HistoryFrom base.init) :=
  ⊤

instance baseHistoryMeasurableSingletonClass :
    MeasurableSingletonClass
      (base.toArena.HistoryFrom base.init) := by
  infer_instance

instance historyMeasurable :
    MeasurableSpace History :=
  ⊤

instance historyMeasurableSingletonClass :
    MeasurableSingletonClass History := by
  infer_instance

instance localActionCountable
    (history : History) :
    Countable (game.observed.base.Action history.1) := by
  change Countable (nodeAction history.1)
  cases history.1 <;> infer_instance

instance terminalDecidable
    (state : Node) :
    Decidable (base.isTerminal state) := by
  cases state with
  | active =>
      exact isFalse fun hterminal => hterminal.false false
  | terminal =>
      exact isTrue ⟨Empty.elim⟩

instance gameTerminalDecidable
    (state : game.observed.base.State) :
    Decidable (game.observed.base.isTerminal state) := by
  change Decidable (base.isTerminal state)
  infer_instance

/-- The player profile is unreachable but supplies the structural behavioral
argument expected by the observed-chance executor. -/
def behavioralProfile :
    game.observed.BehavioralProfile :=
  fun _ _ => FiniteLaw.pure ()

/-- The induced history policy flips the fair chance coin at every active
history. -/
def fairHistoryPolicy :
    base.toArena.StochasticHistoryPolicy base.init :=
  ObservedChanceGame.BehavioralProfile.toHistoryPolicy
    game behavioralProfile

theorem activeHistory_nonterminal (n : ℕ) :
    ¬ base.isTerminal (activeHistory n).1 := by
  change ¬ IsEmpty (nodeAction .active)
  simp only [nodeAction]
  intro hempty
  exact hempty.false false

theorem terminalHistory_terminal (n : ℕ) :
    base.isTerminal (terminalHistory n).1 := by
  change IsEmpty (nodeAction .terminal)
  simp only [nodeAction]
  exact ⟨Empty.elim⟩

@[simp]
theorem fairHistoryPolicy_active
    (n : ℕ) :
    fairHistoryPolicy
        (activeHistory n)
      (activeHistory_nonterminal n) =
      fairCoin := by
  unfold fairHistoryPolicy
  rw [
    ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance
      game behavioralProfile
      (activeHistory n)
      (activeHistory_nonterminal n)
      rfl]
  rfl

private theorem FiniteLaw.eventMass_bind
    {α β : Type*} (law : FiniteLaw α)
    (next : α → FiniteLaw β) (event : β → Bool) :
    (law.bind next).eventMass event =
      (law.atoms.map fun atom =>
        atom.2 * (next atom.1).eventMass event).sum := by
  unfold FiniteLaw.eventMass
  rw [FiniteLaw.bind_atoms]
  induction law.atoms with
  | nil => simp
  | cons atom atoms ih =>
      rcases atom with ⟨outcome, weight⟩
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      rw [ih]
      congr 1
      simp only [List.map_map, Function.comp_def]
      induction (next outcome).atoms with
      | nil => simp
      | cons inner inners ihInner =>
          rcases inner with ⟨innerOutcome, innerWeight⟩
          simp only [List.map_cons, List.sum_cons]
          rw [ihInner]
          cases hevent : event innerOutcome <;>
            simp [mul_add]

@[simp]
theorem activeHistory_next_repeat (n : ℕ) :
    (⟨base.next (activeHistory n).1 false,
        (activeHistory n).2.snoc false⟩ : History) =
      activeHistory (n + 1) :=
  rfl

@[simp]
theorem activeHistory_next_stop (n : ℕ) :
    (⟨base.next (activeHistory n).1 true,
        (activeHistory n).2.snoc true⟩ : History) =
      terminalHistory n :=
  rfl

/-- After `fuel` further fair moves from an active history, the probability
of the unique still-active history is exactly `2⁻fuel`. -/
theorem active_survival_probability
    (offset fuel : ℕ) :
    (base.toArena.stochasticHistoryLawFrom
        fairHistoryPolicy (activeHistory offset) fuel).eventMass
        (fun endpoint =>
          decide (¬ base.isTerminal endpoint.1)) =
      (1 / 2 : ℚ≥0) ^ fuel := by
  induction fuel generalizing offset with
  | zero =>
      rw [base.toArena.stochasticHistoryLawFrom_zero]
      have hnonterminal :
          ¬ base.isTerminal (activeHistory offset).1 :=
        activeHistory_nonterminal offset
      simp [FiniteLaw.eventMass]
      simpa only [activeHistory_state] using hnonterminal
  | succ fuel ih =>
      rw [
        base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          fairHistoryPolicy (activeHistory offset) fuel
          (activeHistory_nonterminal offset),
        fairHistoryPolicy_active]
      rw [FiniteLaw.eventMass_bind]
      simp only [fairCoin, List.map, List.sum,
        List.foldr_cons, List.foldr_nil, add_zero]
      change
        (1 / 2 : ℚ≥0) *
              (base.toArena.stochasticHistoryLawFrom
                fairHistoryPolicy (activeHistory (offset + 1)) fuel).eventMass
                (fun endpoint =>
                  decide (¬ base.isTerminal endpoint.1)) +
            (1 / 2 : ℚ≥0) *
              (base.toArena.stochasticHistoryLawFrom
                fairHistoryPolicy (terminalHistory offset) fuel).eventMass
                (fun endpoint =>
                  decide (¬ base.isTerminal endpoint.1)) =
          (1 / 2 : ℚ≥0) ^ (fuel + 1)
      rw [ih (offset + 1)]
      rw [
        base.toArena.stochasticHistoryLawFrom_of_terminal
          fairHistoryPolicy (terminalHistory offset)
          (terminalHistory_terminal offset)]
      have hterminal : base.isTerminal Node.terminal := by
        change IsEmpty Empty
        exact ⟨Empty.elim⟩
      simp [FiniteLaw.eventMass, hterminal, pow_succ, mul_comm]

/-- Every supported nonterminal endpoint after `fuel` further moves is the
unique all-repeat history. -/
theorem nonterminal_support_unique
    (offset fuel : ℕ)
    (endpoint : History)
    (hnonterminal :
      ¬ base.isTerminal endpoint.1)
    (hsupport :
      (base.toArena.stochasticHistoryLawFrom
        fairHistoryPolicy (activeHistory offset) fuel).HasPositiveAtom
          endpoint) :
    endpoint = activeHistory (offset + fuel) := by
  induction fuel generalizing offset endpoint with
  | zero =>
      rw [base.toArena.stochasticHistoryLawFrom_zero] at hsupport
      exact
        (FiniteLaw.hasPositiveAtom_pure_iff
          (activeHistory offset) endpoint).mp hsupport
  | succ fuel ih =>
      rw [
        base.toArena.stochasticHistoryLawFrom_succ_of_not_terminal
          fairHistoryPolicy (activeHistory offset) fuel
          (activeHistory_nonterminal offset),
        fairHistoryPolicy_active] at hsupport
      obtain ⟨action, _haction, htail⟩ :=
        (FiniteLaw.hasPositiveAtom_bind_iff
          fairCoin
          (fun action =>
            base.toArena.stochasticHistoryLawFrom
              fairHistoryPolicy
              ⟨base.next (activeHistory offset).1 action,
                (activeHistory offset).2.snoc action⟩
              fuel)
              endpoint).mp hsupport
      cases action with
      | false =>
          have htail' :
              (base.toArena.stochasticHistoryLawFrom
                fairHistoryPolicy
                (activeHistory (offset + 1)) fuel).HasPositiveAtom endpoint := by
            simpa only [activeHistory_next_repeat] using htail
          have heq :=
            ih (offset + 1) endpoint hnonterminal htail'
          calc
            endpoint = activeHistory ((offset + 1) + fuel) := heq
            _ = activeHistory (offset + (fuel + 1)) := by
              congr 1
              omega
      | true =>
          have htail' :
              (base.toArena.stochasticHistoryLawFrom
                fairHistoryPolicy
                (terminalHistory offset) fuel).HasPositiveAtom endpoint := by
            simpa only [activeHistory_next_stop] using htail
          rw [
            base.toArena.stochasticHistoryLawFrom_of_terminal
              fairHistoryPolicy (terminalHistory offset)
              (terminalHistory_terminal offset)] at htail'
          have heq :
              endpoint = terminalHistory offset :=
            (FiniteLaw.hasPositiveAtom_pure_iff
              (terminalHistory offset) endpoint).mp htail'
          rw [heq] at hnonterminal
          exact
            (hnonterminal
              (terminalHistory_terminal offset)).elim

/-- Nonterminal complete histories. -/
def nonterminalHistories : Set History :=
  {history | ¬ base.isTerminal history.1}

theorem nonterminalHistories_measurable :
    MeasurableSet nonterminalHistories :=
  (Set.to_countable _).measurableSet

private theorem finiteLawMeasure_apply_eq_eventMass
    {α : Type*} [MeasurableSpace α]
    (law : FiniteLaw α) (event : α → Bool)
    (hevent : MeasurableSet {outcome | event outcome}) :
    finiteLawMeasure(law) {outcome | event outcome} =
      (law.eventMass event : ENNReal) := by
  have hzero : ((0 : ℚ≥0) : ENNReal) = 0 := by
    change (((0 : ℚ≥0) : NNReal) : ENNReal) = 0
    simp
  have hadd (p q : ℚ≥0) :
      ((p + q : ℚ≥0) : ENNReal) =
        (p : ENNReal) + (q : ENNReal) := by
    change (((p + q : ℚ≥0) : NNReal) : ENNReal) =
      ((p : NNReal) : ENNReal) + ((q : NNReal) : ENNReal)
    simp
  have hmeasure :
      finiteLawMeasure(law) {outcome | event outcome} =
        (((law.atoms.map fun atom =>
          if event atom.1 then atom.2 else 0).sum : ℚ≥0) : ENNReal) := by
    induction law.atoms with
    | nil => simp [hzero]
    | cons atom atoms ih =>
        rcases atom with ⟨outcome, weight⟩
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        rw [Measure.add_apply, Measure.smul_apply,
          Measure.dirac_apply' _ hevent, ih]
        cases heventOutcome : event outcome <;>
          simp [heventOutcome, hadd]
  exact hmeasure

/-- The bounded executor's unfinished mass is exactly the probability of the
unique all-repeat history. -/
theorem finite_unfinished_mass
    (fuel : ℕ) :
    finiteLawMeasure(
      base.toArena.stochasticHistoryLawFrom
        fairHistoryPolicy initialHistory fuel) nonterminalHistories =
      (1 / 2 : ENNReal) ^ fuel := by
  let p :=
    base.toArena.stochasticHistoryLawFrom
      fairHistoryPolicy initialHistory fuel
  have hsurvival :
      p.eventMass (fun endpoint =>
          decide (¬ base.isTerminal endpoint.1)) =
        (1 / 2 : ℚ≥0) ^ fuel := by
    dsimp only [p]
    simpa only [initialHistory, activeHistory, activePath,
      Nat.zero_add] using
      active_survival_probability 0 fuel
  change finiteLawMeasure(p) nonterminalHistories =
      (1 / 2 : ENNReal) ^ fuel
  have hdecMeasurable :
      MeasurableSet {endpoint : History |
        decide (¬ base.isTerminal endpoint.1)} := by
    exact nonterminalHistories_measurable
  have hdecSet :
      {endpoint : History | decide (¬ base.isTerminal endpoint.1)} =
        nonterminalHistories := by
    ext endpoint
    simp [nonterminalHistories]
  calc
    finiteLawMeasure(p) nonterminalHistories =
        finiteLawMeasure(p)
          {endpoint : History |
            decide (¬ base.isTerminal endpoint.1)} := by
      exact
        (congrArg
          (fun event : Set History => finiteLawMeasure(p) event)
          hdecSet).symm
    _ =
        (p.eventMass (fun endpoint =>
          decide (¬ base.isTerminal endpoint.1)) : ENNReal) := by
      exact finiteLawMeasure_apply_eq_eventMass p _ hdecMeasurable
    _ = (((1 / 2 : ℚ≥0) ^ fuel : ℚ≥0) : ENNReal) := by
      rw [hsurvival]
    _ = (1 / 2 : ENNReal) ^ fuel := by
      calc
        (((1 / 2 : ℚ≥0) ^ fuel : ℚ≥0) : ENNReal) =
            ((((1 / 2 : ℚ≥0) ^ fuel : ℚ≥0) : NNReal) : ENNReal) :=
          (ENNReal.coe_nnratCast _).symm
        _ = (((1 / 2 : ℚ≥0) : NNReal) : ENNReal) ^ fuel := by
          congr 1
          apply NNReal.eq
          simp
        _ = ((1 / 2 : ℚ≥0) : ENNReal) ^ fuel := by
          rw [ENNReal.coe_nnratCast]
        _ = (1 / 2 : ENNReal) ^ fuel := by
          congr 1
          change (((1 / 2 : ℚ≥0) : NNReal) : ENNReal) = _
          norm_num

/-! ## Supplied analytic presentation and certified finite marginals -/

instance completeHistoryActionCountable :
    Countable
      (ObservedChanceGame.CompleteHistoryAction game) := by
  infer_instance

/-- Canonical discrete complete-history model. -/
noncomputable def historyModel :
    game.MeasurableHistoryModel :=
  ObservedChanceGame.MeasurableHistoryModel.discrete game

instance historyModelPathEventCountable :
    Countable historyModel.toArena.PathEvent := by
  change
    Countable
      (History ×
        (Unit ⊕
          ObservedChanceGame.CompleteHistoryAction game))
  infer_instance

instance historyModelPathEventMeasurableSingletonClass :
    MeasurableSingletonClass historyModel.toArena.PathEvent := by
  change
    MeasurableSingletonClass
      (game.AnalyticHistoryArena).PathEvent
  infer_instance

variable
  {presentation : game.observed.MeasurableKernelPresentation historyModel}
  {analyticProfile : presentation.KernelBehavioralProfile}
  (finiteMarginals :
    ∀ horizon,
      (analyticProfile.statePathMeasure initialHistory).map
          (fun path => path horizon) =
        finiteLawMeasureTop(
          base.toArena.stochasticHistoryLawFrom
            fairHistoryPolicy initialHistory horizon))

include finiteMarginals

/-- Every finite analytic state coordinate recovers exactly the bounded
stopped-history executor. -/
theorem analytic_finite_state_law
    (horizon : ℕ) :
    (analyticProfile.statePathMeasure initialHistory).map
        (fun path => path horizon) =
      finiteLawMeasureTop(
        base.toArena.stochasticHistoryLawFrom
          fairHistoryPolicy initialHistory horizon) :=
  finiteMarginals horizon

/-- The analytic infinite-path law has exact unfinished mass `2⁻horizon`. -/
theorem analytic_unfinished_mass
    (horizon : ℕ) :
    analyticProfile.unfinishedMass initialHistory horizon =
      (1 / 2 : ENNReal) ^ horizon := by
  unfold
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.unfinishedMass
    ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.UnfinishedAt
  change
    analyticProfile.statePathMeasure initialHistory
        ((fun path => path horizon) ⁻¹'
          nonterminalHistories) =
      (1 / 2 : ENNReal) ^ horizon
  rw [← Measure.map_apply
    (measurable_pi_apply horizon)
    nonterminalHistories_measurable]
  rw [analytic_finite_state_law finiteMarginals]
  exact finite_unfinished_mass horizon

/-- Unfinished mass vanishes although it is positive at every finite
horizon. -/
theorem analytic_unfinished_mass_tendsto_zero :
    Filter.Tendsto
      (analyticProfile.unfinishedMass initialHistory)
      Filter.atTop
      (nhds 0) := by
  have hpow :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (1 / 2 : ENNReal)) (by norm_num)
  apply hpow.congr'
  exact
    Filter.Eventually.of_forall fun horizon =>
      (analytic_unfinished_mass finiteMarginals horizon).symm

/-- The analytic profile reaches some terminal history almost surely. -/
theorem analytic_reachesTerminalAlmostSurely :
    analyticProfile.ReachesTerminalAlmostSurely
      initialHistory :=
  analyticProfile.reachesTerminalAlmostSurely_of_unfinishedMass_tendsto_zero
    initialHistory (analytic_unfinished_mass_tendsto_zero finiteMarginals)

/-- Countable-discrete terminal awareness upgrades reachability to eventual
terminal absorption. -/
theorem analytic_terminatesAlmostSurely :
    analyticProfile.TerminatesAlmostSurely
      initialHistory :=
  analyticProfile.terminatesAlmostSurely_of_reachesTerminalAlmostSurely
    initialHistory (analytic_reachesTerminalAlmostSurely finiteMarginals)

/-- There is no deterministic finite bound on the random termination time. -/
theorem analytic_not_terminatesBy
    (horizon : ℕ) :
    ¬ analyticProfile.TerminatesBy initialHistory horizon := by
  intro hterminates
  have hzero :
      analyticProfile.unfinishedMass initialHistory horizon = 0 :=
    (analyticProfile.terminatesBy_iff_unfinishedMass_eq_zero
      initialHistory horizon).mp hterminates
  rw [analytic_unfinished_mass finiteMarginals] at hzero
  have hpositive :
      0 < (1 / 2 : ENNReal) ^ horizon := by
    exact
      (pos_iff_ne_zero).2
        (pow_ne_zero _ (by norm_num))
  exact hpositive.ne' hzero

omit finiteMarginals in
/-- Base terminal payoff, extended measurably to every complete history and
bounded by one. -/
def terminalPayoff :
    ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension
      game.observed historyModel where
  payoff := fun _ history =>
    base.payoff history.1 ()
  payoff_measurable := by
    intro _
    change
      @Measurable History ℝ ⊤ inferInstance
        (fun history => base.payoff history.1 ())
    exact Measurable.of_discrete
  payoff_eq_base := by
    intro _ _ _
    rfl
  bound := 1
  norm_payoff_le := by
    intro i history _
    cases i
    cases history.1 <;> simp [nodePayoff]

/-- The general dominated-convergence result applies to the strict
unbounded-support termination example. -/
theorem analytic_expectedUtility_tendsto :
    Filter.Tendsto
      (fun horizon =>
        (terminalPayoff.stoppedBoundedPathUtility horizon).expectedUtility
          analyticProfile initialHistory ())
      Filter.atTop
      (nhds
        (terminalPayoff.expectedEventualUtility
          analyticProfile initialHistory
          (analytic_terminatesAlmostSurely finiteMarginals) ())) :=
  terminalPayoff.expectedUtility_tendsto_expectedEventualUtility
    analyticProfile initialHistory
    (analytic_terminatesAlmostSurely finiteMarginals) ()

end Examples.ObservedMeasurableKernelAlmostSureOutcomeBoundary
