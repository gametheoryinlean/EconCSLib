/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import Mathlib.Tactic

/-!
# Random finite-time termination regression

A fair root coin terminates immediately with payoff two or delays termination
for one event and pays one. A second policy terminates immediately with
probability one. The example computes distinct finite laws and utilities,
shows that the executable unfinished mass changes from one to one half to zero,
and checks the explicitly partial bounded terminal-time/payoff interface.

This is a discrete event-time example; it does not claim continuous time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Examples.RandomTermination

inductive State
  | root
  | delayed
  | win
  | small
  deriving DecidableEq

-- Countability is used only in measurability proofs. Supply the finite
-- injection inside Prop instead of deriving a choice-based runtime helper.
instance : Countable State :=
  ⟨⟨(fun state => match state with
      | .root => 0 | .delayed => 1 | .win => 2 | .small => 3),
    by intro a b h; cases a <;> cases b <;> simp_all⟩⟩

def arena : Arena where
  State := State
  Action
    | .root => Bool
    | .delayed => Unit
    | .win => PEmpty
    | .small => PEmpty
  next
    | .root, stop => if stop = true then .win else .delayed
    | .delayed, _ => .small

instance (s : arena.State) : Decidable (arena.IsTerminal s) := by
  cases s
  · exact isFalse fun h => h.false true
  · exact isFalse fun h => h.false ()
  · exact isTrue ⟨PEmpty.elim⟩
  · exact isTrue ⟨PEmpty.elim⟩

abbrev History := arena.HistoryFrom State.root

inductive HistoryCode
  | root
  | delayed
  | win
  | small

instance : Countable HistoryCode :=
  ⟨⟨(fun code => match code with
      | .root => 0 | .delayed => 1 | .win => 2 | .small => 3),
    by intro a b h; cases a <;> cases b <;> simp_all⟩⟩

def decodeHistory : HistoryCode → History
  | .root => ⟨_, Arena.History.nil⟩
  | .delayed =>
      ⟨_, Arena.History.nil.snoc
        (show arena.Action State.root from false)⟩
  | .win =>
      ⟨_, Arena.History.nil.snoc
        (show arena.Action State.root from true)⟩
  | .small =>
      ⟨_,
        (Arena.History.nil.snoc
          (show arena.Action State.root from false)).snoc
          (show arena.Action
            (arena.next State.root false) from ())⟩

theorem history_exists_code :
    ∀ {state : arena.State}
      (history : arena.History State.root state),
      ∃ code, decodeHistory code = ⟨state, history⟩ := by
  intro state history
  induction history with
  | nil =>
    exact ⟨HistoryCode.root, rfl⟩
  | @snoc previous history action ih =>
    obtain ⟨code, hcode⟩ := ih
    cases code with
    | root =>
      cases hcode
      cases action
      · exact ⟨HistoryCode.delayed, rfl⟩
      · exact ⟨HistoryCode.win, rfl⟩
    | delayed =>
      cases hcode
      cases action
      exact ⟨HistoryCode.small, rfl⟩
    | win =>
      cases hcode
      change PEmpty at action
      exact PEmpty.elim action
    | small =>
      cases hcode
      change PEmpty at action
      exact PEmpty.elim action

theorem decodeHistory_surjective :
    Function.Surjective decodeHistory := by
  rintro ⟨state, history⟩
  exact history_exists_code history

instance : Countable History :=
  decodeHistory_surjective.countable

instance : MeasurableSpace History := ⊤

instance : MeasurableSingletonClass History := by
  infer_instance

def initial : History :=
  decodeHistory .root

def delayed : History :=
  decodeHistory .delayed

def win : History :=
  decodeHistory .win

def small : History :=
  decodeHistory .small

theorem initial_not_terminal :
    ¬ arena.IsTerminal initial.1 := by
  change ¬ IsEmpty Bool
  exact fun h => h.false true

theorem delayed_not_terminal :
    ¬ arena.IsTerminal delayed.1 := by
  change ¬ IsEmpty Unit
  exact fun h => h.false ()

theorem win_terminal :
    arena.IsTerminal win.1 := by
  change IsEmpty PEmpty
  exact ⟨PEmpty.elim⟩

theorem small_terminal :
    arena.IsTerminal small.1 := by
  change IsEmpty PEmpty
  exact ⟨PEmpty.elim⟩

/-- The exact fair coin used by the executable finite-law policies. -/
def fairCoin : FiniteLaw Bool where
  atoms := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

def balancedPolicy :
    arena.StochasticHistoryPolicy State.root :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        simpa [arena, hstate] using
          fairCoin
    | delayed =>
        exact FiniteLaw.pure ()
    | win =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩
    | small =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩

def immediatePolicy :
    arena.StochasticHistoryPolicy State.root :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        exact FiniteLaw.pure true
    | delayed =>
        exact FiniteLaw.pure ()
    | win =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩
    | small =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨PEmpty.elim⟩

@[simp]
theorem balancedPolicy_initial :
    balancedPolicy initial initial_not_terminal =
      fairCoin := by
  rw [balancedPolicy]
  rfl

@[simp]
theorem immediatePolicy_initial :
    immediatePolicy initial initial_not_terminal =
      FiniteLaw.pure true := by
  rw [immediatePolicy]
  rfl

@[simp]
theorem balancedPolicy_delayed :
    balancedPolicy delayed delayed_not_terminal =
      FiniteLaw.pure () := by
  rw [balancedPolicy]
  rfl

def rootExtension (stop : Bool) : History :=
  if stop = true then win else delayed

def finalExtension (stop : Bool) : History :=
  if stop = true then win else small

/-- Executable indicator for the high-payoff terminal state. -/
def isWin (history : History) : Bool :=
  match history.1 with
  | .win => true
  | _ => false

theorem balanced_one_step_law :
    arena.stochasticHistoryLawFrom balancedPolicy initial 1 =
      (fairCoin).map
        rootExtension := by
  rw [arena.stochasticHistoryLawFrom_succ_of_not_terminal
    balancedPolicy initial 0 initial_not_terminal]
  rw [balancedPolicy_initial]
  simp only [arena.stochasticHistoryLawFrom_zero]
  calc
    _ =
        (fairCoin).map
          (fun action =>
            (⟨arena.next initial.1 action,
              initial.2.snoc action⟩ : History)) :=
      (FiniteLaw.map_eq_bind_pure_comp _ _).symm
    _ = _ := by
      rw [show
        (fun action =>
          (⟨arena.next initial.1 action,
            initial.2.snoc action⟩ : History)) =
            rootExtension by
          funext stop
          cases stop <;> rfl]
      rfl

theorem immediate_one_step_law :
    arena.stochasticHistoryLawFrom immediatePolicy initial 1 =
      FiniteLaw.pure win := by
  rw [arena.stochasticHistoryLawFrom_succ_of_not_terminal
    immediatePolicy initial 0 initial_not_terminal]
  rw [immediatePolicy_initial]
  simp only [arena.stochasticHistoryLawFrom_zero]
  change
    (FiniteLaw.pure true).bind
        (FiniteLaw.pure ∘ fun action =>
          (⟨arena.next initial.1 action,
            initial.2.snoc action⟩ : History)) =
      FiniteLaw.pure win
  rw [FiniteLaw.pure_bind]
  rfl

theorem balanced_two_step_law :
    arena.stochasticHistoryLawFrom balancedPolicy initial 2 =
      (fairCoin).map
        finalExtension := by
  rw [arena.stochasticHistoryLawFrom_succ_of_not_terminal
    balancedPolicy initial 1 initial_not_terminal]
  rw [balancedPolicy_initial]
  calc
    _ =
        (fairCoin).bind
          (FiniteLaw.pure ∘ finalExtension) := by
      apply congrArg
      funext stop
      cases stop
      · change
          arena.stochasticHistoryLawFrom balancedPolicy delayed 1 =
            FiniteLaw.pure (finalExtension false)
        rw [arena.stochasticHistoryLawFrom_succ_of_not_terminal
          balancedPolicy delayed 0 delayed_not_terminal]
        rw [balancedPolicy_delayed]
        simp [small, delayed, decodeHistory, arena, finalExtension]
        rfl
      · change
          arena.stochasticHistoryLawFrom balancedPolicy win 1 =
            FiniteLaw.pure (finalExtension true)
        rw [arena.stochasticHistoryLawFrom_succ_of_terminal
          balancedPolicy win 0 win_terminal]
        rfl
    _ = _ := (FiniteLaw.map_eq_bind_pure_comp _ _).symm

theorem balanced_one_step_win_probability :
    (arena.stochasticHistoryLawFrom balancedPolicy initial 1).eventMass isWin =
      (1 / 2 : ℚ≥0) := by
  rw [balanced_one_step_law]
  norm_num [FiniteLaw.eventMass, FiniteLaw.map, fairCoin, rootExtension,
    isWin, win, delayed, decodeHistory, arena]
  change (0 + (1 / 2 : ℚ≥0)) = 1 / 2
  exact zero_add _

theorem immediate_one_step_win_probability :
    (arena.stochasticHistoryLawFrom immediatePolicy initial 1).eventMass isWin = 1 := by
  rw [immediate_one_step_law]
  norm_num [FiniteLaw.eventMass, FiniteLaw.pure, isWin, win, decodeHistory, arena]
  rfl

theorem one_step_laws_differ :
    arena.stochasticHistoryLawFrom balancedPolicy initial 1 ≠
      arena.stochasticHistoryLawFrom immediatePolicy initial 1 := by
  intro heq
  have happly :=
    congrArg (fun p : FiniteLaw History => p.eventMass isWin) heq
  change
    (arena.stochasticHistoryLawFrom balancedPolicy initial 1).eventMass isWin =
      (arena.stochasticHistoryLawFrom immediatePolicy initial 1).eventMass isWin at happly
  rw [balanced_one_step_win_probability,
    immediate_one_step_win_probability] at happly
  norm_num at happly

/-- The executable one-step path marginal is exactly the bounded law. -/
theorem balanced_path_marginal_one :
    Arena.pathMarginal balancedPolicy initial 1 =
      fairCoin.map rootExtension :=
  balanced_one_step_law

theorem balanced_noneMass_zero :
    Arena.noneMass balancedPolicy initial 0 = 1 := by
  rw [Arena.noneMass, Arena.pathMarginal_zero]
  simp [FiniteLaw.eventMass, FiniteLaw.pure, initial_not_terminal]

theorem balanced_noneMass_one :
    Arena.noneMass balancedPolicy initial 1 = (1 / 2 : ℚ≥0) := by
  rw [Arena.noneMass, Arena.pathMarginal, balanced_one_step_law]
  norm_num [FiniteLaw.eventMass, FiniteLaw.map, fairCoin, rootExtension,
    delayed_not_terminal, win_terminal]

theorem balanced_noneMass_two :
    Arena.noneMass balancedPolicy initial 2 = 0 := by
  rw [Arena.noneMass, Arena.pathMarginal, balanced_two_step_law]
  norm_num [FiniteLaw.eventMass, FiniteLaw.map, fairCoin, finalExtension,
    small_terminal, win_terminal]

theorem balanced_noneMass_strictly_changes :
    Arena.noneMass balancedPolicy initial 1 <
      Arena.noneMass balancedPolicy initial 0 ∧
    Arena.noneMass balancedPolicy initial 2 <
      Arena.noneMass balancedPolicy initial 1 := by
  rw [balanced_noneMass_zero, balanced_noneMass_one,
    balanced_noneMass_two]
  norm_num

/-- One concrete lazy path used to exercise bounded terminal search. -/
def delayedPath : ℕ → History
  | 0 => initial
  | 1 => delayed
  | _ => small

example :
    Arena.terminalTime (A := arena) delayedPath 1 = none := by
  native_decide

example :
    Arena.terminalTime (A := arena) delayedPath 2 = some 2 := by
  native_decide

def payoff (history : History) : ℝ :=
  match history.1 with
  | .win => 2
  | .small => 1
  | .root => 0
  | .delayed => 0

theorem payoff_measurable : Measurable payoff :=
  measurable_of_countable _

/-- A nonconstant bounded-horizon utility: probability of reaching the
high-payoff terminal history by the selected fuel. -/
def boundedWinUtility
    (policy : arena.StochasticHistoryPolicy State.root)
    (fuel : ℕ) : ℚ≥0 :=
  (arena.stochasticHistoryLawFrom policy initial fuel).eventMass isWin

theorem balanced_utility_zero :
    boundedWinUtility balancedPolicy 0 = 0 := by
  rw [boundedWinUtility, arena.stochasticHistoryLawFrom_zero]
  norm_num [FiniteLaw.eventMass, isWin, initial, decodeHistory]

theorem balanced_utility_one :
    boundedWinUtility balancedPolicy 1 = (1 / 2 : ℚ≥0) :=
  balanced_one_step_win_probability

theorem immediate_utility_one :
    boundedWinUtility immediatePolicy 1 = 1 :=
  immediate_one_step_win_probability

theorem horizon_changes_balanced_utility :
    boundedWinUtility balancedPolicy 0 ≠
      boundedWinUtility balancedPolicy 1 := by
  rw [balanced_utility_zero, balanced_utility_one]
  norm_num

theorem policies_have_different_utility :
    boundedWinUtility balancedPolicy 1 ≠
      boundedWinUtility immediatePolicy 1 := by
  rw [balanced_utility_one, immediate_utility_one]
  norm_num

example :
    Arena.terminalPayoff (A := arena) payoff delayedPath 1 = none := by
  native_decide

example :
    Arena.terminalPayoff (A := arena) payoff delayedPath 2 = some 1 := by
  rw [Arena.terminalPayoff,
    show Arena.terminalTime (A := arena) delayedPath 2 = some 2 by
      native_decide]
  change some (payoff small) = some 1
  rfl

end Examples.RandomTermination
