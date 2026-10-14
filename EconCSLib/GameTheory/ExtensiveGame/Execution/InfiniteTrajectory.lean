/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.FiniteCompletePath
import EconCSLib.GameTheory.ExtensiveGame.Execution.Truncation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Executable finite prefixes and supplied infinite path laws

This module separates two semantic responsibilities that were previously
combined by an Ionescu--Tulcea construction hidden inside a noncomputable
definition.

* `pathMarginal`, `noneMass`, and `stoppedPayoffLaw` are executable finite
  computations backed by `FiniteLaw` and exact rational weights.
* `pathLaw`, `pathProbabilityMeasure`, and `terminalPayoffLaw` only project
  caller-supplied probability measures. Their legality and finite-marginal
  coherence are explicit theorem hypotheses.
* `terminalTime` performs bounded search and returns `Option`; an infinite path
  is not treated as a terminating sample-producing computation.

Existence or extension arguments for complete path measures belong in theorem
proofs or in downstream supplied presentations. This module never
manufactures a kernel or an infinite law through classical choice.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Arena

variable {A : Arena} {start : A.State}

local macro "finiteLawMeasure(" law:term ")" : term =>
  `(($law).atoms.foldr
      (fun atom rest =>
        (atom.2 : ENNReal) • Measure.dirac atom.1 + rest)
      0)

private theorem finiteLawMeasure_pure
    {X : Type*} [MeasurableSpace X] (outcome : X) :
    finiteLawMeasure(FiniteLaw.pure outcome) =
      Measure.dirac outcome := by
  rw [FiniteLaw.pure_atoms]
  simp only [List.foldr_cons, List.foldr_nil]
  change (((1 : ℚ≥0) : NNReal) : ENNReal) •
      Measure.dirac outcome + 0 = Measure.dirac outcome
  simp

/-- One executable terminal-absorbing stochastic history step. -/
def absorbingStepLaw
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    FiniteLaw (A.HistoryFrom start) :=
  if hterminal : A.IsTerminal current.1 then
    FiniteLaw.pure current
  else
    (policy current hterminal).map fun action =>
      ⟨A.next current.1 action, current.2.snoc action⟩

@[simp]
theorem absorbingStepLaw_eq_stochasticHistoryLawFrom_one
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    absorbingStepLaw policy current =
      A.stochasticHistoryLawFrom policy current 1 := by
  by_cases hterminal : A.IsTerminal current.1
  · simp [absorbingStepLaw, hterminal]
  · rw [absorbingStepLaw, dif_neg hterminal]
    rw [A.stochasticHistoryLawFrom_succ_of_not_terminal
      policy current 0 hterminal]
    simpa [Function.comp_def] using
      (FiniteLaw.map_eq_bind_pure_comp
        (fun action =>
          (⟨A.next current.1 action, current.2.snoc action⟩ :
            A.HistoryFrom start))
        (policy current hterminal))

/-- The executable history law at one bounded event coordinate. -/
def pathMarginal
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (time : ℕ) :
    FiniteLaw (A.HistoryFrom start) :=
  A.stochasticHistoryLawFrom policy current time

@[simp]
theorem pathMarginal_zero
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start) :
    pathMarginal policy current 0 = FiniteLaw.pure current :=
  A.stochasticHistoryLawFrom_zero policy current

/-- Bounded marginals compose by one executable terminal-absorbing step. -/
theorem pathMarginal_succ
    [(s : A.State) → Decidable (A.IsTerminal s)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (time : ℕ) :
    pathMarginal policy current (time + 1) =
      (pathMarginal policy current time).bind
        (absorbingStepLaw policy) := by
  rw [pathMarginal, pathMarginal,
    A.stochasticHistoryLawFrom_add policy current time 1]
  apply congrArg
    ((A.stochasticHistoryLawFrom policy current time).bind)
  funext middle
  exact absorbingStepLaw_eq_stochasticHistoryLawFrom_one policy middle |>.symm

/-- Project a caller-supplied complete path probability measure.

The policy and current history index the intended semantics. Coherence with
the executable finite prefixes is supplied to the theorems below rather than
being manufactured here by an extension theorem. -/
def pathLaw
    [MeasurableSpace (A.HistoryFrom start)]
    (_policy : A.StochasticHistoryPolicy start)
    (_current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start)) :
    Measure (ℕ → A.HistoryFrom start) :=
  supplied

/-- Every coordinate of a supplied complete path law agrees with executable
bounded evolution when the caller supplies that coherence certificate. -/
theorem pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          finiteLawMeasure(pathMarginal policy current time))
    (time : ℕ) :
    (pathLaw policy current supplied).map (fun path => path time) =
      finiteLawMeasure(pathMarginal policy current time) :=
  finiteMarginal time

/-- A supplied coherent complete path law starts at its indexed history. -/
theorem pathLaw_initial
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          finiteLawMeasure(pathMarginal policy current time)) :
    (pathLaw policy current supplied).map (fun path => path 0) =
      Measure.dirac current := by
  rw [pathLaw_finiteMarginal_eq_stochasticHistoryLawFrom_finiteLawMeasure
    policy current supplied finiteMarginal 0]
  rw [pathMarginal_zero, finiteLawMeasure_pure]

/-- Expose a supplied almost-sure transition-coherence certificate. -/
theorem pathLaw_ae_legalTransition
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (legalTransition :
      ∀ᵐ path ∂(supplied : Measure (ℕ → A.HistoryFrom start)),
        ∀ time,
          IsLegalAbsorbingTransition policy
            (path time) (path (time + 1))) :
    ∀ᵐ path ∂pathLaw policy current supplied,
      ∀ time,
        IsLegalAbsorbingTransition policy
          (path time) (path (time + 1)) :=
  legalTransition

/-- Finite-marginal and transition coherence imply canonical complete-play
legality for the supplied law. -/
theorem pathLaw_ae_isCompletePlayPathFrom
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (finiteMarginal :
      ∀ time,
        (supplied : Measure (ℕ → A.HistoryFrom start)).map
            (fun path => path time) =
          finiteLawMeasure(pathMarginal policy current time))
    (legalTransition :
      ∀ᵐ path ∂(supplied : Measure (ℕ → A.HistoryFrom start)),
        ∀ time,
          IsLegalAbsorbingTransition policy
            (path time) (path (time + 1))) :
    ∀ᵐ path ∂pathLaw policy current supplied,
      A.IsCompletePlayPathFrom current path := by
  letI : IsProbabilityMeasure (pathLaw policy current supplied) := by
    rw [pathLaw]
    infer_instance
  have hinitial :
      ∀ᵐ path ∂pathLaw policy current supplied,
        path 0 = current := by
    have hmeasurable :
        MeasurableSet
          {path : ℕ → A.HistoryFrom start | path 0 = current} :=
      (measurable_pi_apply 0 :
        Measurable
          (fun path : ℕ → A.HistoryFrom start => path 0))
        (measurableSet_singleton current)
    change
      {path : ℕ → A.HistoryFrom start | path 0 = current} ∈
        ae (pathLaw policy current supplied)
    rw [MeasureTheory.mem_ae_iff_prob_eq_one hmeasurable]
    change
      pathLaw policy current supplied
          ((fun path : ℕ → A.HistoryFrom start => path 0) ⁻¹'
            {current}) = 1
    rw [← Measure.map_apply
      (measurable_pi_apply 0 :
        Measurable
          (fun path : ℕ → A.HistoryFrom start => path 0))
      (measurableSet_singleton current)]
    rw [pathLaw_initial policy current supplied finiteMarginal]
    simp
  filter_upwards
    [hinitial,
      pathLaw_ae_legalTransition
        policy current supplied legalTransition]
      with path hzero hlegal
  refine ⟨hzero, fun time => ?_⟩
  rcases hlegal time with hstay | hstep
  · exact Or.inl hstay
  · rcases hstep with
      ⟨_hnonterminal, action, _hsupport, hnext⟩
    exact Or.inr ⟨action, hnext⟩

/-- Terminal histories are absorbing almost surely under an explicitly
supplied transition-coherence certificate. -/
theorem pathLaw_terminal_absorbing
    [(s : A.State) → Decidable (A.IsTerminal s)]
    [MeasurableSpace (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start))
    (legalTransition :
      ∀ᵐ path ∂(supplied : Measure (ℕ → A.HistoryFrom start)),
        ∀ time,
          IsLegalAbsorbingTransition policy
            (path time) (path (time + 1))) :
    ∀ᵐ path ∂pathLaw policy current supplied,
      ∀ time, A.IsTerminal (path time).1 →
        path (time + 1) = path time := by
  filter_upwards
    [pathLaw_ae_legalTransition
      policy current supplied legalTransition]
    with path hlegal
  intro time hterminal
  rcases hlegal time with hstay | hstep
  · exact hstay.2
  · exact False.elim (hstep.1 hterminal)

/-- The coordinate process on the infinite history-path space. -/
def historyCoordinateProcess
    (time : ℕ) (path : ℕ → A.HistoryFrom start) :
    A.HistoryFrom start :=
  path time

/-- The set of terminal complete histories. -/
def terminalHistorySet : Set (A.HistoryFrom start) :=
  {history | A.IsTerminal history.1}

/-- Search the prefix through `fuel` for the first terminal event time.

`none` means that the bounded search found no terminal coordinate; it does not
assert that the infinite path never terminates. -/
def terminalTime
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (path : ℕ → A.HistoryFrom start)
    (fuel : ℕ) : Option ℕ :=
  (List.range (fuel + 1)).find?
    (fun time => decide (A.IsTerminal (path time).1))

/-- Almost-sure eventual termination of a supplied path law. -/
def AETerminates
    [MeasurableSpace (A.HistoryFrom start)]
    (_policy : A.StochasticHistoryPolicy start)
    (_current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start)) : Prop :=
  ∀ᵐ path ∂(supplied : Measure (ℕ → A.HistoryFrom start)),
    ∃ time, A.IsTerminal (path time).1

/-- Once a terminal history is reached on an absorbing path, every later
coordinate is the same terminal history. -/
theorem path_eq_of_terminal_of_le
    (path : ℕ → A.HistoryFrom start)
    (habsorbing :
      ∀ time, A.IsTerminal (path time).1 →
        path (time + 1) = path time)
    {first later : ℕ}
    (hterminal : A.IsTerminal (path first).1)
    (hle : first ≤ later) :
    path later = path first ∧ A.IsTerminal (path later).1 := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction steps with
  | zero => simpa
  | succ steps ih =>
      have ih' := ih (Nat.le_add_right first steps)
      have hstep :
          path (first + steps + 1) =
            path (first + steps) :=
        habsorbing (first + steps) ih'.2
      constructor
      · rw [Nat.add_succ]
        exact hstep.trans ih'.1
      · rw [Nat.add_succ, hstep]
        exact ih'.2

/-- Bounded stopped payoff. Horizon exhaustion remains the explicit value
`0`; this is a finite observable, not an infinite terminal-payoff selector. -/
def stoppedPayoff
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (payoff : A.HistoryFrom start → ℝ)
    (time : ℕ) (path : ℕ → A.HistoryFrom start) : ℝ :=
  if A.IsTerminal (path time).1 then payoff (path time) else 0

/-- Bounded-search terminal payoff. Missing termination evidence is reported
as `none` rather than being assigned an invented payoff. -/
def terminalPayoff
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (payoff : A.HistoryFrom start → ℝ)
    (path : ℕ → A.HistoryFrom start)
    (fuel : ℕ) : Option ℝ :=
  (terminalTime path fuel).map fun time => payoff (path time)

/-- Paths unfinished at event time `time`. -/
def unfinishedAt (time : ℕ) :
    Set (ℕ → A.HistoryFrom start) :=
  {path | ¬ A.IsTerminal (path time).1}

/-- Exact executable mass of histories still nonterminal at a bounded event
time. This compatibility spelling unfolds through `pathMarginal`; pure finite
truncation code uses `Arena.unfinishedMass`. -/
def noneMass
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (time : ℕ) : ℚ≥0 :=
  (pathMarginal policy current time).eventMass
    (fun history => decide (¬ A.IsTerminal history.1))

/-- The unfinished-path cylinder is measurable whenever singleton histories
are measurable. -/
theorem unfinishedAt_measurableSet
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (time : ℕ) :
    MeasurableSet
      (unfinishedAt (A := A) (start := start) time) :=
  ((Set.to_countable
    (terminalHistorySet (A := A) (start := start))).measurableSet.preimage
      (measurable_pi_apply time)).compl

/-- Project the supplied complete path probability measure without rebuilding
it from finite marginals. -/
def pathProbabilityMeasure
    [MeasurableSpace (A.HistoryFrom start)]
    (_policy : A.StochasticHistoryPolicy start)
    (_current : A.HistoryFrom start)
    (supplied : ProbabilityMeasure (ℕ → A.HistoryFrom start)) :
    ProbabilityMeasure (ℕ → A.HistoryFrom start) :=
  supplied

/-- Executable finite law of the stopped payoff at event time `time`. -/
def stoppedPayoffLaw
    [(state : A.State) → Decidable (A.IsTerminal state)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (payoff : A.HistoryFrom start → ℝ)
    (time : ℕ) : FiniteLaw ℝ :=
  (pathMarginal policy current time).map fun history =>
    if A.IsTerminal history.1 then payoff history else 0

/-- Project a caller-supplied terminal-payoff probability law.

The caller owns the analytic pushforward and its relationship to the supplied
complete path law; no measure-valued map is synthesized here. -/
def terminalPayoffLaw
    (_policy : A.StochasticHistoryPolicy start)
    (_current : A.HistoryFrom start)
    (_payoff : A.HistoryFrom start → ℝ)
    (supplied : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  supplied

end Arena
