/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism
import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation

Probabilistic weak/stuttering simulation from a stochastic kernel Arena to a
deterministic serialized Arena.

One source macro action is matched by a positive amount of target execution
under a normalized history policy.  The source successor law and target
endpoint law must admit a relation-supported coupling.  A customizable
`PolicyAdmissible` predicate can require, for example, that target chance nodes
use the chance kernels specified by an `ObservedChanceGame`.

The support Arena exposes a realized stochastic transition as an action paired
with a positive-probability successor.  The main theorem proves that every
probabilistic weak simulation induces a progressing ordinary `Arena`
weak/stuttering simulation from this support Arena to the target history
unfolding.

## Main definitions

* `KernelArena.supportArena` — the Arena of positive-probability realized
  kernel transitions.
* `KernelArena.ProbabilisticWeakSimulation` — finite target execution plus
  exact successor-law coupling.
* `KernelArena.executionKernelArena` — packages finite serialized executions
  as macro transitions of a stochastic arena.

## Main results

* `ProbabilisticWeakSimulation.toKernelSimulation` — expose a weak serializer
  as an ordinary coupling-based kernel simulation at macro boundaries.
* `ProbabilisticWeakSimulation.toSupportWeakSimulation` — forget probabilities
  and obtain an ordinary weak simulation.
* `toSupportWeakSimulation_progressing` — every matched macro step uses at
  least one target transition.
-/

namespace KernelArena

/-- The deterministic support Arena of a stochastic kernel Arena.

An action records a macro action together with a successor in the support of
its transition law.  This is an operational path view only; it does not turn a
chance outcome into a strategic choice. -/
def supportArena (A : KernelArena) : Arena where
  State := A.State
  Action := fun state =>
    Σ action : A.Action state,
      { nextState : A.State //
        (A.next state action).HasPositiveAtom nextState }
  next := fun _ realized => realized.2.1

/-- The support Arena is terminal exactly when the kernel Arena has no macro
action. Finite-law positive-atom nonemptiness is essential in the forward
direction. -/
theorem supportArena_isTerminal_iff (A : KernelArena) (state : A.State) :
    A.supportArena.IsTerminal state ↔ IsEmpty (A.Action state) := by
  constructor
  · intro hterminal
    refine ⟨fun action => ?_⟩
    obtain ⟨nextState, hnextState⟩ :=
      (A.next state action).exists_hasPositiveAtom
    exact hterminal.false ⟨action, ⟨nextState, hnextState⟩⟩
  · intro hterminal
    exact ⟨fun realized => hterminal.false realized.1⟩

/-- A coupling-based weak simulation of a kernel Arena by finite execution in
a deterministic target Arena.

`PolicyAdmissible` is kept abstract so callers can impose model-specific
conditions, especially exact use of target chance kernels. -/
structure ProbabilisticWeakSimulation
    (A : KernelArena) (B : Arena) (start : B.State)
    [(state : B.State) → Decidable (B.IsTerminal state)]
    (PolicyAdmissible : B.StochasticHistoryPolicy start → Prop) where
  /-- Relation between source macro states and target complete histories. -/
  Rel : A.State → B.HistoryFrom start → Prop
  /-- Every macro action is implemented by a positive-fuel admissible target
  execution whose endpoint law is coupled to the source successor law. -/
  match_action :
    ∀ {source : A.State} {target : B.HistoryFrom start},
      Rel source target →
      ∀ action : A.Action source,
        PSigma fun policy : B.StochasticHistoryPolicy start =>
          PSigma fun fuel : ℕ =>
            PSigma fun _hpositive : 0 < fuel =>
              PSigma fun _hadmissible : PolicyAdmissible policy =>
                FiniteLaw.RelCoupling Rel
                  (A.next source action)
                  (B.stochasticHistoryLawFrom policy target fuel)
  /-- Source and target macro states terminate simultaneously. -/
  terminal_iff :
    ∀ {source : A.State} {target : B.HistoryFrom start},
      Rel source target →
        (IsEmpty (A.Action source) ↔ B.IsTerminal target.1)

/-- A positive-length admissible serialized macro execution. -/
structure ExecutionAction
    (B : Arena) (start : B.State)
    [(state : B.State) → Decidable (B.IsTerminal state)]
    (PolicyAdmissible : B.StochasticHistoryPolicy start → Prop)
    (history : B.HistoryFrom start) where
  /-- Macro executions may start only at a nonterminal target boundary. -/
  nonterminal : ¬ B.IsTerminal history.1
  /-- Policy controlling the serialized micro steps. -/
  policy : B.StochasticHistoryPolicy start
  /-- Number of serialized micro steps in the macro execution. -/
  fuel : ℕ
  /-- A source macro step must make positive target progress. -/
  positive : 0 < fuel
  /-- Model-specific admissibility, such as exact chance consistency. -/
  admissible : PolicyAdmissible policy

/-- The macro-boundary stochastic arena generated by serialized executions.

Its actions are positive-length admissible policies together with their
horizon, and its transition kernel is the exact endpoint law of that finite
execution. -/
def executionKernelArena
    (B : Arena) (start : B.State)
    [(state : B.State) → Decidable (B.IsTerminal state)]
    (PolicyAdmissible : B.StochasticHistoryPolicy start → Prop) :
  KernelArena where
  State := B.HistoryFrom start
  Action := fun history =>
    ExecutionAction B start PolicyAdmissible history
  next := fun history execution =>
    B.stochasticHistoryLawFrom execution.policy history execution.fuel

namespace ProbabilisticWeakSimulation

variable {A : KernelArena} {B : Arena} {start : B.State}
  [(state : B.State) → Decidable (B.IsTerminal state)]
  {PolicyAdmissible : B.StochasticHistoryPolicy start → Prop}

/-- Regard a probabilistic weak serializer as an ordinary kernel simulation
between macro-boundary arenas.

This theorem retains the exact finite-law coupling.  Only the internal serialized
micro steps are hidden inside an `ExecutionAction`; no probability weights
are forgotten. -/
def toKernelSimulation
    (R : ProbabilisticWeakSimulation A B start PolicyAdmissible) :
    A.Simulation (executionKernelArena B start PolicyAdmissible) where
  Rel := R.Rel
  match_action := by
    intro source target hrelated action
    obtain
      ⟨policy, fuel, hpositive, hadmissible, hcoupling⟩ :=
      R.match_action hrelated action
    have hsourceNonterminal :
        ¬ IsEmpty (A.Action source) := by
      intro hterminal
      exact hterminal.false action
    have htargetNonterminal :
        ¬ B.IsTerminal target.1 := by
      intro hterminal
      exact
        hsourceNonterminal
          ((R.terminal_iff hrelated).mpr hterminal)
    exact
      ⟨⟨htargetNonterminal, policy, fuel, hpositive, hadmissible⟩,
        hcoupling⟩

/-- The induced macro-boundary kernel simulation preserves terminality.

The target action type is empty exactly at related serialized terminal
histories. -/
theorem toKernelSimulation_terminal_iff
    (R : ProbabilisticWeakSimulation A B start PolicyAdmissible)
    {source : A.State} {target : B.HistoryFrom start}
    (hrelated : R.Rel source target) :
    IsEmpty (A.Action source) ↔
      IsEmpty
        ((executionKernelArena B start PolicyAdmissible).Action target) := by
  constructor
  · intro hsource
    refine ⟨fun execution => ?_⟩
    exact execution.nonterminal ((R.terminal_iff hrelated).mp hsource)
  · intro htarget
    refine ⟨fun action => ?_⟩
    obtain
      ⟨policy, fuel, hpositive, hadmissible, _⟩ :=
      R.match_action hrelated action
    have hsourceNonterminal :
        ¬ IsEmpty (A.Action source) := by
      intro hterminal
      exact hterminal.false action
    have htargetNonterminal :
        ¬ B.IsTerminal target.1 := by
      intro hterminal
      exact
        hsourceNonterminal
          ((R.terminal_iff hrelated).mpr hterminal)
    exact
      htarget.false
        ⟨htargetNonterminal, policy, fuel, hpositive, hadmissible⟩

/-- Forget probability weights and obtain a weak simulation between realized
support paths and the target history unfolding. -/
def toSupportWeakSimulation
    (R : ProbabilisticWeakSimulation A B start PolicyAdmissible) :
    A.supportArena.WeakSimulation (B.unfoldFrom start) where
  Rel := R.Rel
  match_step := by
    intro source target hrelated realized
    obtain ⟨sourceAction, nextSource, hnextSource⟩ := realized
    obtain
      ⟨policy, fuel, hfuel, _, coupling⟩ :=
      R.match_action hrelated sourceAction
    obtain ⟨coupledTarget, htargetPositive, hcoupled⟩ :=
      coupling.exists_right_of_hasPositiveAtom_left hnextSource
    have hsourceNonterminal : ¬ IsEmpty (A.Action source) := by
      intro hterminal
      exact hterminal.false sourceAction
    have htargetNonterminal : ¬ B.IsTerminal target.1 := by
      intro hterminal
      exact hsourceNonterminal ((R.terminal_iff hrelated).mpr hterminal)
    obtain ⟨suffix, _, hsuffix⟩ :=
      B.exists_positive_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
        policy target coupledTarget fuel hfuel htargetNonterminal
          htargetPositive
    have htargetEq :
        (⟨coupledTarget.1, target.2.append suffix⟩ :
          B.HistoryFrom start) = coupledTarget := by
      apply Sigma.ext (by rfl)
      exact heq_of_eq hsuffix.symm
    refine
      ⟨⟨coupledTarget.1, target.2.append suffix⟩,
        ⟨target.2.liftAppend suffix⟩, ?_⟩
    rw [htargetEq]
    exact hcoupled
  terminal_iff := by
    intro source target hrelated
    calc
      A.supportArena.IsTerminal source ↔
          IsEmpty (A.Action source) :=
        A.supportArena_isTerminal_iff source
      _ ↔ B.IsTerminal target.1 := R.terminal_iff hrelated
      _ ↔ (B.unfoldFrom start).IsTerminal target := Iff.rfl

/-- The support-level weak simulation induced by a probabilistic weak
simulation is progressing. -/
theorem toSupportWeakSimulation_progressing
    (R : ProbabilisticWeakSimulation A B start PolicyAdmissible) :
    R.toSupportWeakSimulation.Progressing := by
  intro source target hrelated realized
  obtain ⟨sourceAction, nextSource, hnextSource⟩ := realized
  obtain
    ⟨policy, fuel, hfuel, _, coupling⟩ :=
    R.match_action hrelated sourceAction
  obtain ⟨coupledTarget, htargetPositive, hcoupled⟩ :=
    coupling.exists_right_of_hasPositiveAtom_left hnextSource
  have hsourceNonterminal : ¬ IsEmpty (A.Action source) := by
    intro hterminal
    exact hterminal.false sourceAction
  have htargetNonterminal : ¬ B.IsTerminal target.1 := by
    intro hterminal
    exact hsourceNonterminal ((R.terminal_iff hrelated).mpr hterminal)
  obtain ⟨suffix, hsuffixPositive, hsuffix⟩ :=
    B.exists_positive_suffix_of_hasPositiveAtom_stochasticHistoryLawFrom
      policy target coupledTarget fuel hfuel htargetNonterminal
        htargetPositive
  have htargetEq :
      (⟨coupledTarget.1, target.2.append suffix⟩ :
        B.HistoryFrom start) = coupledTarget := by
    apply Sigma.ext (by rfl)
    exact heq_of_eq hsuffix.symm
  refine
    ⟨⟨coupledTarget.1, target.2.append suffix⟩,
      target.2.liftAppend suffix, ?_, ?_⟩
  · have hlength :
        (target.2.liftAppend suffix).length = suffix.length :=
      Arena.History.length_liftAppend (A := B) target.2 suffix
    exact hlength.symm ▸ hsuffixPositive
  · rw [htargetEq]
    exact hcoupled

end ProbabilisticWeakSimulation

end KernelArena
