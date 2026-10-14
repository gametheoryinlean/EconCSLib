/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel
import EconCSLib.Math.Probability.FiniteLaw.Conditioning

/-!
# Exact finite conditional continuation

This module conditions an exact finite law on a decidable observation and
then continues every posterior atom with another exact finite law. Impossible
observations return `none`; no off-path posterior is selected. The generic
construction is specialized to complete Arena histories and to the state- and
action-recording prefix executors of `KernelArena`.

The retained posterior atom is the whole observation-time history or prefix.
Consequently continuations preserve action memory, route dependence, and the
absolute event clock. The joint law records both the observation-time value
and the final value, and its Bayes theorem is stated using semantic
`FiniteLaw.Equivalent` rather than equality of sparse atom lists.
-/

namespace FiniteConditionalContinuation

variable {α β γ : Type*} [DecidableEq β]

private theorem condition_some_iff (prior : FiniteLaw α)
    (observe : α → β) (value : β) :
    (∃ posterior, prior.conditionOnFiber observe value = some posterior) ↔
      prior.FiberPossible observe value := by
  rw [← Option.ne_none_iff_exists']
  simp [FiniteLaw.conditionOnFiber, FiniteLaw.FiberPossible]

private theorem expectRat_conditionOnFiber (prior : FiniteLaw α)
    (observe : α → β) (observed : β) (posterior : FiniteLaw α)
    (hposterior : prior.conditionOnFiber observe observed = some posterior)
    (payoff : α → ℚ) :
    posterior.expectRat payoff =
      prior.expectRat
          (fun sample => if observe sample = observed then payoff sample else 0) /
        (prior.eventMass
          (fun sample => decide (observe sample = observed)) : ℚ) := by
  let atoms := prior.atoms.map fun atom =>
    (atom.1, if observe atom.1 = observed then atom.2 else 0)
  have htotal : FiniteLaw.totalWeight atoms =
      prior.eventMass
        (fun sample => decide (observe sample = observed)) := by
    simp [atoms, FiniteLaw.totalWeight, FiniteLaw.eventMass,
      List.map_map, Function.comp_def]
  have hcondition : FiniteLaw.normalize? atoms = some posterior := by
    change FiniteLaw.normalize? (prior.atoms.map fun atom =>
      (atom.1, if decide (observe atom.1 = observed) then atom.2 else 0)) =
        some posterior at hposterior
    simpa [atoms] using hposterior
  unfold FiniteLaw.normalize? at hcondition
  split at hcondition
  · simp at hcondition
  · rename_i hnonzero
    have hp : FiniteLaw.normalize atoms hnonzero = posterior :=
      Option.some.inj hcondition
    rw [← hp]
    simp only [FiniteLaw.expectRat, FiniteLaw.normalize, List.map_map,
      Function.comp_def, htotal]
    dsimp only [atoms]
    simp only [List.map_map, Function.comp_def]
    generalize prior.eventMass
      (fun sample => decide (observe sample = observed)) = mass
    induction prior.atoms with
    | nil => simp
    | cons atom atoms ih =>
      simp only [List.map_cons, List.sum_cons, ih, add_div]
      congr 1
      split <;> simp [div_mul_eq_mul_div]

/-- Condition `prior` on an observed fiber and continue every posterior atom.
Zero-mass observations return `none`. -/
def law (prior : FiniteLaw α) (observe : α → β) (observed : β)
    (next : α → FiniteLaw γ) : Option (FiniteLaw γ) :=
  (prior.conditionOnFiber observe observed).map fun posterior =>
    posterior.bind next

/-- Exact rational payoff of a conditional continuation. `none` distinguishes
an impossible observation from a possible observation with zero payoff. -/
def expectRat (prior : FiniteLaw α) (observe : α → β) (observed : β)
    (next : α → FiniteLaw γ) (payoff : γ → ℚ) : Option ℚ :=
  (law prior observe observed next).map fun result => result.expectRat payoff

/-- The actual joint law retains both the observation-time atom and its
continued result. -/
def joint (prior : FiniteLaw α) (next : α → FiniteLaw γ) :
    FiniteLaw (α × γ) :=
  prior.bind fun sample => (next sample).map fun final => (sample, final)

private theorem joint_fst (prior : FiniteLaw α) (next : α → FiniteLaw γ) :
    ((joint prior next).map Prod.fst).Equivalent prior := by
  intro value
  change FiniteLaw.expectRat _ value = prior.expectRat value
  simp [joint, FiniteLaw.expectRat_map, FiniteLaw.expectRat_bind,
    Function.comp_def]

/-- Forgetting the recorded observation-time atom gives ordinary monadic
continuation. -/
theorem joint_snd (prior : FiniteLaw α) (next : α → FiniteLaw γ) :
    (joint prior next).map Prod.snd = prior.bind next := by
  rw [joint, FiniteLaw.map_bind]
  congr 1
  funext sample
  simpa only [FiniteLaw.map_comp, Function.comp_def] using
    FiniteLaw.map_id (next sample)

/-- Exactly zero observation mass is the only failure mode. -/
theorem law_eq_none_iff (prior : FiniteLaw α) (observe : α → β)
    (observed : β) (next : α → FiniteLaw γ) :
    law prior observe observed next = none ↔
      prior.eventMass
        (fun sample => decide (observe sample = observed)) = 0 := by
  simp [law, FiniteLaw.conditionOnFiber]

/-- Conditional expectation is absent exactly on a zero-mass observation. -/
theorem expectRat_eq_none_iff (prior : FiniteLaw α) (observe : α → β)
    (observed : β) (next : α → FiniteLaw γ) (payoff : γ → ℚ) :
    expectRat prior observe observed next payoff = none ↔
      prior.eventMass
        (fun sample => decide (observe sample = observed)) = 0 := by
  simp [expectRat, law, FiniteLaw.conditionOnFiber]

/-- Bayes-weighted continuation expectation over every compatible prior atom. -/
theorem expectRat_bayes (prior : FiniteLaw α) (observe : α → β)
    (observed : β) (next : α → FiniteLaw γ) (payoff : γ → ℚ)
    (hpossible : prior.FiberPossible observe observed) :
    expectRat prior observe observed next payoff = some
      (prior.expectRat (fun sample =>
          if observe sample = observed then
            (next sample).expectRat payoff
          else 0) /
        (prior.eventMass
          (fun sample => decide (observe sample = observed)) : ℚ)) := by
  obtain ⟨posterior, hposterior⟩ :=
    (condition_some_iff prior observe observed).mpr hpossible
  simp only [expectRat, law, hposterior, Option.map_some,
    FiniteLaw.expectRat_bind]
  rw [expectRat_conditionOnFiber prior observe observed posterior hposterior]

/-- Conditioning the first coordinate of the joint law agrees semantically
with retaining a posterior atom and then continuing it. -/
theorem condition_joint (prior : FiniteLaw α) (next : α → FiniteLaw γ)
    (observe : α → β) (observed : β) (posterior : FiniteLaw α)
    (hposterior : prior.conditionOnFiber observe observed = some posterior) :
    ∃ jointPosterior,
      (joint prior next).conditionOnFiber
          (fun pair => observe pair.1) observed = some jointPosterior ∧
      jointPosterior.Equivalent
        (posterior.bind fun sample =>
          (next sample).map fun final => (sample, final)) := by
  have hmass :
      (joint prior next).eventMass
          (fun pair => decide (observe pair.1 = observed)) =
        prior.eventMass
          (fun sample => decide (observe sample = observed)) := by
    simpa [FiniteLaw.eventMass_map, Function.comp_def] using
      (joint_fst prior next).eventMass
        (fun sample => decide (observe sample = observed))
  have hpossible :=
    (condition_some_iff prior observe observed).mp ⟨posterior, hposterior⟩
  have hjpossible :
      (joint prior next).FiberPossible
        (fun pair => observe pair.1) observed := by
    simpa only [FiniteLaw.FiberPossible, hmass] using hpossible
  obtain ⟨jointPosterior, hjoint⟩ :=
    (condition_some_iff (joint prior next) _ observed).mpr hjpossible
  refine ⟨jointPosterior, hjoint, ?_⟩
  intro payoff
  change jointPosterior.expectRat payoff = FiniteLaw.expectRat _ payoff
  rw [expectRat_conditionOnFiber (joint prior next) _ observed
      jointPosterior hjoint payoff,
    FiniteLaw.expectRat_bind posterior,
    expectRat_conditionOnFiber prior observe observed posterior hposterior,
    hmass]
  congr 1
  simp only [joint, FiniteLaw.expectRat_bind, FiniteLaw.expectRat_map,
    Function.comp_def]
  apply congrArg prior.expectRat
  funext sample
  by_cases h : observe sample = observed <;> simp [h]

end FiniteConditionalContinuation

namespace Arena.StochasticHistoryPolicy

variable {A : Arena} {start : A.State} {Observation : Type*}
variable [DecidableEq Observation]
variable [(state : A.State) → Decidable (A.IsTerminal state)]

/-- Condition a finite prior on complete Arena histories, then continue the
same policy for `steps` terminal-absorbing transitions. -/
def conditionalLawFrom (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start))
    (observe : A.HistoryFrom start → Observation) (observed : Observation)
    (steps : ℕ) : Option (FiniteLaw (A.HistoryFrom start)) :=
  FiniteConditionalContinuation.law prior observe observed fun history =>
    A.stochasticHistoryLawFrom policy history steps

/-- Exact rational payoff of a conditionally continued Arena history law. -/
def conditionalExpectedPayoffFrom (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start))
    (observe : A.HistoryFrom start → Observation) (observed : Observation)
    (steps : ℕ) (payoff : A.HistoryFrom start → ℚ) : Option ℚ :=
  FiniteConditionalContinuation.expectRat prior observe observed
    (fun history => A.stochasticHistoryLawFrom policy history steps) payoff

/-- The Arena conditional continuation fails exactly for an impossible
observation, independently of the continuation horizon. -/
theorem conditionalLawFrom_eq_none_iff
    (policy : A.StochasticHistoryPolicy start)
    (prior : FiniteLaw (A.HistoryFrom start))
    (observe : A.HistoryFrom start → Observation) (observed : Observation)
    (steps : ℕ) :
    policy.conditionalLawFrom prior observe observed steps = none ↔
      prior.eventMass
        (fun history => decide (observe history = observed)) = 0 :=
  FiniteConditionalContinuation.law_eq_none_iff _ _ _ _

end Arena.StochasticHistoryPolicy

namespace KernelArena.StateHistoryPolicy

variable {A : KernelArena} {Observation : Type*} [DecidableEq Observation]
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- Condition a finite prior on complete state prefixes and continue at the
same absolute clock. -/
def conditionalPrefixLawFrom (policy : A.StateHistoryPolicy) (start : ℕ)
    (prior : FiniteLaw (A.StatePrefix start))
    (observe : A.StatePrefix start → Observation) (observed : Observation)
    (steps : ℕ) : Option (FiniteLaw (A.StatePrefix (start + steps))) :=
  FiniteConditionalContinuation.law prior observe observed fun history =>
    policy.prefixLawFrom start history steps

end KernelArena.StateHistoryPolicy

namespace KernelArena.EventHistoryPolicy

variable {A : KernelArena} {Observation : Type*} [DecidableEq Observation]
variable [(state : A.State) → Decidable (IsEmpty (A.Action state))]

/-- Condition a finite prior on action-recording prefixes and continue at the
same absolute clock without discarding the retained actions. -/
def conditionalPrefixLawFrom (policy : A.EventHistoryPolicy) (start : ℕ)
    (prior : FiniteLaw (A.EventPrefix start))
    (observe : A.EventPrefix start → Observation) (observed : Observation)
    (steps : ℕ) : Option (FiniteLaw (A.EventPrefix (start + steps))) :=
  FiniteConditionalContinuation.law prior observe observed fun history =>
    policy.prefixLawFrom start history steps

end KernelArena.EventHistoryPolicy
