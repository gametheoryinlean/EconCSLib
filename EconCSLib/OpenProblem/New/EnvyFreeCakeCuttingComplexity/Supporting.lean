/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.EnvyFreeCakeCuttingComplexity.Problem

/-!
# EnvyFreeCakeCuttingComplexity: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
Total transcript/state procedures may have inconsistent infinite branches. Termination
is required only along every valid reply sequence for a fixed instance.
-/

open scoped unitInterval

namespace EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

open SocialChoice.FairDivision.Divisible

theorem RWQuery.exists_validAnswer {N : Type*} (q : RWQuery N)
    (problem : CakeInstance N) : ∃ a, q.IsValidAnswer problem a := by
  classical
  cases q with
  | cut i left amount =>
      by_cases h : ∃ right, IsCutPoint problem i left amount right
      · obtain ⟨right, hright⟩ := h
        exact ⟨some right, hright⟩
      · exact ⟨none, h⟩
  | eval i left right ordered =>
      exact ⟨(problem.measure i (Set.Icc left right)).toReal, rfl⟩

/-- A deterministic total next-decision function, fixed before the valuation profile. A
query step charges one call and has one successor for every reply. -/
structure RWProcedure (N : Type*) [Fintype N] (State : Type*) where
  initial : State
  step : State → Sum (Allocation N I) (Σ q : RWQuery N, q.Answer → State)

inductive ProcedureExecution {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) :
    State → Allocation N I → ℕ → Prop
  | output {state allocation} (step : P.step state = .inl allocation) :
      ProcedureExecution P problem state allocation 0
  | query {state} {q : RWQuery N} {next : q.Answer → State}
      {answer allocation queries}
      (step : P.step state = .inr ⟨q, next⟩)
      (valid : q.IsValidAnswer problem answer)
      (rest : ProcedureExecution P problem (next answer) allocation queries) :
      ProcedureExecution P problem state allocation (queries + 1)

/-- Successor comes first, as required by accessibility. Every valid cut reply is
retained; the relation does not select a tie-breaking policy. -/
def RWProcedure.ValidStep {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) (nextState state : State) : Prop :=
  ∃ (q : RWQuery N) (next : q.Answer → State) (answer : q.Answer),
    P.step state = .inr ⟨q, next⟩ ∧ q.IsValidAnswer problem answer ∧
      next answer = nextState

def RWProcedure.SolvesInstance {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) : Prop :=
  Acc (P.ValidStep problem) P.initial ∧
    ∀ allocation queries, ProcedureExecution P problem P.initial allocation queries →
      IsValidOutput problem allocation

def RWProcedure.Solves {N State : Type*} [Fintype N]
    (P : RWProcedure N State) : Prop := ∀ problem, P.SolvesInstance problem

theorem RWProcedure.execution_exists {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) {state : State}
    (hAcc : Acc (P.ValidStep problem) state) :
    ∃ allocation queries, ProcedureExecution P problem state allocation queries := by
  induction hAcc with
  | intro state _ ih =>
      cases hstep : P.step state with
      | inl allocation => exact ⟨allocation, 0, .output hstep⟩
      | inr decision =>
          rcases decision with ⟨q, next⟩
          obtain ⟨answer, hvalid⟩ := q.exists_validAnswer problem
          obtain ⟨allocation, queries, hexec⟩ :=
            ih (next answer) ⟨q, next, answer, hstep, hvalid, rfl⟩
          exact ⟨allocation, queries + 1, .query hstep hvalid hexec⟩

/-- Fuel only truncates query steps. An already available output costs zero. The arbitrary
empty fallback is proved unreachable on valid bounded executions. -/
def RWProcedure.truncate {N State : Type*} [Fintype N]
    (P : RWProcedure N State) : ℕ → State → RWProtocol N
  | fuel, state =>
      match P.step state with
      | .inl allocation => .output allocation
      | .inr ⟨q, next⟩ =>
          match fuel with
          | 0 => .output (fun _ => ∅)
          | fuel + 1 => .query q (fun answer => P.truncate fuel (next answer))

theorem ProcedureExecution.truncate {N State : Type*} [Fintype N]
    {P : RWProcedure N State} {problem : CakeInstance N}
    {state allocation queries} (h : ProcedureExecution P problem state allocation queries)
    {fuel : ℕ} (hbound : queries ≤ fuel) :
    RWExecution problem (P.truncate fuel state) allocation queries := by
  induction h generalizing fuel with
  | output hstep =>
      rw [RWProcedure.truncate, hstep]
      exact .output _
  | query hstep hvalid rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [RWProcedure.truncate, hstep]
          exact .query hvalid (ih (by omega))

theorem RWProcedure.truncate_reverse {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) (fuel : ℕ)
    (state : State) (hAcc : Acc (P.ValidStep problem) state)
    (hbound : ∀ allocation queries,
      ProcedureExecution P problem state allocation queries → queries ≤ fuel) :
    ∀ allocation queries, RWExecution problem (P.truncate fuel state) allocation queries →
      ProcedureExecution P problem state allocation queries := by
  induction fuel generalizing state with
  | zero =>
      cases hstep : P.step state with
      | inl result =>
          intro allocation queries h
          rw [truncate, hstep] at h
          cases h
          exact .output hstep
      | inr decision =>
          obtain ⟨allocation, queries, hexec⟩ := P.execution_exists problem hAcc
          have hz := hbound allocation queries hexec
          cases hexec with
          | output hout => simp [hstep] at hout
          | query _ _ _ => omega
  | succ fuel ih =>
      cases hstep : P.step state with
      | inl result =>
          intro allocation queries h
          rw [truncate, hstep] at h
          cases h
          exact .output hstep
      | inr decision =>
          rcases decision with ⟨q, next⟩
          intro allocation queries h
          rw [truncate, hstep] at h
          cases h with
          | query hvalid hrest =>
              apply ProcedureExecution.query hstep hvalid
              apply ih _ (hAcc.inv ⟨q, next, _, hstep, hvalid, rfl⟩) _ _ _ hrest
              intro result count hexec
              have hb := hbound result (count + 1) (.query hstep hvalid hexec)
              omega

/-- The bounded-depth tree preserves every legal terminal outcome and count; this requires
a common bound. -/
theorem RWProcedure.truncate_execution_iff {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (problem : CakeInstance N) (fuel : ℕ)
    (state : State) (hAcc : Acc (P.ValidStep problem) state)
    (hbound : ∀ allocation queries,
      ProcedureExecution P problem state allocation queries → queries ≤ fuel)
    (allocation : Allocation N I) (queries : ℕ) :
    RWExecution problem (P.truncate fuel state) allocation queries ↔
      ProcedureExecution P problem state allocation queries := by
  exact ⟨P.truncate_reverse problem fuel state hAcc hbound allocation queries,
    fun h => h.truncate (hbound allocation queries h)⟩

/-- The existing tree correctness recursion is equivalent to correctness of all its valid
terminal executions, since every query has a legal reply. -/
theorem RWProtocol.solvesInstance_iff_all_outputs {N : Type*} [Fintype N]
    (T : RWProtocol N) (problem : CakeInstance N) :
    T.SolvesInstance problem ↔
      ∀ allocation queries, RWExecution problem T allocation queries →
        IsValidOutput problem allocation := by
  induction T with
  | output result =>
      constructor
      · intro h allocation queries hexec
        cases hexec
        exact h
      · intro h
        exact h result 0 (.output result)
  | query q next ih =>
      constructor
      · intro h allocation queries hexec
        cases hexec with
        | query hvalid hrest =>
            exact (ih _).mp (h.2 _ hvalid) _ _ hrest
      · intro h
        refine ⟨q.exists_validAnswer problem, ?_⟩
        intro answer hvalid
        apply (ih answer).mpr
        intro allocation queries hexec
        exact h allocation (queries + 1) (.query hvalid hexec)

/-- A uniform query cap converts an all-replies terminating safe procedure into an actual
existing tree, without changing any valid outcome or query count. -/
theorem RWProcedure.truncate_solves {N State : Type*} [Fintype N]
    (P : RWProcedure N State) (hP : P.Solves) (fuel : ℕ)
    (hbound : ∀ problem allocation queries,
      ProcedureExecution P problem P.initial allocation queries → queries ≤ fuel) :
    (P.truncate fuel P.initial).Solves := by
  intro problem
  apply (RWProtocol.solvesInstance_iff_all_outputs _ problem).mpr
  intro allocation queries hexec
  exact (hP problem).2 allocation queries
    (P.truncate_reverse problem fuel P.initial (hP problem).1 (hbound problem)
      allocation queries hexec)

/-- Existing finite lower-bound predicates apply even when a correct procedure has no
uniform upper bound. If no hard execution existed, a finite truncation would
contradict the tree lower bound. -/
theorem IsQueryLowerBound.for_procedure {lower : ℕ → ℕ}
    (hLower : IsQueryLowerBound lower) (n : ℕ) (hn : 2 ≤ n)
    {State : Type*} (P : RWProcedure (Fin n) State) (hP : P.Solves) :
    ∃ problem allocation queries,
      ProcedureExecution P problem P.initial allocation queries ∧ lower n ≤ queries := by
  classical
  by_contra hNo
  have hbound : ∀ problem allocation queries,
      ProcedureExecution P problem P.initial allocation queries → queries ≤ lower n := by
    intro problem allocation queries hexec
    by_contra hgt
    apply hNo
    exact ⟨problem, allocation, queries, hexec, by omega⟩
  obtain ⟨problem, allocation, queries, hexec, hlarge⟩ :=
    hLower n hn (P.truncate (lower n) P.initial) (P.truncate_solves hP _ hbound)
  exact hNo ⟨problem, allocation, queries,
    P.truncate_reverse problem (lower n) P.initial (hP problem).1 (hbound problem)
      allocation queries hexec, hlarge⟩

end EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

end


section

/-!
Existing well-founded trees satisfy the procedure termination contract. The embedding
preserves every valid terminal allocation and exact query count.
-/

open scoped unitInterval

namespace EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

open SocialChoice.FairDivision.Divisible

def RWProtocol.asProcedure {N : Type*} [Fintype N] (T : RWProtocol N) :
    RWProcedure N (RWProtocol N) where
  initial := T
  step := fun state => match state with
    | .output allocation => .inl allocation
    | .query q next => .inr ⟨q, next⟩

theorem RWProtocol.asProcedure_accessible {N : Type*} [Fintype N]
    (T : RWProtocol N) (problem : CakeInstance N) (state : RWProtocol N) :
    Acc (T.asProcedure.ValidStep problem) state := by
  induction state with
  | output allocation =>
      constructor
      intro child hchild
      obtain ⟨q, next, answer, hstep, _, _⟩ := hchild
      cases hstep
  | query q next ih =>
      constructor
      intro child hchild
      obtain ⟨q', next', answer, hstep, _, rfl⟩ := hchild
      change (Sum.inr ⟨q, next⟩ : Sum (Allocation N I)
        (Σ q : RWQuery N, q.Answer → RWProtocol N)) = .inr ⟨q', next'⟩ at hstep
      cases Sum.inr.inj hstep
      exact ih answer

theorem RWProtocol.asProcedure_execution_iff {N : Type*} [Fintype N]
    (T : RWProtocol N) (problem : CakeInstance N) (state : RWProtocol N)
    (allocation : Allocation N I) (queries : ℕ) :
    ProcedureExecution T.asProcedure problem state allocation queries ↔
      RWExecution problem state allocation queries := by
  constructor
  · intro h
    induction h with
    | @output state allocation hstep =>
        cases state with
        | output result =>
            cases hstep
            exact .output _
        | query q next => cases hstep
    | @query state q next answer allocation queries hstep hvalid rest ih =>
        cases state with
        | output result => cases hstep
        | query q' next' =>
            change (Sum.inr ⟨q', next'⟩ : Sum (Allocation N I)
              (Σ q : RWQuery N, q.Answer → RWProtocol N)) = .inr ⟨q, next⟩ at hstep
            cases Sum.inr.inj hstep
            exact .query hvalid ih
  · intro h
    induction h with
    | output result => exact .output rfl
    | query hvalid _ ih => exact .query rfl hvalid ih

theorem RWProtocol.asProcedure_solves_iff {N : Type*} [Fintype N]
    (T : RWProtocol N) : T.asProcedure.Solves ↔ T.Solves := by
  constructor
  · intro h problem
    apply (T.solvesInstance_iff_all_outputs problem).mpr
    intro allocation queries hexec
    exact (h problem).2 allocation queries
      ((T.asProcedure_execution_iff problem T allocation queries).mpr hexec)
  · intro h problem
    refine ⟨T.asProcedure_accessible problem T, ?_⟩
    intro allocation queries hexec
    exact (T.solvesInstance_iff_all_outputs problem).mp (h problem) allocation queries
      ((T.asProcedure_execution_iff problem T allocation queries).mp hexec)

/-- Uniform finite query upper bounds are unchanged by allowing total state procedures
that terminate only along instance-consistent reply sequences. -/
theorem isQueryUpperBound_iff_procedures (upper : ℕ → ℕ) :
    IsQueryUpperBound upper ↔
      ∃ (State : ℕ → Type) (procedures : ∀ n, RWProcedure (Fin n) (State n)),
        ∀ n, 2 ≤ n → (procedures n).Solves ∧
          ∀ problem allocation queries,
            ProcedureExecution (procedures n) problem (procedures n).initial
              allocation queries → queries ≤ upper n := by
  constructor
  · rintro ⟨trees, htrees⟩
    refine ⟨fun n => RWProtocol (Fin n), fun n => (trees n).asProcedure, ?_⟩
    intro n hn
    refine ⟨(trees n).asProcedure_solves_iff.mpr (htrees n hn).1, ?_⟩
    intro problem allocation queries hexec
    exact (htrees n hn).2 problem allocation queries
      (((trees n).asProcedure_execution_iff problem (trees n) allocation queries).mp hexec)
  · rintro ⟨State, procedures, hprocedures⟩
    refine ⟨fun n => (procedures n).truncate (upper n) (procedures n).initial, ?_⟩
    intro n hn
    obtain ⟨hsolves, hbound⟩ := hprocedures n hn
    refine ⟨(procedures n).truncate_solves hsolves (upper n) hbound, ?_⟩
    intro problem allocation queries hexec
    exact hbound problem allocation queries
      ((procedures n).truncate_reverse problem (upper n) (procedures n).initial
        (hsolves problem).1 (hbound problem) allocation queries hexec)


end EconCSLib.OpenProblem.New.EconCSBench.EnvyFreeCakeCuttingComplexity

end
