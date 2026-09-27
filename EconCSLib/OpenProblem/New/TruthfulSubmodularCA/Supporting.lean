/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.TruthfulSubmodularCA.Problem

/-!
# TruthfulSubmodularCA: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Universally truthful submodular mechanisms with oracle access

Uses native normalized monotone submodular real valuations. The reference interface
permits both value and demand queries [Assadi–Kesselheim–Singla, arXiv:2010.01420,
Section 2.1 and Theorem 2]; bundle-only remains a named variant. The following
definitions describe complete outputs. `PartialAllocation` extends the same interfaces
to partial realized outputs for the primary question. One query execution produces
allocation, payments, and both counts. Universal truthfulness is checked for every
seed and every fixed legal oracle family. This is a query-complexity model.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Allocation and payments are emitted together. DSIC does not silently include IR or
no-positive-transfers. -/
structure Outcome (n m : ℕ) where
  assignment : Assignment n m
  payment : Fin n → ℝ

/-- A well-founded adaptive query tree. Real branching and local computation are
unrestricted; no self-declared time counter is present. -/
inductive QueryTree (mode : OracleConvention) (n m : ℕ)
  | output (result : Outcome n m)
  | demand (bidder : Fin n) (price : Prices m)
      (next : Bundle m → QueryTree mode n m)
  | value (enabled : mode = .valueAndDemand) (bidder : Fin n) (bundle : Bundle m)
      (next : ℝ → QueryTree mode n m)

/-- One execution gives output and counts. Value replies use reported, not secretly
truthful, valuations. -/
def QueryTree.run {mode : OracleConvention} {n m : ℕ}
    (T : QueryTree mode n m) (oracle : DemandOracleFamily n m)
    (reports : Profile n m) : Outcome n m × QueryCount :=
  match T with
  | .output result => (result, ⟨0, 0⟩)
  | .demand i p next =>
      let result := (next (oracle.answer i (reports i) p)).run oracle reports
      (result.1, ⟨result.2.demand + 1, result.2.value⟩)
  | .value _ i S next =>
      let result := (next (bundleValue (reports i) S)).run oracle reports
      (result.1, ⟨result.2.demand, result.2.value + 1⟩)

/-- DSIC for a deterministic component, comparing the same true valuation and oracle
family before and after misreporting. -/
def QueryTree.IsDSIC {mode : OracleConvention} {n m : ℕ}
    (T : QueryTree mode n m) (oracle : DemandOracleFamily n m) : Prop :=
  ∀ (truth : Profile n m) (i : Fin n) (misreport : Valuation m),
    let honest := (T.run oracle truth).1
    let deviated := (T.run oracle (Function.update truth i misreport)).1
    bundleValue (truth i) (assignedBundle honest.assignment i) - honest.payment i ≥
      bundleValue (truth i) (assignedBundle deviated.assignment i) - deviated.payment i

/-- An arbitrary seed law chosen before profiles and oracle families; no finite-support or
dyadic restriction. -/
structure Mechanism (mode : OracleConvention) (n m : ℕ)
    (Seed : Type*) [MeasurableSpace Seed] where
  seedLaw : Measure Seed
  probability : IsProbabilityMeasure seedLaw
  program : Seed → QueryTree mode n m

/-- Truthfulness holds for every seed. -/
def Mechanism.IsUniversallyTruthful {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (M : Mechanism mode n m Seed) : Prop :=
  ∀ oracle : DemandOracleFamily n m, ∀ seed, (M.program seed).IsDSIC oracle

/-- Allocation events and payments are measurable. Finite allocation support bounds
welfare; payment integrability is unnecessary for per-seed DSIC. -/
def Mechanism.HasMeasurableOutcomes {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (M : Mechanism mode n m Seed) : Prop :=
  ∀ (oracle : DemandOracleFamily n m) (reports : Profile n m),
    (∀ A : Assignment n m,
      MeasurableSet {seed |
        ((M.program seed).run oracle reports).1.assignment = A}) ∧
    (∀ i : Fin n, Measurable (fun seed =>
      ((M.program seed).run oracle reports).1.payment i))

/-- Expected welfare for a fixed report profile and oracle family under the mechanism's
seed law. -/
def Mechanism.expectedWelfare {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (M : Mechanism mode n m Seed) (oracle : DemandOracleFamily n m)
    (reports : Profile n m) : ℝ :=
  ∫ seed, welfare reports ((M.program seed).run oracle reports).1.assignment ∂M.seedLaw

/-- Uniform worst-case total query bounds, counting both value and demand access when
enabled. -/
def Mechanism.UsesPolynomialQueries {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (M : Mechanism mode n m Seed) (coefficient exponent : ℕ) : Prop :=
  let Input := Seed × Profile n m
  UniformResourceBound coefficient exponent
    (fun _ : Input => n + m)
    (fun (input : Input) (oracle : DemandOracleFamily n m) =>
      ((M.program input.1).run oracle input.2).2.total)

end
end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

end


section

/-!
## Well-defined expected welfare

Measurable assignment fibers and the existing probability seed law imply integrable
welfare. No payment integrability or bound on reported values is required: a fixed
finite report profile has only finitely many assignments.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Native bundle-value nonnegativity implies allocation-welfare nonnegativity. -/
theorem welfare_nonnegative {n m : ℕ} (v : Profile n m) (A : Assignment n m) :
    0 ≤ welfare v A := by
  exact Finset.sum_nonneg fun i _ => (v i).nonnegative _

/-- Measurable finite allocation fibers suffice for welfare integrability. -/
theorem Mechanism.welfare_integrable {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed)
    (hM : M.HasMeasurableOutcomes) (oracle : DemandOracleFamily n m)
    (reports : Profile n m) :
    Integrable (fun seed =>
      welfare reports ((M.program seed).run oracle reports).1.assignment) M.seedLaw := by
  classical
  letI : IsProbabilityMeasure M.seedLaw := M.probability
  let allocation : Seed → Assignment n m := fun seed =>
    ((M.program seed).run oracle reports).1.assignment
  have hfiber (A : Assignment n m) : MeasurableSet {seed | allocation seed = A} :=
    (hM oracle reports).1 A
  have hsum : Integrable (fun seed => ∑ A : Assignment n m,
      {seed | allocation seed = A}.indicator (fun _ => welfare reports A) seed)
      M.seedLaw :=
    integrable_finsetSum Finset.univ fun A _ =>
      (integrable_const (welfare reports A)).indicator (hfiber A)
  convert hsum using 1
  funext seed
  simp [Set.indicator_apply, eq_comm, allocation]

/-- Expected welfare is nonnegative for every fixed report profile. -/
theorem Mechanism.expectedWelfare_nonnegative {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed)
    (oracle : DemandOracleFamily n m) (reports : Profile n m) :
    0 ≤ M.expectedWelfare oracle reports := by
  exact integral_nonneg fun seed => welfare_nonnegative reports _

end
end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

end


section

/-!
## Partial outputs for the reference truthful-auction question

The oracle, reporting, and counting interfaces are reused. Complete mechanisms embed
without changing their execution; no reverse incentive-preserving completion is
assumed. The optimal welfare benchmark may still be complete.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

open MeasureTheory
open scoped BigOperators
noncomputable section

def Assignment.toPartial {n m : ℕ} (A : Assignment n m) : PartialAssignment n m :=
  fun g => some (A g)

@[simp] theorem partialAssignedBundle_toPartial {n m : ℕ}
    (A : Assignment n m) (i : Fin n) :
    partialAssignedBundle A.toPartial i = assignedBundle A i := by
  simp [partialAssignedBundle, Assignment.toPartial, assignedBundle]

theorem Assignment.toPartial_injective {n m : ℕ} :
    Function.Injective (Assignment.toPartial (n := n) (m := m)) := by
  intro A B h
  funext g
  exact Option.some.inj (congrFun h g)

def Outcome.toPartial {n m : ℕ} (result : Outcome n m) : PartialOutcome n m :=
  ⟨result.assignment.toPartial, result.payment⟩

theorem partialWelfare_nonnegative {n m : ℕ} (v : Profile n m)
    (A : PartialAssignment n m) : 0 ≤ partialWelfare v A := by
  exact Finset.sum_nonneg fun i _ => (v i).nonnegative _

@[simp] theorem partialWelfare_toPartial {n m : ℕ}
    (v : Profile n m) (A : Assignment n m) : partialWelfare v A.toPartial = welfare v A := by
  simp [partialWelfare, welfare]

def QueryTree.toPartial {mode : OracleConvention} {n m : ℕ} :
    QueryTree mode n m → PartialQueryTree mode n m
  | .output result => .output result.toPartial
  | .demand i p next => .demand i p fun answer => (next answer).toPartial
  | .value enabled i S next => .value enabled i S fun answer => (next answer).toPartial

/-- The embedding preserves allocation, every payment, and both exact query counts. -/
theorem QueryTree.toPartial_run {mode : OracleConvention} {n m : ℕ}
    (T : QueryTree mode n m) (oracle : DemandOracleFamily n m) (reports : Profile n m) :
    T.toPartial.run oracle reports = ((T.run oracle reports).1.toPartial,
      (T.run oracle reports).2) := by
  induction T with
  | output result => rfl
  | demand i p next ih => simp [toPartial, PartialQueryTree.run, run, ih]
  | value enabled i S next ih => simp [toPartial, PartialQueryTree.run, run, ih]

theorem QueryTree.toPartial_isDSIC_iff {mode : OracleConvention} {n m : ℕ}
    (T : QueryTree mode n m) (oracle : DemandOracleFamily n m) :
    T.toPartial.IsDSIC oracle ↔ T.IsDSIC oracle := by
  simp only [PartialQueryTree.IsDSIC, IsDSIC, toPartial_run,
    Outcome.toPartial, partialAssignedBundle_toPartial]

def Mechanism.toPartial {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed) :
    PartialMechanism mode n m Seed :=
  ⟨M.seedLaw, M.probability, fun seed => (M.program seed).toPartial⟩

theorem Mechanism.toPartial_isUniversallyTruthful_iff {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed) :
    M.toPartial.IsUniversallyTruthful ↔ M.IsUniversallyTruthful := by
  simp only [PartialMechanism.IsUniversallyTruthful, IsUniversallyTruthful,
    toPartial, QueryTree.toPartial_isDSIC_iff]

theorem Mechanism.toPartial_expectedWelfare {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed)
    (oracle : DemandOracleFamily n m) (reports : Profile n m) :
    M.toPartial.expectedWelfare oracle reports = M.expectedWelfare oracle reports := by
  simp only [PartialMechanism.expectedWelfare, expectedWelfare, toPartial,
    QueryTree.toPartial_run, Outcome.toPartial, partialWelfare_toPartial]

theorem Mechanism.toPartial_usesPolynomialQueries_iff {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed)
    (coefficient exponent : ℕ) :
    M.toPartial.UsesPolynomialQueries coefficient exponent ↔
      M.UsesPolynomialQueries coefficient exponent := by
  simp only [PartialMechanism.UsesPolynomialQueries, UsesPolynomialQueries, toPartial,
    QueryTree.toPartial_run]

theorem Mechanism.toPartial_hasMeasurableOutcomes {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : Mechanism mode n m Seed)
    (hM : M.HasMeasurableOutcomes) : M.toPartial.HasMeasurableOutcomes := by
  classical
  intro oracle reports
  constructor
  · intro B
    by_cases hB : ∃ A : Assignment n m, A.toPartial = B
    · obtain ⟨A, rfl⟩ := hB
      simpa only [toPartial, QueryTree.toPartial_run, Outcome.toPartial,
        Assignment.toPartial_injective.eq_iff] using (hM oracle reports).1 A
    · have hEmpty : {seed | ((M.toPartial.program seed).run oracle reports).1.assignment = B}
          = ∅ := by
        ext seed
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hB ⟨((M.program seed).run oracle reports).1.assignment,
          by simpa only [toPartial, QueryTree.toPartial_run, Outcome.toPartial] using h⟩
      rw [hEmpty]
      exact MeasurableSet.empty
  · intro i
    simpa only [toPartial, QueryTree.toPartial_run, Outcome.toPartial]
      using (hM oracle reports).2 i

/-- Finite partial-assignment fibers make welfare integrable, even without any uniform
bound on the possible reported valuations. -/
theorem PartialMechanism.welfare_integrable {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : PartialMechanism mode n m Seed)
    (hM : M.HasMeasurableOutcomes) (oracle : DemandOracleFamily n m)
    (reports : Profile n m) :
    Integrable (fun seed =>
      partialWelfare reports ((M.program seed).run oracle reports).1.assignment) M.seedLaw := by
  classical
  letI : IsProbabilityMeasure M.seedLaw := M.probability
  let allocation : Seed → PartialAssignment n m := fun seed =>
    ((M.program seed).run oracle reports).1.assignment
  have hfiber (A : PartialAssignment n m) : MeasurableSet {seed | allocation seed = A} :=
    (hM oracle reports).1 A
  have hsum : Integrable (fun seed => ∑ A : PartialAssignment n m,
      {seed | allocation seed = A}.indicator (fun _ => partialWelfare reports A) seed)
      M.seedLaw :=
    integrable_finsetSum Finset.univ fun A _ =>
      (integrable_const (partialWelfare reports A)).indicator (hfiber A)
  convert hsum using 1
  funext seed
  simp [Set.indicator_apply, eq_comm, allocation]

/-- This is allocation completion only. -/
def PartialAssignment.complete {n m : ℕ} (A : PartialAssignment n m)
    (default : Fin n) : Assignment n m := fun g => (A g).getD default

theorem partialAssignedBundle_subset_complete {n m : ℕ} (A : PartialAssignment n m)
    (default i : Fin n) :
    partialAssignedBundle A i ⊆ assignedBundle (A.complete default) i := by
  intro g hg
  simp only [partialAssignedBundle, Finset.mem_filter, Finset.mem_univ, true_and] at hg
  simp [assignedBundle, PartialAssignment.complete, hg]

/-- Monotonicity lets the welfare benchmark use complete partitions even when mechanism
outputs are partial. This says nothing about preserving incentives. -/
theorem partialWelfare_le_complete {n m : ℕ} (reports : Profile n m)
    (A : PartialAssignment n m) (default : Fin n) :
    partialWelfare reports A ≤ welfare reports (A.complete default) := by
  apply Finset.sum_le_sum
  intro i _
  exact (reports i).monotone _ _ (partialAssignedBundle_subset_complete A default i)

/-- Complete and partial allocation benchmarks are equivalent; this is a statement about
optimal welfare. -/
theorem forall_partialWelfare_le_iff {n m : ℕ} (hn : 0 < n)
    (reports : Profile n m) (bound : ℝ) :
    (∀ A : PartialAssignment n m, partialWelfare reports A ≤ bound) ↔
      (∀ A : Assignment n m, welfare reports A ≤ bound) := by
  constructor
  · intro h A
    simpa only [partialWelfare_toPartial] using h A.toPartial
  · intro h A
    exact (partialWelfare_le_complete reports A ⟨0, hn⟩).trans (h _)

end
end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

end


section

/-!
## The O(log log m) universally truthful query target

The main question uses both value and demand access as in the reference; the literal
bundle-only reading is named separately. Outputs may be partial, while the welfare
benchmark is complete. Truthfulness is per seed for all legal reporting oracles. Only
query complexity is bounded. No polynomial running-time claim or free
truthfulness-preserving completion of a partial allocation is inferred.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

open MeasureTheory

noncomputable section

/-- The stronger complete-output variant. Approximation and query constants precede
dimensions and valuations; the cutoff keeps log(log m) positive. -/
def QueryConventionLogLogStatement (mode : OracleConvention) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ cutoff : ℕ, 3 ≤ cutoff ∧
      ∃ coefficient exponent : ℕ,
        ∀ n m : ℕ, 0 < n →
          ∃ (Seed : Type) (mSeed : MeasurableSpace Seed),
            letI : MeasurableSpace Seed := mSeed
            ∃ mechanism : Mechanism mode n m Seed,
              mechanism.IsUniversallyTruthful ∧
              mechanism.HasMeasurableOutcomes ∧
              mechanism.UsesPolynomialQueries coefficient exponent ∧
              (cutoff ≤ m →
                ∀ (oracle : DemandOracleFamily n m) (reports : Profile n m)
                  (alternative : Assignment n m),
                  welfare reports alternative ≤
                    (C * Real.log (Real.log (m : ℝ))) *
                      mechanism.expectedWelfare oracle reports)

/-- The earlier complete-partition requirement is an explicitly stronger variant. -/
def CompleteTruthfulSubmodularLogLogStatement : Prop :=
  QueryConventionLogLogStatement .valueAndDemand

/-- The original Markdown's complete-output, bundle-only reading is retained. -/
def DemandOnlyTruthfulSubmodularLogLogStatement : Prop :=
  QueryConventionLogLogStatement .demandOnly

/-- Bundle-only access with partial outputs; distinct from the reference-access target. -/
def PartialDemandOnlyTruthfulSubmodularLogLogStatement : Prop :=
  PartialQueryConventionLogLogStatement .demandOnly

/-- Explicit reference-access alias with partial realized allocations. -/
def ValueAndDemandTruthfulSubmodularLogLogStatement : Prop :=
  PartialQueryConventionLogLogStatement .valueAndDemand

/-- A complete-output solution is a partial-output solution with identical execution,
payments, welfare and costs; no reverse completion is asserted. -/
theorem partialQueryConventionLogLogStatement_of_complete {mode : OracleConvention}
    (h : QueryConventionLogLogStatement mode) : PartialQueryConventionLogLogStatement mode := by
  obtain ⟨C, hC, cutoff, hcutoff, coefficient, exponent, h⟩ := h
  refine ⟨C, hC, cutoff, hcutoff, coefficient, exponent, ?_⟩
  intro n m hn
  obtain ⟨Seed, mSeed, M, hTruth, hMeas, hQueries, hApprox⟩ := h n m hn
  letI : MeasurableSpace Seed := mSeed
  refine ⟨Seed, mSeed, M.toPartial, ?_, ?_, ?_, ?_⟩
  · exact M.toPartial_isUniversallyTruthful_iff.mpr hTruth
  · exact M.toPartial_hasMeasurableOutcomes hMeas
  · exact (M.toPartial_usesPolynomialQueries_iff coefficient exponent).mpr hQueries
  · simpa only [Mechanism.toPartial_expectedWelfare] using hApprox

end
end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

end
