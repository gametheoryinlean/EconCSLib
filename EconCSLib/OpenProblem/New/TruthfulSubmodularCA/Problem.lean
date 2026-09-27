/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.New.SharedConcepts.All
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 24. Truthful submodular combinatorial auctions
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

/-- Finite bundles from m labeled items. -/
abbrev Bundle (m : ℕ) := Finset (Fin m)

/-- The native normalized, nonnegative, monotone submodular valuation type. -/
abbrev Valuation (m : ℕ) :=
  SubmodularBundleValuation (Finset.univ : Finset (Fin m))

/-- The product reporting domain, without a prior over reports. -/
abbrev Profile (n m : ℕ) := Fin n → Valuation m

/-- Semantic bundle value; this definition does not grant free query access. -/
def bundleValue {m : ℕ} (v : Valuation m) (S : Bundle m) : ℝ :=
  v.val ⟨S, Finset.subset_univ S⟩

/-- Finite nonnegative real item prices. -/
structure Prices (m : ℕ) where
  item : Fin m → ℝ
  nonnegative : ∀ g, 0 ≤ item g

/-- Quasilinear bundle utility used to specify legal demand replies. -/
def demandUtility {m : ℕ} (v : Valuation m) (p : Prices m)
    (S : Bundle m) : ℝ :=
  bundleValue v S - ∑ g ∈ S, p.item g

/-- A legal bundle-only demand reply maximizes utility over all bundles. -/
def IsDemandAnswer {m : ℕ} (v : Valuation m) (p : Prices m)
    (S : Bundle m) : Prop :=
  ∀ T : Bundle m, demandUtility v p T ≤ demandUtility v p S

/-- Tie-breaking is fixed for each bidder and report, independent of opponents, seed, and
transcript; repeated queries are consistent. -/
structure DemandOracleFamily (n m : ℕ) where
  answer : Fin n → Valuation m → Prices m → Bundle m
  valid : ∀ i v p, IsDemandAnswer v p (answer i v p)

/-- Literal bundle-only access and the value-and-demand reference convention. -/
inductive OracleConvention
  | demandOnly
  | valueAndDemand
  deriving DecidableEq

/-- Every item has exactly one owner; no completion step is performed outside execution. -/
abbrev Assignment (n m : ℕ) := Fin m → Fin n

/-- A bidder's bundle in a complete assignment. -/
def assignedBundle {n m : ℕ} (A : Assignment n m) (i : Fin n) : Bundle m :=
  Finset.univ.filter fun g => A g = i

/-- Social welfare excludes transfers between seller and bidders. -/
def welfare {n m : ℕ} (v : Profile n m) (A : Assignment n m) : ℝ :=
  ∑ i, bundleValue (v i) (assignedBundle A i)

/-- Actual demand and value query counts from one execution. -/
structure QueryCount where
  demand : ℕ := 0
  value : ℕ := 0
  deriving DecidableEq

/-- Total calls to both oracle kinds. -/
def QueryCount.total (q : QueryCount) : ℕ := q.demand + q.value

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

/-- An item may remain unallocated; `some i` denotes its unique bidder. -/
abbrev PartialAssignment (n m : ℕ) := Fin m → Option (Fin n)

def partialAssignedBundle {n m : ℕ} (A : PartialAssignment n m) (i : Fin n) : Bundle m :=
  Finset.univ.filter fun g => A g = some i

structure PartialOutcome (n m : ℕ) where
  assignment : PartialAssignment n m
  payment : Fin n → ℝ

def partialWelfare {n m : ℕ} (v : Profile n m) (A : PartialAssignment n m) : ℝ :=
  ∑ i, bundleValue (v i) (partialAssignedBundle A i)

/-- Only the output type differs from the complete-allocation tree. All oracle interfaces,
reports, prices, and query-count structures are reused unchanged. -/
inductive PartialQueryTree (mode : OracleConvention) (n m : ℕ)
  | output (result : PartialOutcome n m)
  | demand (bidder : Fin n) (price : Prices m)
      (next : Bundle m → PartialQueryTree mode n m)
  | value (enabled : mode = .valueAndDemand) (bidder : Fin n) (bundle : Bundle m)
      (next : ℝ → PartialQueryTree mode n m)

def PartialQueryTree.run {mode : OracleConvention} {n m : ℕ}
    (T : PartialQueryTree mode n m) (oracle : DemandOracleFamily n m)
    (reports : Profile n m) : PartialOutcome n m × QueryCount :=
  match T with
  | .output result => (result, ⟨0, 0⟩)
  | .demand i p next =>
      let result := (next (oracle.answer i (reports i) p)).run oracle reports
      (result.1, ⟨result.2.demand + 1, result.2.value⟩)
  | .value _ i S next =>
      let result := (next (bundleValue (reports i) S)).run oracle reports
      (result.1, ⟨result.2.demand, result.2.value + 1⟩)

def PartialQueryTree.IsDSIC {mode : OracleConvention} {n m : ℕ}
    (T : PartialQueryTree mode n m) (oracle : DemandOracleFamily n m) : Prop :=
  ∀ (truth : Profile n m) (i : Fin n) (misreport : Valuation m),
    let honest := (T.run oracle truth).1
    let deviated := (T.run oracle (Function.update truth i misreport)).1
    bundleValue (truth i) (partialAssignedBundle honest.assignment i) - honest.payment i ≥
      bundleValue (truth i) (partialAssignedBundle deviated.assignment i) - deviated.payment i

structure PartialMechanism (mode : OracleConvention) (n m : ℕ)
    (Seed : Type*) [MeasurableSpace Seed] where
  seedLaw : Measure Seed
  probability : IsProbabilityMeasure seedLaw
  program : Seed → PartialQueryTree mode n m

def PartialMechanism.IsUniversallyTruthful {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : PartialMechanism mode n m Seed) : Prop :=
  ∀ oracle : DemandOracleFamily n m, ∀ seed, (M.program seed).IsDSIC oracle

def PartialMechanism.HasMeasurableOutcomes {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : PartialMechanism mode n m Seed) : Prop :=
  ∀ (oracle : DemandOracleFamily n m) (reports : Profile n m),
    (∀ A : PartialAssignment n m, MeasurableSet {seed |
      ((M.program seed).run oracle reports).1.assignment = A}) ∧
    (∀ i : Fin n, Measurable (fun seed =>
      ((M.program seed).run oracle reports).1.payment i))

def PartialMechanism.expectedWelfare {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : PartialMechanism mode n m Seed)
    (oracle : DemandOracleFamily n m) (reports : Profile n m) : ℝ :=
  ∫ seed, partialWelfare reports ((M.program seed).run oracle reports).1.assignment ∂M.seedLaw

def PartialMechanism.UsesPolynomialQueries {mode : OracleConvention} {n m : ℕ}
    {Seed : Type*} [MeasurableSpace Seed] (M : PartialMechanism mode n m Seed)
    (coefficient exponent : ℕ) : Prop :=
  let Input := Seed × Profile n m
  UniformResourceBound coefficient exponent (fun _ : Input => n + m)
    (fun (input : Input) (oracle : DemandOracleFamily n m) =>
      ((M.program input.1).run oracle input.2).2.total)

/-- Reference-style target with partial realized outputs. The benchmark remains complete,
equivalently optimal for monotone valuations and a nonempty bidder set. -/
def PartialQueryConventionLogLogStatement (mode : OracleConvention) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ cutoff : ℕ, 3 ≤ cutoff ∧
      ∃ coefficient exponent : ℕ,
        ∀ n m : ℕ, 0 < n →
          ∃ (Seed : Type) (mSeed : MeasurableSpace Seed),
            letI : MeasurableSpace Seed := mSeed
            ∃ mechanism : PartialMechanism mode n m Seed,
              mechanism.IsUniversallyTruthful ∧
              mechanism.HasMeasurableOutcomes ∧
              mechanism.UsesPolynomialQueries coefficient exponent ∧
              (cutoff ≤ m →
                ∀ (oracle : DemandOracleFamily n m) (reports : Profile n m)
                  (alternative : Assignment n m),
                  welfare reports alternative ≤
                    (C * Real.log (Real.log (m : ℝ))) *
                      mechanism.expectedWelfare oracle reports)

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

/-- Reference-access target: partial outputs, both charged query kinds, and universal
truthfulness. This is query complexity. -/
def TruthfulSubmodularLogLogStatement : Prop :=
  PartialQueryConventionLogLogStatement .valueAndDemand

end
end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA

/-- The primary value-and-demand query model permits unsold items. -/
theorem truthfulSubmodularCA :
    answer(sorry) ↔ TruthfulSubmodularLogLogStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.TruthfulSubmodularCA
