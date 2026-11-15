/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.New.SharedConcepts.LibraryDefinitions

/-!
# Lotteries and bundle mechanisms

Uniform lotteries and deterministic bundle mechanisms, with dominant-strategy
incentive compatibility and ex-post individual rationality.
-/


open scoped BigOperators

namespace EconCSLib.OpenProblem.New.EconCSBench

/-!
## Finite probability distributions
-/

/-- The uniform lottery, using Mathlib's simplex barycenter. -/
noncomputable abbrev uniformLottery (α : Type*) [Fintype α] [Nonempty α] :
    Lottery ℝ α := stdSimplex.barycenter

/-!
## Direct combinatorial mechanisms
-/

/-- A deterministic direct mechanism with a common report domain, using the native
MechanismWithTransfers type. DSIC and IR are separate predicates. -/
abbrev DeterministicBundleMechanism
    (I Report : Type*) {G : Type*} [DecidableEq G] (M : Finset G) :=
  MechanismWithTransfers I (fun _ => Report) (BundlePartitionAllocation I M) ℝ

/-- Compatibility name for the native allocation-rule projection. -/
abbrev DeterministicBundleMechanism.allocation
    {I Report G : Type*} [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M) :
    (I → Report) → BundlePartitionAllocation I M := mech.allocationRule

/-- Compatibility name for the native payment-rule projection. -/
abbrev DeterministicBundleMechanism.payment
    {I Report G : Type*} [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M) :
    (I → Report) → I → ℝ := mech.paymentRule

/-- The bundle interface already has the native transfer-mechanism type. -/
abbrev DeterministicBundleMechanism.toMechanismWithTransfers
    {I Report G : Type*} [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M) :
    MechanismWithTransfers I (fun _ => Report) (BundlePartitionAllocation I M) ℝ := mech

/-- Weak dominant-strategy truthfulness, with the same true valuation on both sides and
arbitrary opponent reports. IR, no subsidies and budget balance are separate
conditions; dominance need not be unique. -/
def DeterministicBundleMechanism.IsDSIC
    {I Report G : Type*} [DecidableEq I] [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M)
    (value : Report → BundleAllocation M → ℝ) : Prop :=
  mech.toMechanismWithTransfers.isDSIC
    (fun allocation payment truth i => value (truth i) (allocation.1 i) - payment i)

/-- Native weak dominance is equivalent to the bundle formulation: opponents' reports
range over all profiles while only the agent's own true value is used. -/
theorem DeterministicBundleMechanism.isDSIC_iff
    {I Report G : Type*} [DecidableEq I] [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M)
    (value : Report → BundleAllocation M → ℝ) :
    mech.IsDSIC value ↔
      ∀ (truth : I → Report) (i : I) (misreport : Report),
        value (truth i) ((mech.allocation truth).1 i) - mech.payment truth i ≥
          value (truth i)
              ((mech.allocation (Function.update truth i misreport)).1 i) -
            mech.payment (Function.update truth i misreport) i := by
  change (∀ (truth : I → Report) (i : I) (misreport : Report) (reports : I → Report),
    value (truth i) ((mech.allocation (Function.update reports i misreport)).1 i) -
        mech.payment (Function.update reports i misreport) i ≤
      value (truth i) ((mech.allocation (Function.update reports i (truth i))).1 i) -
        mech.payment (Function.update reports i (truth i)) i) ↔ _
  constructor
  · intro h truth i misreport
    simpa only [Function.update_eq_self] using h truth i misreport truth
  · intro h truth i misreport reports
    simpa only [Function.update_self, Function.update_idem] using
      h (Function.update reports i (truth i)) i misreport

/-- Ex-post individual rationality with outside option zero. Negative payments are not
excluded unless the problem separately forbids subsidies. -/
def DeterministicBundleMechanism.IsIR
    {I Report G : Type*} [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M)
    (value : Report → BundleAllocation M → ℝ) : Prop := by
  classical
  exact mech.toMechanismWithTransfers.isExPostIR
    (fun allocation payment truth i => value (truth i) (allocation.1 i) - payment i)

/-- For private bundle values, native ex-post IR against arbitrary opponents' reports is
precisely nonnegative truthful utility at every report profile. -/
theorem DeterministicBundleMechanism.isIR_iff
    {I Report G : Type*} [DecidableEq G] {M : Finset G}
    (mech : DeterministicBundleMechanism I Report M)
    (value : Report → BundleAllocation M → ℝ) :
    mech.IsIR value ↔ ∀ (truth : I → Report) (i : I),
      0 ≤ value (truth i) ((mech.allocation truth).1 i) - mech.payment truth i := by
  classical
  change (∀ (truth : I → Report) (i : I) (reports : I → Report),
    0 ≤ value (truth i) ((mech.allocation (Function.update reports i (truth i))).1 i) -
      mech.payment (Function.update reports i (truth i)) i) ↔ _
  constructor
  · intro h truth i
    simpa only [Function.update_eq_self] using h truth i truth
  · intro h truth i reports
    simpa only [Function.update_self] using h (Function.update reports i (truth i)) i

end EconCSLib.OpenProblem.New.EconCSBench
