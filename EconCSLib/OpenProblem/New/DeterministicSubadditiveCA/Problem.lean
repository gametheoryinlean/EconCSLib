/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.SharedConcepts.All
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer

/-!
# 03. Deterministic subadditive combinatorial auctions
-/



section

/-!
## Truthful subadditive auctions and bit communication

Valuations are normalized, monotone, subadditive and real-valued. The native
direct-mechanism DSIC inequality is reused. Both allocation and all payments are
determined by the same protocol leaf. Each internal node sends one bit; local
computation is uncharged.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

/-- A deterministic mechanism on the full real subadditive domain. -/
abbrev SubadditiveMechanism
    (I : Type*) {G : Type*} [DecidableEq G] (M : Finset G) :=
  DeterministicBundleMechanism I (SubadditiveBundleValuation M) M

/-- The true valuation used on both sides of the incentive inequality. -/
def reportedValue
    {G : Type*} [DecidableEq G] {M : Finset G}
    (v : SubadditiveBundleValuation M) : BundleAllocation M → ℝ :=
  v.val

/-- Every feasible allocation has at most twice the mechanism's welfare. This includes
zero optimum and imposes no additional completeness condition. -/
noncomputable def IsTwoApproximation
    {I Report G : Type*} [Fintype I] [DecidableEq G] {M : Finset G}
    (value : Report → BundleAllocation M → ℝ)
    (mechanism : DeterministicBundleMechanism I Report M) : Prop :=
  ∀ (reports : I → Report) (alternative : BundlePartitionAllocation I M),
    bundleSocialWelfare (fun i => value (reports i)) alternative ≤
      2 * bundleSocialWelfare (fun i => value (reports i))
        (mechanism.allocation reports)

end EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

end


section

/-!
## Public precision and a fixed underlying mechanism

Ron--Thomas--Weinberg--Zhang (arXiv:2409.08241v1, Section 2, footnote 11 and Appendix
D) use V_k = {a / 2^k : a <= 2^(2k)}, with polynomial dependence on k. The same
allocation and payments must be implemented at every precision (Dobzinski,
arXiv:1604.01971, Appendix A.4.1). The union is dyadic, not all rationals or reals.
Local runtime is uncharged; valuations remain private.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

/-- The exact dyadic grid at public precision k. -/
def ValueHasPrecision (k : ℕ) (x : ℝ) : Prop :=
  ∃ a : ℕ, a ≤ 2 ^ (2 * k) ∧ x = (a : ℝ) / (2 : ℝ) ^ k

/-- A common precision bound for every bundle value. -/
def HasPrecision
    {G : Type*} [DecidableEq G] {M : Finset G}
    (k : ℕ) (v : SubadditiveBundleValuation M) : Prop :=
  ∀ S : BundleAllocation M, ValueHasPrecision k (v.val S)

/-- One bidder's private input at precision k. -/
abbrev PrecisionValuation
    {G : Type*} [DecidableEq G] (M : Finset G) (k : ℕ) :=
  {v : SubadditiveBundleValuation M // HasPrecision k v}

/-- A mechanism on all real reports, implemented on each precision grid. This enforces
cross-precision consistency, but does not itself assert DSIC. -/
def SubadditiveMechanism.HasRealPrecisionCommunicationBound
    {I G : Type*} [Fintype I] [DecidableEq G] {M : Finset G}
    (mechanism : SubadditiveMechanism I M)
    (coefficient exponent : ℕ) : Prop :=
  ∀ k : ℕ,
    ∃ protocol : BitCommunicationProtocol I
        (fun _ => PrecisionValuation M k)
        (fun reports =>
          let semantic := fun i => (reports i).1
          (mechanism.allocation semantic, mechanism.payment semantic)),
      protocol.HasCommunicationBound coefficient exponent
        (fun _ => [M.card, Fintype.card I, k])

end EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

end


section

/-!
## Independent interpretations of the truthful two-approximation question

The adopted main target is RealMechanismPrecisionTwoApproximationStatement: a
real-domain mechanism with communication polynomial in n, m and public precision k.
LiteralReal and the dyadic-domain ReferencePrecision variants are retained separately;
no equivalence is claimed. Coefficients are uniform over dimensions and reports.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

/-- The full-real DSIC and approximation target, with communication bounds for precision-k
inputs and one mechanism fixed before k. -/
def RealMechanismPrecisionTwoApproximationStatement : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ n m : ℕ, 0 < n →
      ∃ mechanism : SubadditiveMechanism (Fin n) (Finset.univ : Finset (Fin m)),
        mechanism.IsDSIC reportedValue ∧
        mechanism.HasRealPrecisionCommunicationBound coefficient exponent ∧
        IsTwoApproximation reportedValue mechanism

end EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

/-- Full-real truthfulness with the explicitly adopted precision communication bound. -/
theorem deterministicSubadditiveCA :
    answer(sorry) ↔ RealMechanismPrecisionTwoApproximationStatement := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA
