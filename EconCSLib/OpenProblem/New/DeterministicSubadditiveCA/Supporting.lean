/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.DeterministicSubadditiveCA.Problem

/-!
# DeterministicSubadditiveCA: supporting material

Auxiliary definitions and lemmas for the problem statement.
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

/-- Literal bit complexity depending only on market dimensions. The protocol is chosen
before reports and reads only the current sender's private input. The reference
precision convention is defined separately. -/
def SubadditiveMechanism.HasBitCommunicationBound
    {I G : Type*} [Fintype I] [DecidableEq G] {M : Finset G}
    (mechanism : SubadditiveMechanism I M)
    (coefficient exponent : ℕ) : Prop :=
  ∃ protocol : BitCommunicationProtocol I
      (fun _ => SubadditiveBundleValuation M)
      (fun reports =>
        (mechanism.allocation reports, mechanism.payment reports)),
    protocol.HasCommunicationBound coefficient exponent
      (fun _ => [M.card, Fintype.card I])

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

/-- The precision-independent domain of a single auction rule. -/
abbrev FinitelyPreciseValuation
    {G : Type*} [DecidableEq G] (M : Finset G) :=
  {v : SubadditiveBundleValuation M // ∃ k : ℕ, HasPrecision k v}

/-- Forget the particular precision bound without changing any value. -/
def liftPrecisionValuation
    {G : Type*} [DecidableEq G] {M : Finset G} {k : ℕ}
    (v : PrecisionValuation M k) : FinitelyPreciseValuation M :=
  ⟨v.1, ⟨k, v.2⟩⟩

/-- Evaluate the original semantic valuation, without encoding an answer. -/
def finitePrecisionReportedValue
    {G : Type*} [DecidableEq G] {M : Finset G}
    (v : FinitelyPreciseValuation M) : BundleAllocation M → ℝ :=
  v.1.val

abbrev FinitePrecisionMechanism
    (I : Type*) {G : Type*} [DecidableEq G] (M : Finset G) :=
  DeterministicBundleMechanism I (FinitelyPreciseValuation M) M

/-- One coefficient and exponent work for every precision. Both allocation and payments of
the same mechanism are produced by the protocol. -/
def FinitePrecisionMechanism.HasPrecisionCommunicationBound
    {I G : Type*} [Fintype I] [DecidableEq G] {M : Finset G}
    (mechanism : FinitePrecisionMechanism I M)
    (coefficient exponent : ℕ) : Prop :=
  ∀ k : ℕ,
    ∃ protocol : BitCommunicationProtocol I
        (fun _ => PrecisionValuation M k)
        (fun reports =>
          let lifted := fun i => liftPrecisionValuation (reports i)
          (mechanism.allocation lifted, mechanism.payment lifted)),
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

/-- Literal all-real inputs with a bit bound depending only on n and m; this is not the
precision convention used by the cited papers. -/
def LiteralRealTwoApproximationStatement : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ n m : ℕ, 0 < n →
      ∃ mechanism : SubadditiveMechanism (Fin n) (Finset.univ : Finset (Fin m)),
        mechanism.IsDSIC reportedValue ∧
        mechanism.HasBitCommunicationBound coefficient exponent ∧
        IsTwoApproximation reportedValue mechanism

/-- A mechanism on the union of the precision grids. DSIC compares reports across grids. -/
def ReferencePrecisionTwoApproximationStatement : Prop :=
  ∃ coefficient exponent : ℕ,
    ∀ n m : ℕ, 0 < n →
      ∃ mechanism : FinitePrecisionMechanism (Fin n)
          (Finset.univ : Finset (Fin m)),
        mechanism.IsDSIC finitePrecisionReportedValue ∧
        mechanism.HasPrecisionCommunicationBound coefficient exponent ∧
        IsTwoApproximation finitePrecisionReportedValue mechanism

end EconCSLib.OpenProblem.New.EconCSBench.DeterministicSubadditiveCA

end
