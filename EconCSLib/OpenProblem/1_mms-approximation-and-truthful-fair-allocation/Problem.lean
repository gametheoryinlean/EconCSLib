/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common

open scoped BigOperators

namespace EconCSLib.OpenProblem.EconCSBench.MMSApproximationTruthfulness

open SocialChoice.FairDivision.Indivisible
open MeasureTheory

/-- One agent's admissible additive report.  Nonnegativity is part of the
report type, and weights outside the advertised ground set are fixed at zero,
so a mechanism cannot use irrelevant ambient elements as an extra message
channel. -/
structure AdditiveReport
    (G : Type*) [DecidableEq G] (M : Finset G) where
  weight : G → ℝ
  nonnegative : ∀ g ∈ M, 0 ≤ weight g
  outside_zero : ∀ g, g ∉ M → weight g = 0

instance {G : Type*} [DecidableEq G] {M : Finset G} :
    CoeFun (AdditiveReport G M) (fun _ => G → ℝ) :=
  ⟨AdditiveReport.weight⟩

private theorem additiveReport_eq_of_weight_eq
    {G : Type*} [DecidableEq G] {M : Finset G}
    (left right : AdditiveReport G M)
    (hweight : left.weight = right.weight) : left = right := by
  cases left
  cases right
  cases hweight
  rfl

/-- Convert a report profile into the library's additive valuation. -/
def reportValuation
    {N G : Type*} [DecidableEq G] {M : Finset G}
    (reports : N → AdditiveReport G M) :
    AdditiveValuation N G :=
  ⟨fun i => reports i⟩

/-- A deterministic allocation mechanism without payments. -/
structure DeterministicFairMechanism
    (N G : Type*) [Fintype N] [DecidableEq G] (M : Finset G) where
  /-- Allocation selected from reports. -/
  allocate : (N → AdditiveReport G M) → Allocation N G
  /-- Goods may be left unallocated but never duplicated or invented. -/
  feasible :
    ∀ reports, IsPartialIndivisibleAllocation M (allocate reports)

/-- Dominant-strategy truthfulness without payments. -/
def DeterministicFairMechanism.IsTruthful
    {N G : Type*} [Fintype N] [DecidableEq N] [DecidableEq G]
    {M : Finset G} (mechanism : DeterministicFairMechanism N G M) : Prop :=
  ∀ reports i fake,
    (reportValuation reports).toValuation.val i (mechanism.allocate reports i) ≥
      (reportValuation reports).toValuation.val i
        (mechanism.allocate (Function.update reports i fake) i)

local instance measurableFairAllocation
    (N G : Type*) : MeasurableSpace (Allocation N G) :=
  ⊤

/-- A randomized allocation mechanism without payments.  The output law may
depend on the report profile, exactly as in the definition of a randomized
direct mechanism; no common finite seed space is imposed. -/
structure RandomizedFairMechanism
    (N G : Type*) [Fintype N] [DecidableEq N] [DecidableEq G]
    (M : Finset G) where
  /-- Report-dependent probability law over allocations. -/
  allocation :
    (N → AdditiveReport G M) → Measure (Allocation N G)
  /-- Internal randomization has total mass one. -/
  probability :
    ∀ reports, IsProbabilityMeasure (allocation reports)
  /-- The randomized goals do not grant permission to discard goods, so every
  realized allocation is a complete partition almost surely. -/
  feasible :
    ∀ reports, ∀ᵐ A ∂allocation reports,
      IsAllocation M A
  /-- Every truthful utility random variable is integrable.  The same field
  applies to a deviating profile by instantiating `reports` with that profile. -/
  utility_integrable :
    ∀ (trueReports submittedReports : N → AdditiveReport G M) (i : N),
      Integrable
        (fun A =>
          (reportValuation trueReports).toValuation.val i (A i))
        (allocation submittedReports)

/-- Truthfulness in expectation. -/
def RandomizedFairMechanism.IsTruthfulInExpectation
    {N G : Type*} [Fintype N] [DecidableEq N] [DecidableEq G]
    {M : Finset G}
    (mechanism : RandomizedFairMechanism N G M) : Prop :=
  ∀ reports i fake,
    (∫ A,
      (reportValuation reports).toValuation.val i
        (A i) ∂mechanism.allocation reports) ≥
    (∫ A,
      (reportValuation reports).toValuation.val i
        (A i)
      ∂mechanism.allocation (Function.update reports i fake))

/-! ## Canonical strict-RAM interface

The operational variants below use `Fin n` and `Fin m` as the canonical
labels.  Thus the representation is fixed by the statement, rather than
being selected after the program.  A report table contains one exact-real
word per agent--good pair, while a complete allocation contains one integer
owner per good.  These are unit-cost exact-word encodings; randomization is
kept separate and consists only of fair Boolean tape cells. -/

/-- Turn a fixed injective structural word representation into a lossless
encoding.  The classical inverse only recognizes the already fixed code and
is not an implementation-selected semantic decoder. -/
noncomputable def structuralEncodingOfInjective {α : Type*}
    (encode : α → List UnitCostRAM.Word)
    (hinjective : Function.Injective encode) :
    UnitCostRAM.Encoding α := by
  classical
  exact
    { encode := encode
      decode := fun words =>
        if h : ∃ value, encode value = words then
          some (Classical.choose h)
        else
          none
      decode_encode := fun value => by
        rw [dif_pos ⟨value, rfl⟩]
        congr 1
        apply hinjective
        exact Classical.choose_spec
          (show ∃ candidate, encode candidate = encode value from
            ⟨value, rfl⟩) }

/-- Canonically labelled additive report profiles. -/
abbrev CanonicalMMSReports (n m : ℕ) :=
  Fin n → AdditiveReport (Fin m) Finset.univ

/-- A complete allocation is encoded canonically by the owner of each good. -/
abbrev CanonicalMMSOwners (n m : ℕ) := Fin m → Fin n

/-- The ordinary fair-division allocation induced by an owner vector. -/
def allocationOfOwners {n m : ℕ}
    (owners : CanonicalMMSOwners n m) : Allocation (Fin n) (Fin m) :=
  fun i => Finset.univ.filter fun g => owners g = i

/-- Owner vectors always denote complete, pairwise-disjoint allocations. -/
theorem allocationOfOwners_isAllocation {n m : ℕ}
    (owners : CanonicalMMSOwners n m) :
    IsAllocation (Finset.univ : Finset (Fin m))
      (allocationOfOwners owners) := by
  classical
  constructor
  · intro i j hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    simp only [allocationOfOwners, Finset.mem_filter, Finset.mem_univ,
      true_and] at hgi hgj
    exact hij (hgi.symm.trans hgj)
  · ext g
    simp only [Finset.mem_univ, Finset.mem_biUnion, allocationOfOwners,
      Finset.mem_filter, true_and]
    constructor
    · intro _
      exact ⟨owners g, rfl⟩
    · intro _
      trivial

/-- Header plus the fixed canonical enumeration of the exact-real report
table. -/
noncomputable def canonicalMMSReportWords (n m : ℕ)
    (reports : CanonicalMMSReports n m) : List UnitCostRAM.Word :=
  [.integer (Int.ofNat n), .integer (Int.ofNat m)] ++
    List.ofFn fun index : Fin (Fintype.card (Fin n × Fin m)) =>
      let pair := (Fintype.equivFin (Fin n × Fin m)).symm index
      .real ((reports pair.1).weight pair.2)

private theorem canonicalMMSReportWords_injective (n m : ℕ) :
    Function.Injective (canonicalMMSReportWords n m) := by
  intro left right hwords
  have hpayload := congrArg (List.drop 2) hwords
  have htable :
      (fun index : Fin (Fintype.card (Fin n × Fin m)) =>
        let pair := (Fintype.equivFin (Fin n × Fin m)).symm index
        UnitCostRAM.Word.real ((left pair.1).weight pair.2)) =
      (fun index : Fin (Fintype.card (Fin n × Fin m)) =>
        let pair := (Fintype.equivFin (Fin n × Fin m)).symm index
        UnitCostRAM.Word.real ((right pair.1).weight pair.2)) := by
    apply List.ofFn_injective
    simpa [canonicalMMSReportWords] using hpayload
  funext i
  apply additiveReport_eq_of_weight_eq
  funext g
  have hcoordinate :=
    congrFun htable ((Fintype.equivFin (Fin n × Fin m)) (i, g))
  exact UnitCostRAM.Word.real.inj (by simpa using hcoordinate)

/-- Fixed lossless exact-word encoding of the canonical report table. -/
noncomputable def canonicalMMSReportEncoding (n m : ℕ) :
    UnitCostRAM.Encoding (CanonicalMMSReports n m) :=
  structuralEncodingOfInjective
    (canonicalMMSReportWords n m)
    (canonicalMMSReportWords_injective n m)

/-- Header plus one integer owner label for each good. -/
def canonicalMMSOwnerWords (n m : ℕ)
    (owners : CanonicalMMSOwners n m) : List UnitCostRAM.Word :=
  [.integer (Int.ofNat n), .integer (Int.ofNat m)] ++
    List.ofFn fun g : Fin m => .integer (Int.ofNat (owners g).val)

private theorem canonicalMMSOwnerWords_injective (n m : ℕ) :
    Function.Injective (canonicalMMSOwnerWords n m) := by
  intro left right hwords
  have hpayload := congrArg (List.drop 2) hwords
  have howners :
      (fun g : Fin m => UnitCostRAM.Word.integer (Int.ofNat (left g).val)) =
      fun g : Fin m => UnitCostRAM.Word.integer (Int.ofNat (right g).val) := by
    apply List.ofFn_injective
    simpa [canonicalMMSOwnerWords] using hpayload
  funext g
  apply Fin.ext
  have hinteger := UnitCostRAM.Word.integer.inj (congrFun howners g)
  exact Int.ofNat_injective hinteger

/-- Fixed lossless integer-word encoding of complete allocations. -/
noncomputable def canonicalMMSOwnerEncoding (n m : ℕ) :
    UnitCostRAM.Encoding (CanonicalMMSOwners n m) :=
  structuralEncodingOfInjective
    (canonicalMMSOwnerWords n m)
    (canonicalMMSOwnerWords_injective n m)

/-- A strict certificate's explicit polynomial is dominated by the uniform
coefficient/exponent pair chosen before the finite domains. -/
def strictMMSCertificateRunsWithin
    {Input : Type*} {Output : Input → Type*}
    {inputEncoding : UnitCostRAM.Encoding Input}
    {outputEncoding : UnitCostRAM.DependentEncoding Output}
    {function : (input : Input) → Output input}
    (certificate : StrictRAMComputableInPolyTime
      inputEncoding outputEncoding function)
    (coefficient exponent : ℕ) : Prop :=
  ∀ input,
    certificate.time.eval (inputEncoding.size input) ≤
      coefficient * (inputEncoding.size input + 1) ^ exponent

/-- Peak space of the same deterministic interpreter execution is bounded by
the same uniform polynomial.  Static registers and the encoded input are
included, so a one-step bulk allocation cannot conceal superpolynomial
memory. -/
def strictMMSCertificateUsesSpaceWithin
    {Input : Type*} {Output : Input → Type*}
    {inputEncoding : UnitCostRAM.Encoding Input}
    {outputEncoding : UnitCostRAM.DependentEncoding Output}
    {function : (input : Input) → Output input}
    (certificate : StrictRAMComputableInPolyTime
      inputEncoding outputEncoding function)
    (coefficient exponent : ℕ) : Prop :=
  ∀ input,
    certificate.program.registerCount + inputEncoding.size input +
        UnitCostRAM.ProfiledCost.peakCells
          (UnitCostRAM.run (UnitCostRAM.closedEnvironment fun _ => false)
            certificate.program (certificate.fuel input)
            (inputEncoding.encode input)) ≤
      coefficient * (inputEncoding.size input + 1) ^ exponent

/-- The concrete deterministic allocation function has one finite strict-RAM
program over the canonical representations fixed above. -/
def AllocationRuleRunsWithin
    {n m : ℕ}
    (allocate : CanonicalMMSReports n m → CanonicalMMSOwners n m)
    (program : UnitCostRAM.Program Empty)
    (coefficient exponent : ℕ) : Prop :=
  ∃ certificate : StrictRAMComputableInPolyTime
      (canonicalMMSReportEncoding n m)
      (canonicalMMSOwnerEncoding n m).dependent allocate,
    certificate.program = program ∧
      strictMMSCertificateRunsWithin certificate coefficient exponent ∧
      strictMMSCertificateUsesSpaceWithin certificate coefficient exponent

/-- A finite tape of independent fair Boolean cells. -/
abbrev MMSRandomTape (randomBits : ℕ) := Fin randomBits → Bool

/-- The sampler has no external operation at all: its only varying environment
is the declared Boolean tape, extended deterministically by `false` after its
last fair cell. -/
def mmsRandomEnvironment {randomBits : ℕ}
    (tape : MMSRandomTape randomBits) :
    UnitCostRAM.MachineEnvironment Empty :=
  UnitCostRAM.closedEnvironment fun cursor =>
    if h : cursor < randomBits then tape ⟨cursor, h⟩ else false

/-- Lift the fixed owner-vector encoding to outputs depending on reports and
the fair tape. -/
noncomputable def canonicalMMSOwnerChoiceEncoding
    (n m randomBits : ℕ) :
    UnitCostRAM.ChoiceDependentEncoding
      (fun (_ : CanonicalMMSReports n m)
        (_ : MMSRandomTape randomBits) => CanonicalMMSOwners n m) where
  encode _ _ := (canonicalMMSOwnerEncoding n m).encode
  decode _ _ := (canonicalMMSOwnerEncoding n m).decode
  decode_encode _ _ := (canonicalMMSOwnerEncoding n m).decode_encode

/-- One randomized allocation rule sampled by a uniform finite Boolean tape. -/
structure CanonicalRandomizedMMSRule (n m randomBits : ℕ) where
  allocate : CanonicalMMSReports n m →
    MMSRandomTape randomBits → CanonicalMMSOwners n m

/-- Expected utility under the uniform law on all tapes. -/
noncomputable def CanonicalRandomizedMMSRule.expectedUtility
    {n m randomBits : ℕ}
    (rule : CanonicalRandomizedMMSRule n m randomBits)
    (trueReports submittedReports : CanonicalMMSReports n m)
    (i : Fin n) : ℝ :=
  Lottery.expectedValue (uniformLottery (MMSRandomTape randomBits)) fun tape =>
    (reportValuation trueReports).toValuation.val i
      (allocationOfOwners (rule.allocate submittedReports tape) i)

/-- Truthfulness in expectation for the uniform fair-bit sampler. -/
def CanonicalRandomizedMMSRule.IsTruthfulInExpectation
    {n m randomBits : ℕ}
    (rule : CanonicalRandomizedMMSRule n m randomBits) : Prop :=
  ∀ reports i fake,
    rule.expectedUtility reports reports i ≥
      rule.expectedUtility reports (Function.update reports i fake) i

/-- The advertised MMS factor holds for every tape, not merely on average. -/
def CanonicalRandomizedMMSRule.HasExPostMMS
    {n m randomBits : ℕ}
    (rule : CanonicalRandomizedMMSRule n m randomBits)
    (factor : ℝ) : Prop :=
  ∀ reports tape,
    IsAlphaMMS factor (reportValuation reports).toValuation Finset.univ
      (allocationOfOwners (rule.allocate reports tape))

/-- One strict sampler program must compute the allocation for every report
and every fair tape.  The fixed environment has no external callback that
could conceal an answer.  Actual interpreter time, consumed random bits, and
peak space are all dominated by the displayed uniform polynomial. -/
def CanonicalRandomizedMMSRule.RunsWithin
    {n m randomBits : ℕ}
    (rule : CanonicalRandomizedMMSRule n m randomBits)
    (program : UnitCostRAM.Program Empty)
    (coefficient exponent : ℕ) : Prop :=
  ∃ certificate : StrictRAMComputableInPolyTimeWithFixedEnvironment
      (canonicalMMSReportEncoding n m)
      (canonicalMMSOwnerChoiceEncoding n m randomBits)
      Empty (fun _ tape => mmsRandomEnvironment tape)
      rule.allocate,
    certificate.program = program ∧
    (∀ (reports : CanonicalMMSReports n m)
        (_tape : MMSRandomTape randomBits),
      certificate.time.eval
          ((canonicalMMSReportEncoding n m).size reports) ≤
        coefficient *
          ((canonicalMMSReportEncoding n m).size reports + 1) ^ exponent) ∧
    (∀ (reports : CanonicalMMSReports n m)
        (tape : MMSRandomTape randomBits),
      UnitCostRAM.ProfiledCost.randomBits
          (certificate.execution reports tape) ≤
        coefficient *
          ((canonicalMMSReportEncoding n m).size reports + 1) ^ exponent) ∧
    ∀ (reports : CanonicalMMSReports n m)
        (tape : MMSRandomTape randomBits),
      certificate.program.registerCount +
          (canonicalMMSReportEncoding n m).size reports +
          UnitCostRAM.ProfiledCost.peakCells
            (certificate.execution reports tape) ≤
        coefficient *
          ((canonicalMMSReportEncoding n m).size reports + 1) ^ exponent

/-- The factor may depend on the number of agents, as required by the source
questions (notably the randomized `1 / log n` benchmark). -/
def IsAdmissibleFactorFunction (factor : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → 0 ≤ factor n ∧ factor n ≤ 1

/-- Every nonnegative additive instance admits the factor prescribed for its
number of agents. -/
def MMSExistenceGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq G]
      (problem : AdditiveInstance N G),
    (∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) →
      ∃ A : Allocation N G,
        problem.feasible A ∧
          IsAlphaMMS (factor (Fintype.card N))
            problem.toValuation problem.allGoods A

/-- Every nonnegative additive instance has the prescribed MMS factor produced
by one uniform polynomial-time interface.  Canonical `Fin` labels lose no
finite instances up to relabelling, and make the report/allocation encodings
independent of the implementation witness. -/
def PolynomialMMSExistenceGuarantee (factor : ℕ → ℝ) : Prop :=
  ∃ coefficient exponent : ℕ,
  ∃ program : UnitCostRAM.Program Empty,
    ∀ n, 0 < n → ∀ m,
      ∃ allocate : CanonicalMMSReports n m → CanonicalMMSOwners n m,
        (∀ reports,
          IsAlphaMMS (factor n)
            (reportValuation reports).toValuation Finset.univ
            (allocationOfOwners (allocate reports))) ∧
        AllocationRuleRunsWithin allocate program
          coefficient exponent

/-- `factor n` is the pointwise supremum of all achievable factor functions.
The supremum need not itself be attained. -/
def IsPointwiseTightFactor
    (guarantee : (ℕ → ℝ) → Prop) (factor : ℕ → ℝ) : Prop :=
  IsAdmissibleFactorFunction factor ∧
    (∀ other, IsAdmissibleFactorFunction other → guarantee other →
      ∀ n, 0 < n → other n ≤ factor n) ∧
    ∀ n, 0 < n → ∀ ε, 0 < ε →
      ∃ other, IsAdmissibleFactorFunction other ∧ guarantee other ∧
        factor n - ε < other n

/-- Pointwise-tight MMS-existence factor as a function of `n`. -/
def IsBestMMSExistenceFactor (factor : ℕ → ℝ) : Prop :=
  IsPointwiseTightFactor MMSExistenceGuarantee factor

/-- A pointwise-greatest polynomial-time MMS factor. -/
def IsBestPolynomialMMSFactor (factor : ℕ → ℝ) : Prop :=
  IsPointwiseTightFactor PolynomialMMSExistenceGuarantee factor

/-- A deterministic truthful mechanism realizes `factor n`, allowing
unallocated goods. -/
def DeterministicTruthfulGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq N] [DecidableEq G]
      (M : Finset G),
    ∃ mechanism : DeterministicFairMechanism N G M,
      mechanism.IsTruthful ∧
      ∀ reports,
        IsAlphaMMS (factor (Fintype.card N))
          (reportValuation reports).toValuation M
          (mechanism.allocate reports)

/-- Pointwise-best deterministic truthful MMS factor. -/
def IsBestDeterministicTruthfulFactor (factor : ℕ → ℝ) : Prop :=
  IsPointwiseTightFactor DeterministicTruthfulGuarantee factor

/-- Randomized truthfulness in expectation with an ex-post MMS factor for
every seed. -/
def RandomizedTIEGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ (N G : Type) [Fintype N] [Nonempty N] [DecidableEq N] [DecidableEq G]
      (M : Finset G),
    ∃ mechanism : RandomizedFairMechanism N G M,
      mechanism.IsTruthfulInExpectation ∧
      ∀ reports, ∀ᵐ A ∂mechanism.allocation reports,
          IsAlphaMMS (factor (Fintype.card N))
            (reportValuation reports).toValuation M
            A

/-- Polynomial-time randomized TIE guarantee from one strict sampler program.
The tape length is itself bounded by the same displayed polynomial and its law
is the canonical uniform law on Boolean strings, so arbitrary real-valued
output probabilities cannot be supplied as free advice. -/
def PolynomialRandomizedTIEGuarantee (factor : ℕ → ℝ) : Prop :=
  ∃ coefficient exponent : ℕ,
  ∃ program : UnitCostRAM.Program Empty,
    ∀ n, 0 < n → ∀ m,
      ∃ rule : CanonicalRandomizedMMSRule n m
          (coefficient * (n + m + n * m + 1) ^ exponent),
        rule.IsTruthfulInExpectation ∧
        rule.RunsWithin program coefficient exponent ∧
        rule.HasExPostMMS (factor n)

/-- Pointwise-best unrestricted randomized TIE factor. -/
def IsBestRandomizedTIEFactor (factor : ℕ → ℝ) : Prop :=
  IsPointwiseTightFactor RandomizedTIEGuarantee factor

/-- Pointwise-best polynomial-time randomized TIE factor. -/
def IsBestPolynomialRandomizedTIEFactor (factor : ℕ → ℝ) : Prop :=
  IsPointwiseTightFactor PolynomialRandomizedTIEGuarantee factor

/-- The five function-valued answers explicitly requested by the two research
goals.  Values at `0` are intentionally unconstrained because the Markdown only
considers a nonempty agent set. -/
structure MMSApproximationAndTruthfulAllocationAnswer where
  existenceFactor : ℕ → ℝ
  polynomialExistenceFactor : ℕ → ℝ
  deterministicTruthfulFactor : ℕ → ℝ
  randomizedTIEFactor : ℕ → ℝ
  polynomialRandomizedTIEFactor : ℕ → ℝ

/-- Correctness of a proposed tuple of tight MMS-factor functions. -/
def IsCorrectMMSApproximationAndTruthfulAllocationAnswer
    (result : MMSApproximationAndTruthfulAllocationAnswer) : Prop :=
  IsBestMMSExistenceFactor result.existenceFactor ∧
  IsBestPolynomialMMSFactor result.polynomialExistenceFactor ∧
  IsBestDeterministicTruthfulFactor result.deterministicTruthfulFactor ∧
  IsBestRandomizedTIEFactor result.randomizedTIEFactor ∧
  IsBestPolynomialRandomizedTIEFactor
    result.polynomialRandomizedTIEFactor

/-- Open-problem statement: all five pointwise-tight factor functions requested
by the Markdown can be supplied simultaneously. -/
def MMSApproximationAndTruthfulAllocationStatement : Prop :=
  ∃ result : MMSApproximationAndTruthfulAllocationAnswer,
    IsCorrectMMSApproximationAndTruthfulAllocationAnswer result

/-- Typed open-problem answer.  A submission must give all five factor
functions explicitly; a pointwise supremum/infimum restatement is not regarded
as solving the research problem. -/
theorem mmsApproximationAndTruthfulAllocation :
    IsCorrectMMSApproximationAndTruthfulAllocationAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.MMSApproximationTruthfulness
