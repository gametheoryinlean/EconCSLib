/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.SocialChoice.FairDivision.Indivisible.Instance
import EconCSLib.SocialChoice.FairDivision.Indivisible.MMS
import Lean.Elab.Tactic.NormCast
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# 12. MMS approximation and truthful allocation
-/



section

/-!
## MMS guarantees and allocation mechanisms without payments

Native additive valuations and MMS are reused. Real singleton values may be zero or
tied. OP1 and randomized OP2b require complete allocations; deterministic OP2a permits
unallocated goods. Incentives use true values.
-/

open scoped BigOperators
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open SocialChoice.FairDivision.Indivisible

/-- One bidder's nonnegative singleton values on exactly m goods. -/
structure AdditiveReport (K : Type*) [Zero K] [LE K] (m : ℕ) where
  weight : Fin m → K
  nonnegative : ∀ g, 0 ≤ weight g

abbrev Reports (K : Type*) [Zero K] [LE K] (n m : ℕ) :=
  Fin n → AdditiveReport K m

/-- At most one owner per good; none records an unallocated good. -/
abbrev Owners (n m : ℕ) := Fin m → Option (Fin n)

/-- Interpret owner labels in the library's native allocation type. -/
def allocationOfOwners {n m : ℕ} (a : Owners n m) : Allocation (Fin n) (Fin m) :=
  fun i => Finset.univ.filter fun g => a g = some i

/-- Every good has exactly one owner. -/
def IsComplete {n m : ℕ} (a : Owners n m) : Prop :=
  ∀ g, a g ≠ none

/-- The native additive valuation induced by the singleton table. -/
def reportValuation {n m : ℕ} (v : Reports ℝ n m) :
    AdditiveValuation (Fin n) (Fin m) :=
  ⟨fun i => (v i).weight⟩

/-- True bundle utility without transfers. -/
noncomputable def utility {n m : ℕ} (v : Reports ℝ n m) (i : Fin n) (a : Owners n m) : ℝ :=
  (reportValuation v).toValuation.val i (allocationOfOwners a i)

/-- MMS is computed on all m goods and n bundles even for partial outputs. The inequality
handles zero MMS without division. -/
noncomputable def IsFair {n m : ℕ} (_hn : 0 < n) (α : ℝ)
    (v : Reports ℝ n m) (a : Owners n m) : Prop :=
  IsAlphaMMS α (reportValuation v).toValuation Finset.univ
    (allocationOfOwners a)

/-- A mechanism fixed before the report profile. -/
abbrev DeterministicMechanism (n m : ℕ) := Reports ℝ n m → Owners n m

/-- Dominant-strategy truthfulness against arbitrary opponent reports. -/
def IsTruthful {n m : ℕ} (f : DeterministicMechanism n m) : Prop :=
  ∀ v i fake,
    utility v i (f (Function.update v i fake)) ≤ utility v i (f v)

/-- Every lottery on the finite allocation space, with no rational or dyadic probability
restriction. -/
abbrev RandomizedMechanism (n m : ℕ) :=
  Reports ℝ n m → Lottery ℝ (Owners n m)

/-- TIE averages only over the mechanism's internal randomness. -/
noncomputable def IsTIE {n m : ℕ} (f : RandomizedMechanism n m) : Prop :=
  ∀ v i fake,
    Lottery.expectedValue (f (Function.update v i fake)) (utility v i) ≤
      Lottery.expectedValue (f v) (utility v i)

/-- Fairness for every positive-probability realized allocation, not just expected
utility. Zero-probability outcomes impose no condition. -/
noncomputable def HasExPostMMS {n m : ℕ} (hn : 0 < n) (α : ℝ)
    (v : Reports ℝ n m) (law : Lottery ℝ (Owners n m)) : Prop :=
  ∀ a, 0 < law.val a → IsComplete a ∧ IsFair hn α v a

/-- The factor depends on n, not on m or the valuation profile. -/
def IsAdmissibleFactor (factor : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → 0 ≤ factor n ∧ factor n ≤ 1

/-- Complete MMS allocations, without incentives or runtime constraints. -/
noncomputable def MMSExistenceGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ n (hn : 0 < n) m (v : Reports ℝ n m),
    ∃ a, IsComplete a ∧ IsFair hn (factor n) v a

/-- A truthful mechanism per market, permitting partial allocations and without
non-bossiness or neutrality. -/
noncomputable def DeterministicTruthfulGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ n (hn : 0 < n) m, ∃ f : DeterministicMechanism n m,
    IsTruthful f ∧ ∀ v, IsFair hn (factor n) v (f v)

/-- Full-real TIE with complete ex-post fair allocations. -/
noncomputable def RandomizedTIEGuarantee (factor : ℕ → ℝ) : Prop :=
  ∀ n (hn : 0 < n) m, ∃ f : RandomizedMechanism n m,
    IsTIE f ∧ ∀ v, HasExPostMMS hn (factor n) v (f v)

/-- Pointwise supremal factors. Attainment by one uniform algorithm is a separate
requirement. -/
def IsSupremalFactor (guarantee : (ℕ → ℝ) → Prop) (factor : ℕ → ℝ) : Prop :=
  IsAdmissibleFactor factor ∧
    (∀ other, IsAdmissibleFactor other → guarantee other →
      ∀ n, 0 < n → other n ≤ factor n) ∧
    ∀ n, 0 < n → ∀ ε : ℝ, 0 < ε →
      ∃ other, IsAdmissibleFactor other ∧ guarantee other ∧ factor n - ε < other n

/-- Distinguish a supremum from an attained endpoint, notably for FPTAS results. -/
inductive FactorEndpoint
  | supremum
  | attained
  deriving DecidableEq

/-- A proposed factor is the answer parameter. Merely naming the defining supremum does
not identify the requested mathematical value. -/
def FactorQuestion (endpoint : FactorEndpoint)
    (guarantee : (ℕ → ℝ) → Prop) (factor : ℕ → ℝ) : Prop :=
  match endpoint with
  | .supremum => IsSupremalFactor guarantee factor
  | .attained => IsSupremalFactor guarantee factor ∧ guarantee factor

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


section

/-!
## Rational-table Word-RAM specialization

This fixed representation is separate from the full-real semantic questions. The input
contains singleton values; output contains owner labels. No answer is embedded in the
encoding and no unary value padding is used.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open WordRAM.FiniteData

/-- Interpret one rational singleton table exactly over the reals. -/
noncomputable def realReport {m : ℕ} (v : AdditiveReport ℚ m) : AdditiveReport ℝ m :=
  { weight := fun g => (v.weight g : ℝ)
    nonnegative := fun g => by exact_mod_cast v.nonnegative g }

/-- Interpret rational reports exactly as real reports. -/
noncomputable def realReports {n m : ℕ} (v : Reports ℚ n m) : Reports ℝ n m :=
  fun i => realReport (v i)

/-- Positive agent count, allowing no goods and zero-valued goods. -/
structure RationalInput where
  agents : ℕ
  agents_pos : 0 < agents
  goods : ℕ
  reports : Reports ℚ agents goods

/-- The fixed singleton table, without hidden unary padding. -/
def inputCode (I : RationalInput) : Code :=
  tableCode ([Atom.integer (Int.ofNat I.agents), Atom.integer (Int.ofNat I.goods)] ++
    (List.ofFn fun i : Fin I.agents =>
      List.ofFn fun g : Fin I.goods => Atom.rational ((I.reports i).weight g)).flatten)

/-- Owner labels are bounded by n; invalid labels have no representation witness. -/
def ownerCode {n m : ℕ} (a : Owners n m) : Code :=
  tableCode ([Atom.integer (Int.ofNat n), Atom.integer (Int.ofNat m)] ++
    List.ofFn fun g : Fin m => Atom.integer (Int.ofNat
      (match a g with | none => 0 | some i => i.val + 1)))

/-- A mechanism on every rational report, not just reports as short as the true input. Its
probabilities are not restricted to a bounded tape. -/
abbrev RationalRandomizedMechanism (n m : ℕ) :=
  Reports ℚ n m → Lottery ℝ (Owners n m)

/-- Restrict the same real mechanism, rather than choosing an unrelated rational one. -/
noncomputable def rationalRestriction {n m : ℕ} (f : RandomizedMechanism n m) :
    RationalRandomizedMechanism n m :=
  fun v => f (realReports v)

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


section

/-!
## Exact sampling without a deterministic tape-length cap

A bounded fair-bit tape only produces dyadic probabilities. This model instead permits
almost-sure termination with expected or uniformly bounded almost-sure runtime,
explicitly distinguished. Output and cost come from the same Interaction execution;
one allocation is sampled.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open WordRAM.FiniteData
open MeasureTheory

abbrev RandomTape := ℕ → Bool

/-- The fair-bit product law is constrained on every finite cylinder. It cannot contain
hidden advice; the final witness also requires existence. -/
structure FairBitLaw where
  measure : Measure RandomTape
  probability : IsProbabilityMeasure measure
  prefix_uniform : ∀ (k : ℕ) (bits : Fin k → Bool),
    measure {t | ∀ j : Fin k, t j.val = bits j} = ((2 : ENNReal) ^ k)⁻¹

/-- Read the next fair bit at the interpreter-managed cursor. No real seed or finite tape
length is made available as input. -/
def tapeEnvironment (t : RandomTape) : WordRAM.Interaction.Environment Empty :=
  WordRAM.Interaction.randomOnly (fun k => some (t k))

structure RandomizedSimulator where
  model : WordRAM.Model
  program : WordRAM.Interaction.Program Empty

inductive RuntimeConvention
  | expected
  | uniformAlmostSure
  deriving DecidableEq

/-- The finite owner-vector space has the discrete measurable structure. -/
local instance ownersMeasurable (n m : ℕ) : MeasurableSpace (Owners n m) := ⊤

/-- One program produces each output. Fuel only observes termination; correct decoding and
agreement with the target law hold almost surely. -/
structure RandomizedImplementation (S : RandomizedSimulator) (L : FairBitLaw)
    (mechanism : (n m : ℕ) → RationalRandomizedMechanism n m) where
  fuel : RationalInput → RandomTape → ℕ
  output : (I : RationalInput) → RandomTape → Owners I.agents I.goods
  output_measurable : ∀ I, Measurable (output I)
  halts : ∀ I, ∀ᵐ t ∂L.measure,
    (WordRAM.Interaction.run S.model (tapeEnvironment t) S.program (fuel I t)
      (inputCode I)).termination = .halted (words (ownerCode (output I t)))
  realizes : ∀ I a,
    L.measure {t | output I t = a} =
      ENNReal.ofReal ((mechanism I.agents I.goods I.reports).val a)

/-- Cost of the same interpreter execution that produces the allocation. -/
def RandomizedImplementation.cost
    {S : RandomizedSimulator} {L : FairBitLaw}
    {mechanism : (n m : ℕ) → RationalRandomizedMechanism n m}
    (W : RandomizedImplementation S L mechanism) (I : RationalInput)
    (t : RandomTape) : ℕ :=
  (WordRAM.Interaction.run S.model (tapeEnvironment t) S.program (W.fuel I t)
    (inputCode I)).cost

/-- Expected runtime requires integrability; a nonintegrable Bochner integral cannot be
treated as zero runtime. -/
noncomputable def RandomizedImplementation.Within
    {S : RandomizedSimulator} {L : FairBitLaw}
    {mechanism : (n m : ℕ) → RationalRandomizedMechanism n m}
    (W : RandomizedImplementation S L mechanism) (mode : RuntimeConvention)
    (I : RationalInput) (bound : ℕ) : Prop :=
  match mode with
  | .expected =>
      Integrable (fun t => (W.cost I t : ℝ)) L.measure ∧
        (∫ t, (W.cost I t : ℝ) ∂L.measure) ≤ (bound : ℝ)
  | .uniformAlmostSure => ∀ᵐ t ∂L.measure, W.cost I t ≤ bound

/-- A uniform polynomial budget in fixed input-code size, using StrictCostCore. -/
noncomputable def RandomizedImplementation.IsPolynomialTime
    {S : RandomizedSimulator} {L : FairBitLaw}
    {mechanism : (n m : ℕ) → RationalRandomizedMechanism n m}
    (W : RandomizedImplementation S L mechanism) (mode : RuntimeConvention) : Prop :=
  ∃ bound : RationalInput → ℕ,
    WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
      (fun I => bitSize S.model (inputCode I)) bound ∧
      ∀ I, W.Within mode I (bound I)

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


section

/-!
## Real correctness with a declared finite implementation domain

The mechanism family is TIE and ex-post fair on all real reports. A fixed presentation
determines which inputs are implemented. The fair-bit sampler returns one allocation,
and its output law and runtime refer to the same run.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open WordRAM.FiniteData MeasureTheory

structure RealMMSInput where
  agents : ℕ
  agents_pos : 0 < agents
  goods : ℕ
  reports : Reports ℝ agents goods

abbrev PackedOwners := Σ n : ℕ, Σ m : ℕ, Owners n m

def IsRealMMSSolution (factor : ℕ → ℝ) (I : RealMMSInput) (output : PackedOwners) : Prop :=
  ∃ a : Owners I.agents I.goods,
    output = ⟨I.agents, I.goods, a⟩ ∧ IsComplete a ∧
      IsFair I.agents_pos (factor I.agents) I.reports a

noncomputable def IsRealTIEFamily (factor : ℕ → ℝ)
    (M : (n m : ℕ) → RandomizedMechanism n m) : Prop :=
  ∀ n (hn : 0 < n) m,
    IsTIE (M n m) ∧ ∀ v, HasExPostMMS hn (factor n) v (M n m v)

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


section

/-!
## Canonical rational execution of full-real MMS specifications

The economic selector or mechanism is correct on every real instance. One fixed
program implements its restriction to every nonnegative rational table. Input and
output codes are the structural inputCode and ownerCode; there is no chosen decoder,
presentation, input promise, or hidden solution advice. The source distinguishes
real-valued economic types from finite reported data [BFM 2026, Sections 1.2 and 2];
this section fixes the explicit rational singleton-table specialization.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open WordRAM.FiniteData

/-- Every rational input has its exact full-real economic interpretation. -/
noncomputable def RationalInput.toReal (I : RationalInput) : RealMMSInput where
  agents := I.agents
  agents_pos := I.agents_pos
  goods := I.goods
  reports := realReports I.reports

/-- A uniform interpreter implementation of the same selector on every rational input. The
output is forced to be its canonical owner code. Fuel and the proof-level output
witness are not accessible machine inputs. -/
structure CanonicalMMSImplementation (solve : RealMMSInput → PackedOwners) where
  model : WordRAM.Model
  program : WordRAM.Program
  fuel : RationalInput → ℕ
  output : (I : RationalInput) → Owners I.agents I.goods
  halts : ∀ I,
    (WordRAM.Search.execution model program (fuel I) (inputCode I)).termination =
      .halted (words (ownerCode (output I)))
  realizes : ∀ I, solve I.toReal = ⟨I.agents, I.goods, output I⟩

/-- The cost is read from the same execution that produces the owner vector. -/
def CanonicalMMSImplementation.cost {solve : RealMMSInput → PackedOwners}
    (W : CanonicalMMSImplementation solve) (I : RationalInput) : ℕ :=
  (WordRAM.Search.execution W.model W.program (W.fuel I) (inputCode I)).cost

/-- Uniform polynomial complexity in the fixed rational singleton-table code. -/
def CanonicalMMSImplementation.IsPolynomialTime {solve : RealMMSInput → PackedOwners}
    (W : CanonicalMMSImplementation solve) : Prop :=
  WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial
    (fun I => bitSize W.model (inputCode I)) W.cost

/-- Full-real complete MMS existence with canonical execution of the same selector on all
rational inputs. -/
def RealMMSCanonicalRationalGuarantee (factor : ℕ → ℝ) : Prop :=
  ∃ solve : RealMMSInput → PackedOwners,
    (∀ I, IsRealMMSSolution factor I (solve I)) ∧
      ∃ W : CanonicalMMSImplementation solve, W.IsPolynomialTime

/-- Every real TIE mechanism is restricted to rational reports by exact casting. -/
noncomputable def restrictRealFamily
    (M : (n m : ℕ) → RandomizedMechanism n m) :
    (n m : ℕ) → RationalRandomizedMechanism n m :=
  fun n m => rationalRestriction (M n m)

/-- Full-real TIE and ex-post fairness with an exact canonical sampler on all rational
tables. The single program and fair-bit law precede every input. -/
noncomputable def RealTIECanonicalRationalGuarantee
    (mode : RuntimeConvention) (factor : ℕ → ℝ) : Prop :=
  ∃ M : (n m : ℕ) → RandomizedMechanism n m,
    IsRealTIEFamily factor M ∧
      ∃ L : FairBitLaw, ∃ S : RandomizedSimulator,
        ∃ W : RandomizedImplementation S L (restrictRealFamily M),
          W.IsPolynomialTime mode

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


section

/-!
## Independent factor-identification questions

Each target checks a proposed factor(n), with supremum and attainment separated. The
adopted defaults are supremum and expected sampler runtime. The efficient
represented-domain variants do not claim to encode all reals. The nonalgorithmic
branches retain all real reports, and progress in one branch does not require solving
the others. The canonical rational-implementation questions have no caller-chosen
presentation or decoder.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

/-- OP1: complete MMS existence on every nonnegative-real instance. -/
noncomputable def MMSExistenceQuestion
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint MMSExistenceGuarantee factor

/-- OP2a: deterministic truthful partial allocation, without a runtime bound. -/
noncomputable def DeterministicTruthfulMMSQuestion
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint DeterministicTruthfulGuarantee factor

/-- OP2b: exact TIE and complete ex-post MMS, without a runtime bound. -/
noncomputable def RandomizedTIEMMSQuestion
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint RandomizedTIEGuarantee factor

/-- Adopted endpoint convention: identify the supremal existence factor; attainment
remains a distinct question. -/
noncomputable def BestMMSExistenceFactorQuestion (factor : ℕ → ℝ) : Prop :=
  MMSExistenceQuestion .supremum factor

/-- Full-real existence with canonical execution on every rational singleton table. The
endpoint convention remains an independent choice. -/
noncomputable def RealMMSCanonicalRationalQuestion
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint RealMMSCanonicalRationalGuarantee factor

/-- Full-real TIE and ex-post fairness with canonical rational-input sampling. -/
noncomputable def RealTIECanonicalRationalQuestion
    (mode : RuntimeConvention) (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint (RealTIECanonicalRationalGuarantee mode) factor

/-- The efficient OP1 reference: no arbitrary presentation, decoder, or promise. Only
rational-input execution is asserted; real correctness remains global. -/
noncomputable def BestRealMMSCanonicalRationalFactorQuestion (factor : ℕ → ℝ) : Prop :=
  RealMMSCanonicalRationalQuestion .supremum factor

/-- The efficient randomized reference: exact one-allocation sampling in expected
polynomial time on every canonical rational input, with full-real TIE. -/
noncomputable def BestRealTIECanonicalRationalFactorQuestion (factor : ℕ → ℝ) : Prop :=
  RealTIECanonicalRationalQuestion .expected .supremum factor

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

/-- Supply the supremal factor as a function of the number of agents; attainment is
separate. -/
theorem bestMMSExistenceFactor :
    BestMMSExistenceFactorQuestion (answer(sorry)) := by
  sorry

/-- Full-real correctness with canonical rational-input execution. -/
theorem bestEfficientMMSFactor :
    BestRealMMSCanonicalRationalFactorQuestion (answer(sorry)) := by
  sorry

/-- Independent deterministic truthful factor. -/
theorem bestDeterministicTruthfulFactor :
    DeterministicTruthfulMMSQuestion .supremum (answer(sorry)) := by
  sorry

/-- Independent truthfulness-in-expectation factor without a runtime restriction. -/
theorem bestRandomizedTIEFactor :
    RandomizedTIEMMSQuestion .supremum (answer(sorry)) := by
  sorry

/-- Expected polynomial-time canonical rational sampling, with full-real TIE. -/
theorem bestEfficientTIEFactor :
    BestRealTIECanonicalRationalFactorQuestion (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
