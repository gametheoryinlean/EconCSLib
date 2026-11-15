/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.MMSApproximationAndTruthfulAllocation.Problem

/-!
# MMSApproximationAndTruthfulAllocation: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Rational-table Word-RAM specialization

This fixed representation is separate from the full-real semantic questions. The input
contains singleton values; output contains owner labels. No answer is embedded in the
encoding and no unary value padding is used.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness
open WordRAM.FiniteData

/-- Exact casting preserves unilateral misreports, including longer rational names. -/
theorem realReports_update {n m : ℕ} (v : Reports ℚ n m) (i : Fin n)
    (fake : AdditiveReport ℚ m) :
    realReports (Function.update v i fake) =
      Function.update (realReports v) i (realReport fake) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [realReports]
  · simp [realReports, Function.update_of_ne h]

/-- Well-formed nonnegative rational tables with their dimensions. -/
def IsValidInput (code : Code) : Prop := ∃ I : RationalInput, inputCode I = code

/-- The original complete MMS relation on the same input and owner code. -/
noncomputable def IsMMSSolution (factor : ℕ → ℝ) (input output : Code) : Prop :=
  ∃ I : RationalInput, inputCode I = input ∧
    ∃ a : Owners I.agents I.goods,
      ownerCode a = output ∧ IsComplete a ∧
        IsFair I.agents_pos (factor I.agents) (realReports I.reports) a

/-- One uniform bounded Word-RAM solver over all dimensions and rational reports. -/
noncomputable def RationalWordRAMMMSGuarantee (factor : ℕ → ℝ) : Prop :=
  WordRAM.Search.PolynomiallySolvable IsValidInput (IsMMSSolution factor)

/-- Truthful expected utility evaluated using true values, even for longer fake reports. -/
noncomputable def IsRationalTIE {n m : ℕ} (f : RationalRandomizedMechanism n m) : Prop :=
  ∀ v i fake,
    Lottery.expectedValue (f (Function.update v i fake)) (utility (realReports v) i) ≤
      Lottery.expectedValue (f v) (utility (realReports v) i)

/-- Full-real truthfulness includes every rational unilateral deviation. -/
theorem IsTIE.rational_restriction {n m : ℕ} {f : RandomizedMechanism n m}
    (hf : IsTIE f) : IsRationalTIE (rationalRestriction f) := by
  intro v i fake
  simpa only [rationalRestriction, realReports_update] using
    hf (realReports v) i (realReport fake)

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

/-- An exact rational-input sampler with one mechanism family, fair-bit law and program
for all instances. Neither TIE nor ex-post MMS is relaxed. -/
noncomputable def RationalWordRAMTIEGuarantee
    (mode : RuntimeConvention) (factor : ℕ → ℝ) : Prop :=
  ∃ mechanism : (n m : ℕ) → RationalRandomizedMechanism n m,
    (∀ n (hn : 0 < n) m,
      IsRationalTIE (mechanism n m) ∧
        ∀ v, HasExPostMMS hn (factor n) (realReports v) (mechanism n m v)) ∧
    ∃ L : FairBitLaw, ∃ S : RandomizedSimulator,
      ∃ W : RandomizedImplementation S L mechanism, W.IsPolynomialTime mode

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

/-- Full-real correctness and actual runtime only on the chosen presentation. -/
def RealMMSWithPresentedImplementationGuarantee
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (factor : ℕ → ℝ) : Prop :=
  ∃ solve : RealMMSInput → PackedOwners,
    (∀ I, IsRealMMSSolution factor I (solve I)) ∧
    ∃ W : ExecutionContracts.Realization P (fun _ => True) solve,
      W.IsPolynomialTime

local instance realOwnersMeasurable (n m : ℕ) : MeasurableSpace (Owners n m) := ⊤

/-- The sampler's actual law realizes the full-real mechanism family on represented
inputs. Fuel and cost are not accessible advice. -/
structure RealPresentedSampler
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (S : RandomizedSimulator) (L : FairBitLaw)
    (M : (n m : ℕ) → RandomizedMechanism n m) where
  fuel : Code → RandomTape → ℕ
  output : (I : RealMMSInput) → Code → RandomTape → Owners I.agents I.goods
  output_measurable : ∀ I code, Measurable (output I code)
  halts : ∀ I code, P.decodeInput code = some I → ∀ᵐ t ∂L.measure,
    ∃ outputCode,
      (WordRAM.Interaction.run S.model (tapeEnvironment t) S.program
        (fuel code t) code).termination = .halted (words outputCode) ∧
      P.decodeOutput outputCode = some ⟨I.agents, I.goods, output I code t⟩
  realizes : ∀ I code, P.decodeInput code = some I → ∀ a,
    L.measure {t | output I code t = a} =
      ENNReal.ofReal ((M I.agents I.goods I.reports).val a)

def RealPresentedSampler.cost
    {P : ExecutionContracts.Presentation RealMMSInput PackedOwners}
    {S : RandomizedSimulator} {L : FairBitLaw}
    {M : (n m : ℕ) → RandomizedMechanism n m}
    (W : RealPresentedSampler P S L M) (code : Code) (t : RandomTape) : ℕ :=
  (WordRAM.Interaction.run S.model (tapeEnvironment t) S.program (W.fuel code t) code).cost

noncomputable def RealPresentedSampler.Within
    {P : ExecutionContracts.Presentation RealMMSInput PackedOwners}
    {S : RandomizedSimulator} {L : FairBitLaw}
    {M : (n m : ℕ) → RandomizedMechanism n m}
    (W : RealPresentedSampler P S L M) (mode : RuntimeConvention)
    (code : Code) (bound : ℕ) : Prop :=
  match mode with
  | .expected =>
      Integrable (fun t => (W.cost code t : ℝ)) L.measure ∧
        (∫ t, (W.cost code t : ℝ) ∂L.measure) ≤ (bound : ℝ)
  | .uniformAlmostSure => ∀ᵐ t ∂L.measure, W.cost code t ≤ bound

noncomputable def RealTIEWithPresentedSamplerGuarantee
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (mode : RuntimeConvention) (factor : ℕ → ℝ) : Prop :=
  ∃ M : (n m : ℕ) → RandomizedMechanism n m,
    IsRealTIEFamily factor M ∧
    ∃ L : FairBitLaw, ∃ S : RandomizedSimulator,
    ∃ W : RealPresentedSampler P S L M, ∃ bound : Code → ℕ,
      WordRAM.StrictCostCore.IsEventuallyBoundedByPolynomial (bitSize S.model) bound ∧
        ∀ code I, P.decodeInput code = some I → W.Within mode code (bound code)

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

/-- The canonical implementation question retains the original full-real existence
requirement, without proving any optimal factor. -/
theorem RealMMSCanonicalRationalGuarantee.semantic {factor : ℕ → ℝ}
    (h : RealMMSCanonicalRationalGuarantee factor) : MMSExistenceGuarantee factor := by
  obtain ⟨solve, hsolve, _⟩ := h
  intro n hn m v
  obtain ⟨a, _, ha⟩ := hsolve ⟨n, hn, m, v⟩
  exact ⟨a, ha⟩

/-- Correctness transfers to the owner vector actually emitted by the machine. -/
theorem CanonicalMMSImplementation.output_correct
    {factor : ℕ → ℝ} {solve : RealMMSInput → PackedOwners}
    (W : CanonicalMMSImplementation solve)
    (hsolve : ∀ I, IsRealMMSSolution factor I (solve I)) (I : RationalInput) :
    IsComplete (W.output I) ∧
      IsFair I.agents_pos (factor I.agents) (realReports I.reports) (W.output I) := by
  obtain ⟨a, ha, hcomplete, hfair⟩ := hsolve I.toReal
  rw [W.realizes I] at ha
  have hout : W.output I = a :=
    eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj ha).2)).2
  simpa only [hout] using And.intro hcomplete hfair

/-- Convert the canonical all-input witness to the existing rational search interface.
Classical choice selects only simulation fuel, never machine output. -/
noncomputable def CanonicalMMSImplementation.toRationalSolver
    {factor : ℕ → ℝ} {solve : RealMMSInput → PackedOwners}
    (W : CanonicalMMSImplementation solve)
    (hsolve : ∀ I, IsRealMMSSolution factor I (solve I)) :
    WordRAM.Search.Solver W.model IsValidInput (IsMMSSolution factor) := by
  classical
  exact
    { program := W.program
      fuel := fun code => if h : IsValidInput code then W.fuel (Classical.choose h) else 0
      correct := by
        intro code hcode
        let I : RationalInput := Classical.choose hcode
        have hi : inputCode I = code := Classical.choose_spec hcode
        refine ⟨ownerCode (W.output I), ?_, I, hi, W.output I, rfl,
          W.output_correct hsolve I⟩
        simpa only [dif_pos hcode, hi] using W.halts I }

/-- The rational search adapter preserves the actual execution-cost bound. -/
theorem CanonicalMMSImplementation.toRationalSolver_isPolynomialTime
    {factor : ℕ → ℝ} {solve : RealMMSInput → PackedOwners}
    (W : CanonicalMMSImplementation solve)
    (hsolve : ∀ I, IsRealMMSSolution factor I (solve I))
    (hW : W.IsPolynomialTime) : (W.toRationalSolver hsolve).IsPolynomialTime := by
  classical
  obtain ⟨coefficient, hc, exponent, threshold, hbound⟩ := hW
  refine ⟨coefficient, hc, exponent, threshold, ?_⟩
  intro code hsize
  let I : RationalInput := Classical.choose code.property
  have hi : inputCode I = code.val := Classical.choose_spec code.property
  have hI := hbound I (by simpa only [hi] using hsize)
  simpa only [toRationalSolver, dif_pos code.property, cost, hi] using hI

/-- The canonical full-real specification implies its rational Word-RAM specialization,
with the same program and without a decoder assumption. -/
theorem RealMMSCanonicalRationalGuarantee.rational {factor : ℕ → ℝ}
    (h : RealMMSCanonicalRationalGuarantee factor) :
    RationalWordRAMMMSGuarantee factor := by
  obtain ⟨solve, hsolve, W, hW⟩ := h
  exact ⟨W.model, W.toRationalSolver hsolve,
    W.toRationalSolver_isPolynomialTime hsolve hW⟩

/-- The economic mechanism remains truthful and fair on all real reports. -/
theorem RealTIECanonicalRationalGuarantee.semantic
    {mode : RuntimeConvention} {factor : ℕ → ℝ}
    (h : RealTIECanonicalRationalGuarantee mode factor) :
    RandomizedTIEGuarantee factor := by
  obtain ⟨M, hM, _⟩ := h
  intro n hn m
  exact ⟨M n m, hM n hn m⟩

/-- The same sampler is a valid implementation of the rational TIE question. -/
theorem RealTIECanonicalRationalGuarantee.rational
    {mode : RuntimeConvention} {factor : ℕ → ℝ}
    (h : RealTIECanonicalRationalGuarantee mode factor) :
    RationalWordRAMTIEGuarantee mode factor := by
  obtain ⟨M, hM, L, S, W, hW⟩ := h
  refine ⟨restrictRealFamily M, ?_, L, S, W, hW⟩
  intro n hn m
  refine ⟨(hM n hn m).1.rational_restriction, ?_⟩
  intro v
  exact (hM n hn m).2 (realReports v)

/-- Every positive-probability output of the actual sampler is complete and MMS-fair;
correctness is not confined to an unrelated abstract lottery. -/
theorem canonical_sampler_output_fair
    {factor : ℕ → ℝ} {M : (n m : ℕ) → RandomizedMechanism n m}
    (hM : IsRealTIEFamily factor M) {S : RandomizedSimulator} {L : FairBitLaw}
    (W : RandomizedImplementation S L (restrictRealFamily M))
    (I : RationalInput) (a : Owners I.agents I.goods)
    (ha : 0 < L.measure {t | W.output I t = a}) :
    IsComplete a ∧
      IsFair I.agents_pos (factor I.agents) (realReports I.reports) a := by
  apply (hM I.agents I.agents_pos I.goods).2 (realReports I.reports) a
  rw [W.realizes I a] at ha
  exact ENNReal.ofReal_pos.mp ha

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

/-- The rational-table polynomial-time specialization of OP1. -/
noncomputable def RationalPolynomialMMSQuestion
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint RationalWordRAMMMSGuarantee factor

/-- The rational sampler specialization with an explicit runtime convention. -/
noncomputable def RationalPolynomialTIEMMSQuestion
    (mode : RuntimeConvention) (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint (RationalWordRAMTIEGuarantee mode) factor

/-- Real correctness with implementation only on the declared presentation; no finite
representation of all real inputs is asserted. -/
noncomputable def RealMMSWithPresentedImplementationQuestion
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint (RealMMSWithPresentedImplementationGuarantee P) factor

noncomputable def RealTIEWithPresentedSamplerQuestion
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (mode : RuntimeConvention) (endpoint : FactorEndpoint) (factor : ℕ → ℝ) : Prop :=
  FactorQuestion endpoint (RealTIEWithPresentedSamplerGuarantee P mode) factor

/-- Conditional presented-domain convention, retained for explicit adapters. -/
noncomputable def BestRealTIEPresentedFactorQuestion
    (P : ExecutionContracts.Presentation RealMMSInput PackedOwners)
    (factor : ℕ → ℝ) : Prop :=
  RealTIEWithPresentedSamplerQuestion P .expected .supremum factor

end EconCSLib.OpenProblem.New.EconCSBench.MMSApproximationTruthfulness

end
