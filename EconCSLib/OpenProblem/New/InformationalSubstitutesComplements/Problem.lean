/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.New.Complexity.All
import EconCSLib.OpenProblem.Util.Answer
import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Option
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# 09. Informational substitutes and complements
-/



section

/-!
## Information values and six substitute/complement properties

Chen--Waggoner (arXiv:1703.08636), Definitions 2.2.2--2.2.3, quantify A and B over
whole-signal subsets; only the intermediate disclosure is generalized. Submodularity
on the entire disclosure lattice would be stronger (footnote 4). The strong properties
include arbitrary report spaces. Posterior laws use Radon--Nikodym derivatives;
zero-mass observations do not affect expectations. The measure-theoretic formulas are
specifications.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements


universe uSignalIndex uSignal

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- A real vector is a probability distribution on a finite state space. -/
def IsProbabilityVector
    {State : Type*} [Fintype State] (p : State → ℝ) : Prop :=
  (∀ e, 0 ≤ p e) ∧ ∑ e, p e = 1

/-- Two total Lean functions represent the same expected-score function on the
mathematical domain `Δ(State)` when they agree on every probability vector. -/
def ScoresAgreeOnSimplex
    {State : Type*} [Fintype State]
    (first second : (State → ℝ) → ℝ) : Prop :=
  ∀ p, IsProbabilityVector p → first p = second p

/-- Expected-score functions restricted to their mathematical domain, the finite
probability simplex. -/
abbrev SimplexExpectedScore (State : Type*) [Fintype State] :=
  {p : State → ℝ // IsProbabilityVector p} → ℝ

/-- A finite information source and a finite convex score on the simplex. Off-simplex
values only totalize formulas at null observations. No smoothness, strict convexity,
full support or independence is assumed. -/
structure FiniteBayesianInformation
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  /-- Joint prior on the state and all base-signal realizations. -/
  jointPrior : Lottery ℝ (State × (∀ i, Signal i))
  /-- Expected optimal score as a function of a posterior vector. -/
  score : (State → ℝ) → ℝ
  /-- Convexity of the score function. -/
  score_convex :
    ∀ p q : State → ℝ,
      IsProbabilityVector p → IsProbabilityVector q →
      ∀ weight : ℝ, 0 ≤ weight → weight ≤ 1 →
      score (fun e => weight * p e + (1 - weight) * q e) ≤
        weight * score p + (1 - weight) * score q
/-- Full profile of base-signal realizations. -/
abbrev SignalProfile
    (SignalIndex : Type*) (Signal : SignalIndex → Type*) :=
  ∀ i, Signal i

/-- Two signal profiles reveal the same realization on a chosen subset. -/
def SameOn
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    (S : Finset SignalIndex)
    (a b : SignalProfile SignalIndex Signal) : Prop :=
  ∀ i, i ∈ S → a i = b i

/-- Probability of the partial observation represented by `a` on `S`. -/
noncomputable def observationProbability
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (S : Finset SignalIndex) (a : SignalProfile SignalIndex Signal) : ℝ := by
  classical
  exact ∑ e, ∑ b, if SameOn S a b then source.jointPrior.val (e, b) else 0

/-- Posterior on the state after observing the selected base signals. A zero-probability
observation uses Lean's total division convention, but its term in the outer
expectation has zero weight. -/
noncomputable def posterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (S : Finset SignalIndex) (a : SignalProfile SignalIndex Signal)
    (e : State) : ℝ := by
  classical
  exact
    (∑ b, if SameOn S a b then source.jointPrior.val (e, b) else 0) /
      observationProbability source S a

/-- Marginal probability of a full signal profile. -/
noncomputable def signalProfileProbability
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (a : SignalProfile SignalIndex Signal) : ℝ :=
  ∑ e, source.jointPrior.val (e, a)

/-- The induced value `E[G(P(State | A_S))]` of a subset of whole base signals. Summing
over full profiles is valid because profiles agreeing on `S` induce the same posterior
and their masses aggregate. -/
noncomputable def weakSignalValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (S : Finset SignalIndex) : ℝ :=
  ∑ a, signalProfileProbability source a * source.score (posterior source S a)

/-- Diminishing marginal value on a disclosure lattice, in the exact lattice form used for
informational substitutes. -/
def IsLatticeSubmodular
    {L : Type*} [Lattice L] (value : L → ℝ) : Prop :=
  ∀ A' A B, A ⊓ B ≤ A' → A' ≤ A →
    value (B ⊔ A) - value A ≤ value (B ⊔ A') - value A'

/-- Increasing marginal value on a disclosure lattice. -/
def IsLatticeSupermodular
    {L : Type*} [Lattice L] (value : L → ℝ) : Prop :=
  ∀ A' A B, A ⊓ B ≤ A' → A' ≤ A →
    value (B ⊔ A') - value A' ≤ value (B ⊔ A) - value A

/-- A finite-output randomized partial disclosure (garbling) of the complete finite signal
profile. This is sufficient for deterministic summaries in the moderate notion, and
remains useful for finite certificates, but the strong notion below uses
`GeneralSignalDisclosure` instead. -/
structure SignalDisclosure
    (SignalIndex : Type uSignalIndex)
    (Signal : SignalIndex → Type uSignal)
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  Output : Type (max uSignalIndex uSignal)
  [outputFintype : Fintype Output]
  [outputDecidableEq : DecidableEq Output]
  kernel :
    SignalProfile SignalIndex Signal →
      Lottery ℝ Output

attribute [instance] SignalDisclosure.outputFintype
  SignalDisclosure.outputDecidableEq

/-- An arbitrary randomized partial disclosure of the complete finite signal profile. The
report space may be infinite or continuous (for example a noisy real-valued report),
and `kernel input` is its conditional probability law.

The source alphabet is finite, so it is enough to store the family of output measures
directly; no extra measurability condition in the source argument is needed. This is
the disclosure class quantified over by strong substitutes and complements in
Chen--Waggoner's continuous signal lattice. -/
structure GeneralSignalDisclosure
    (SignalIndex : Type uSignalIndex)
    (Signal : SignalIndex → Type uSignal)
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  Output : Type (max uSignalIndex uSignal)
  [outputMeasurableSpace : MeasurableSpace Output]
  kernel : SignalProfile SignalIndex Signal → Measure Output
  kernel_isProbability : ∀ input, IsProbabilityMeasure (kernel input)

attribute [instance] GeneralSignalDisclosure.outputMeasurableSpace

/-- Blackwell order for arbitrary-output disclosures: `less ≼ more` when a Markov
post-processing of `more` produces exactly the conditional law of `less` for every
source realization. -/
def IsGeneralBlackwellBelow
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (less more : GeneralSignalDisclosure SignalIndex Signal) : Prop :=
  ∃ garbling : Kernel more.Output less.Output,
    IsMarkovKernel garbling ∧
      ∀ input,
        less.kernel input = garbling ∘ₘ more.kernel input

/-- A deterministic summary is a point-mass disclosure for every input. -/
def SignalDisclosure.IsDeterministic
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (disclosure : SignalDisclosure SignalIndex Signal) : Prop :=
  ∃ summary : SignalProfile SignalIndex Signal →
      disclosure.Output,
    ∀ input,
      disclosure.kernel input = Lottery.pure (𝕜 := ℝ) (summary input)

/-- Blackwell order: `less ≤ more` when `less` is obtained by a stochastic post-processing
of `more`. -/
def IsBlackwellBelow
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (less more : SignalDisclosure SignalIndex Signal) : Prop :=
  ∃ garbling :
      more.Output → Lottery ℝ less.Output,
    ∀ input (output : less.Output),
      (less.kernel input).val output =
        ∑ middle : more.Output,
          (more.kernel input).val middle *
            (garbling middle).val output

/-- Source-relative Blackwell order on Chen--Waggoner's support `Γ`. Null signal profiles
impose no constraints on a disclosure. -/
def IsBlackwellBelowOn
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (less more : SignalDisclosure SignalIndex Signal) : Prop :=
  ∃ garbling : more.Output → Lottery ℝ less.Output,
    ∀ input, 0 < signalProfileProbability source input →
      ∀ output : less.Output,
        (less.kernel input).val output =
          ∑ middle : more.Output,
            (more.kernel input).val middle * (garbling middle).val output

/-- General-output Blackwell order relative to the positive-probability signal profiles,
not to unused Cartesian-product assignments. -/
def IsGeneralBlackwellBelowOn
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (less more : GeneralSignalDisclosure SignalIndex Signal) : Prop :=
  ∃ garbling : Kernel more.Output less.Output,
    IsMarkovKernel garbling ∧
      ∀ input, 0 < signalProfileProbability source input →
        less.kernel input = garbling ∘ₘ more.kernel input

/-- Deterministic summaries are required to be point masses only on `Γ`. The total kernel
outside the prior's support has no informational meaning. -/
def SignalDisclosure.IsDeterministicOn
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal) : Prop :=
  ∃ summary : SignalProfile SignalIndex Signal → disclosure.Output,
    ∀ input, 0 < signalProfileProbability source input →
      disclosure.kernel input = Lottery.pure (𝕜 := ℝ) (summary input)

/-- Canonical output profile that records exactly the signals in `S` and uses fixed dummy
values outside `S`. -/
noncomputable def maskedSignalProfile
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Nonempty (Signal i)]
    (S : Finset SignalIndex)
    (input : SignalProfile SignalIndex Signal) :
    SignalProfile SignalIndex Signal :=
  fun i =>
    if i ∈ S then input i
    else Classical.choice (inferInstance : Nonempty (Signal i))

/-- Deterministic disclosure of a collection of whole base signals. -/
noncomputable def wholeSignalDisclosure
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (S : Finset SignalIndex) :
    SignalDisclosure SignalIndex Signal := by
  classical
  exact
    { Output := SignalProfile SignalIndex Signal
      kernel := fun input =>
        Lottery.pure (𝕜 := ℝ) (maskedSignalProfile S input) }

/-- Whole-signal disclosure embedded in the arbitrary-output kernel model. The maximal
measurable structure is the discrete measurable structure on this finite output type. -/
noncomputable def generalWholeSignalDisclosure
    {SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (S : Finset SignalIndex) :
    GeneralSignalDisclosure SignalIndex Signal := by
  classical
  letI : MeasurableSpace (SignalProfile SignalIndex Signal) := ⊤
  exact
    { Output := SignalProfile SignalIndex Signal
      outputMeasurableSpace := inferInstance
      kernel := fun input => Measure.dirac (maskedSignalProfile S input)
      kernel_isProbability := fun _ => inferInstance }

/-- Output measure generated jointly by state `e`, the prior on finite signal profiles,
and an arbitrary-output disclosure kernel. -/
noncomputable def generalDisclosureStateMeasure
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (e : State) : Measure disclosure.Output := by
  classical
  exact ∑ input,
    ENNReal.ofReal (source.jointPrior.val (e, input)) •
      disclosure.kernel input

/-- Marginal output law of an arbitrary-output disclosure. -/
noncomputable def generalDisclosureMeasure
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) :
    Measure disclosure.Output :=
  ∑ e, generalDisclosureStateMeasure source disclosure e

/-- Posterior probability of state `e` at an arbitrary disclosure output, represented by
the Radon--Nikodym derivative of its state-output measure with respect to the marginal
output law. -/
noncomputable def generalDisclosurePosterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (output : disclosure.Output) (e : State) : ℝ :=
  ((generalDisclosureStateMeasure source disclosure e).rnDeriv
      (generalDisclosureMeasure source disclosure) output).toReal

/-- Expected score of an arbitrary-output disclosure. This Bochner integral specializes to
the finite sum in `disclosureValue` for finite report spaces. -/
noncomputable def generalDisclosureValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) : ℝ :=
  ∫ output,
    source.score (generalDisclosurePosterior source disclosure output)
      ∂generalDisclosureMeasure source disclosure

/-- State-output measure after additionally fixing the observed whole-signal profile on
`B`. -/
noncomputable def generalDisclosureWithWholeStateMeasure
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (observed : SignalProfile SignalIndex Signal)
    (e : State) : Measure disclosure.Output := by
  classical
  exact ∑ input,
    if maskedSignalProfile B input = observed then
      ENNReal.ofReal (source.jointPrior.val (e, input)) •
        disclosure.kernel input
    else 0

/-- The joint subprobability law of the report and one masked B-observation. -/
noncomputable def generalDisclosureWithWholeMeasure
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (observed : SignalProfile SignalIndex Signal) :
    Measure disclosure.Output :=
  ∑ e,
    generalDisclosureWithWholeStateMeasure source B disclosure observed e

/-- Posterior after observing both the whole signals in `B` and an arbitrary disclosure
output. -/
noncomputable def generalDisclosureWithWholePosterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (observed : SignalProfile SignalIndex Signal)
    (output : disclosure.Output) (e : State) : ℝ :=
  ((generalDisclosureWithWholeStateMeasure source B disclosure observed e).rnDeriv
      (generalDisclosureWithWholeMeasure source B disclosure observed) output).toReal

/-- Expected score after jointly observing whole signals `B` and an arbitrary-output
disclosure. -/
noncomputable def generalDisclosureWithWholeValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) : ℝ := by
  classical
  exact ∑ observed,
    ∫ output,
      source.score
          (generalDisclosureWithWholePosterior
            source B disclosure observed output)
        ∂generalDisclosureWithWholeMeasure source B disclosure observed

/-- Joint mass of a state and a disclosure output. -/
noncomputable def disclosureJointMass
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (e : State) (output : disclosure.Output) : ℝ :=
  ∑ input,
    source.jointPrior.val (e, input) *
      (disclosure.kernel input).val output

/-- Probability of one disclosure output. -/
noncomputable def disclosureProbability
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (output : disclosure.Output) : ℝ :=
  ∑ e, disclosureJointMass source disclosure e output

/-- Posterior generated by a randomized disclosure. -/
noncomputable def disclosurePosterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (output : disclosure.Output) (e : State) : ℝ :=
  disclosureJointMass source disclosure e output /
    disclosureProbability source disclosure output

/-- Value of a randomized partial disclosure. -/
noncomputable def disclosureValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal) : ℝ :=
  ∑ output,
    disclosureProbability source disclosure output *
      source.score (disclosurePosterior source disclosure output)

/-- Joint mass after observing both all signals in `B` and a partial disclosure. -/
noncomputable def disclosureWithWholeJointMass
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (e : State)
    (output : SignalProfile SignalIndex Signal ×
      disclosure.Output) : ℝ := by
  classical
  exact
    ∑ input,
      source.jointPrior.val (e, input) *
        if maskedSignalProfile B input = output.1 then
          (disclosure.kernel input).val output.2
        else 0

/-- Probability of jointly observing the whole signals in `B` and one output of a partial
disclosure. -/
noncomputable def disclosureWithWholeProbability
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (output : SignalProfile SignalIndex Signal × disclosure.Output) : ℝ :=
  ∑ e, disclosureWithWholeJointMass source B disclosure e output

/-- Posterior generated by jointly observing the whole signals in `B` and one output of a
partial disclosure. -/
noncomputable def disclosureWithWholePosterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : SignalDisclosure SignalIndex Signal)
    (output : SignalProfile SignalIndex Signal × disclosure.Output)
    (e : State) : ℝ :=
  disclosureWithWholeJointMass source B disclosure e output /
    disclosureWithWholeProbability source B disclosure output

/-- Value after jointly observing whole signals `B` and a disclosure. -/
noncomputable def disclosureWithWholeValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : SignalDisclosure SignalIndex Signal) : ℝ := by
  classical
  exact ∑ output,
    disclosureWithWholeProbability source B disclosure output *
      source.score (disclosureWithWholePosterior source B disclosure output)

/-- Weak substitutes/complements use only collections of whole signals. -/
def IsWeakSubstitutes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  IsLatticeSubmodular (weakSignalValue source)

def IsWeakComplements
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  IsLatticeSupermodular (weakSignalValue source)

/-- Moderate substitutes quantify over deterministic summaries between the meet disclosure
and the whole disclosure of `A`. -/
def IsModerateSubstitutes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : SignalDisclosure SignalIndex Signal,
      SignalDisclosure.IsDeterministicOn source disclosure →
      IsBlackwellBelowOn source (wholeSignalDisclosure (A ∩ B)) disclosure →
      IsBlackwellBelowOn source disclosure (wholeSignalDisclosure A) →
        weakSignalValue source (A ∪ B) - weakSignalValue source A ≤
          disclosureWithWholeValue source B disclosure -
            disclosureValue source disclosure

def IsModerateComplements
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : SignalDisclosure SignalIndex Signal,
      SignalDisclosure.IsDeterministicOn source disclosure →
      IsBlackwellBelowOn source (wholeSignalDisclosure (A ∩ B)) disclosure →
      IsBlackwellBelowOn source disclosure (wholeSignalDisclosure A) →
        disclosureWithWholeValue source B disclosure -
            disclosureValue source disclosure ≤
          weakSignalValue source (A ∪ B) - weakSignalValue source A

/-- Strong substitutes use every randomized garbling, including disclosures with infinite
or continuous report spaces. -/
def IsStrongSubstitutes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : GeneralSignalDisclosure SignalIndex Signal,
      IsGeneralBlackwellBelowOn source
          (generalWholeSignalDisclosure (A ∩ B)) disclosure →
      IsGeneralBlackwellBelowOn source disclosure (generalWholeSignalDisclosure A) →
        weakSignalValue source (A ∪ B) - weakSignalValue source A ≤
          generalDisclosureWithWholeValue source B disclosure -
            generalDisclosureValue source disclosure

/-- Strong complements use the same arbitrary-output disclosure class and reverse the
marginal-value inequality. -/
def IsStrongComplements
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : GeneralSignalDisclosure SignalIndex Signal,
      IsGeneralBlackwellBelowOn source
          (generalWholeSignalDisclosure (A ∩ B)) disclosure →
      IsGeneralBlackwellBelowOn source disclosure (generalWholeSignalDisclosure A) →
        generalDisclosureWithWholeValue source B disclosure -
            generalDisclosureValue source disclosure ≤
          weakSignalValue source (A ∪ B) - weakSignalValue source A

/-!
## The six property labels shared by the independent question branches
-/

/-- The six substitute/complement properties requested in the Research Goal. -/
inductive InformationalProperty
  | weakSubstitutes
  | weakComplements
  | moderateSubstitutes
  | moderateComplements
  | strongSubstitutes
  | strongComplements
deriving DecidableEq, Repr

/-- Interpretation of each requested property for one finite information source. -/
def HasInformationalProperty
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) :
    InformationalProperty → Prop
  | .weakSubstitutes => IsWeakSubstitutes source
  | .weakComplements => IsWeakComplements source
  | .moderateSubstitutes => IsModerateSubstitutes source
  | .moderateComplements => IsModerateComplements source
  | .strongSubstitutes => IsStrongSubstitutes source
  | .strongComplements => IsStrongComplements source


end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Finite information alphabets independent of rational representations
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

/-- Nonempty finite state and signal alphabets, allowing zero base signals. Dimensions are
input data, not permission to choose a different program. -/
structure InformationAlphabet where
  states : ℕ
  states_pos : 0 < states
  signals : ℕ
  signalCard : Fin signals → ℕ
  signalCard_pos : ∀ i, 0 < signalCard i

abbrev InformationAlphabet.State (a : InformationAlphabet) := Fin a.states
abbrev InformationAlphabet.Index (a : InformationAlphabet) := Fin a.signals
abbrev InformationAlphabet.Signal (a : InformationAlphabet) (i : a.Index) := Fin (a.signalCard i)
abbrev InformationAlphabet.Profile (a : InformationAlphabet) := ∀ i : a.Index, a.Signal i

instance (a : InformationAlphabet) : Nonempty a.State := ⟨⟨0, a.states_pos⟩⟩
instance (a : InformationAlphabet) (i : a.Index) : Nonempty (a.Signal i) :=
  ⟨⟨0, a.signalCard_pos i⟩⟩

/-- Strict violation of decreasing marginal value for substitutes, or of increasing
marginal value for complements. Equality is not a violation. -/
def ViolatesMarginal (property : InformationalProperty) (low high : ℝ) : Prop :=
  match property with
  | .weakSubstitutes | .moderateSubstitutes | .strongSubstitutes => low < high
  | .weakComplements | .moderateComplements | .strongComplements => high < low

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Encoded certificates in a fixed rational-expression specialization

The input grammar has rational priors and score expressions formed from rational
constants, coordinates, addition, multiplication, maximum and x log x. Negative
outputs carry explicit finite rational counterexample kernels; a bare false Boolean is
not accepted. Cost and output come from the same Word-RAM search execution; real
evaluation is only specification.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open WordRAM.FiniteData
open scoped BigOperators

/-- Exact casting of rational probabilities into semantic reals. -/
noncomputable def lotteryToReal {X : Type*} [Fintype X]
    (p : Lottery ℚ X) : Lottery ℝ X :=
  ⟨fun x => (p.val x : ℝ), by
    constructor
    · intro x
      change (0 : ℝ) ≤ (p.val x : ℝ)
      exact_mod_cast p.property.1 x
    · change (∑ x, (p.val x : ℝ)) = 1
      exact_mod_cast p.property.2⟩

/-- A fixed score-expression grammar. xlogx is syntax. -/
inductive ScoreExpression (State : Type)
  | constant (value : ℚ)
  | coordinate (state : State)
  | add (left right : ScoreExpression State)
  | multiply (left right : ScoreExpression State)
  | maximum (left right : ScoreExpression State)
  | xlogx (state : State)
  deriving Repr

noncomputable def ScoreExpression.evaluate {State : Type} :
    ScoreExpression State → (State → ℝ) → ℝ
  | .constant q, _ => (q : ℝ)
  | .coordinate e, p => p e
  | .add a b, p => a.evaluate p + b.evaluate p
  | .multiply a b, p => a.evaluate p * b.evaluate p
  | .maximum a b, p => max (a.evaluate p) (b.evaluate p)
  | .xlogx e, p => p e * Real.log (p e)

/-- Convexity is an input promise. -/
def IsConvexScoreExpression {State : Type} [Fintype State]
    (G : ScoreExpression State) : Prop :=
  ∀ p q : State → ℝ, IsProbabilityVector p → IsProbabilityVector q →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      G.evaluate (fun e => t * p e + (1 - t) * q e) ≤
        t * G.evaluate p + (1 - t) * G.evaluate q

structure RationalInformationInput where
  alphabet : InformationAlphabet
  prior : Lottery ℚ (alphabet.State × alphabet.Profile)
  score : ScoreExpression alphabet.State
  convex : IsConvexScoreExpression score

/-- The corresponding real source retains zero probabilities and dependent signals. -/
noncomputable def RationalInformationInput.source (I : RationalInformationInput) :
    FiniteBayesianInformation I.alphabet.State I.alphabet.Index I.alphabet.Signal where
  jointPrior := lotteryToReal I.prior
  score := I.score.evaluate
  score_convex := I.convex

/-- Prefix tags with fixed arity and explicit rational numerators and denominators. -/
def ScoreExpression.atoms {m : ℕ} : ScoreExpression (Fin m) → List Atom
  | .constant q => [.integer 0, .rational q]
  | .coordinate e => [.integer 1, .integer (Int.ofNat e.val)]
  | .add a b => [.integer 2] ++ a.atoms ++ b.atoms
  | .multiply a b => [.integer 3] ++ a.atoms ++ b.atoms
  | .maximum a b => [.integer 4] ++ a.atoms ++ b.atoms
  | .xlogx e => [.integer 5, .integer (Int.ofNat e.val)]

/-- Explicit lexicographic enumeration of dependent finite profiles. -/
def finiteProfiles : (n : ℕ) → (card : Fin n → ℕ) →
    List ((i : Fin n) → Fin (card i))
  | 0, _ => [fun i => Fin.elim0 i]
  | n + 1, card =>
      (List.ofFn (fun head : Fin (card 0) => head)).flatMap (fun head =>
        (finiteProfiles n (fun i => card i.succ)).map (fun tail =>
          Fin.cons head tail))

/-- Every profile in a fixed order, including the zero-signal case. -/
def InformationAlphabet.profiles (a : InformationAlphabet) : List a.Profile :=
  finiteProfiles a.signals a.signalCard

def InformationAlphabet.profileAtoms (a : InformationAlphabet) (v : a.Profile) : List Atom :=
  List.ofFn fun i : a.Index => .integer (Int.ofNat (v i).val)

def propertyTag : InformationalProperty → ℕ
  | .weakSubstitutes => 0
  | .weakComplements => 1
  | .moderateSubstitutes => 2
  | .moderateComplements => 3
  | .strongSubstitutes => 4
  | .strongComplements => 5

/-- The full prior table and score syntax. Numeric bit lengths are included, without
value-dependent padding. -/
def RationalInformationInput.atoms (I : RationalInformationInput)
    (property : InformationalProperty) : List Atom :=
  let a := I.alphabet
  [.integer (Int.ofNat (propertyTag property)), .integer (Int.ofNat a.states),
    .integer (Int.ofNat a.signals)] ++
  List.ofFn (fun i : a.Index => .integer (Int.ofNat (a.signalCard i))) ++
  (List.ofFn (fun e : a.State =>
    a.profiles.flatMap (fun v =>
      [.integer (Int.ofNat e.val)] ++ a.profileAtoms v ++ [.rational (I.prior.val (e, v))]))).flatten ++
  I.score.atoms

def RationalInformationInput.code (I : RationalInformationInput)
    (property : InformationalProperty) : Code := tableCode (I.atoms property)

/-- Finite rational kernel data. Normalization proofs are not machine output; the solution
relation checks that the encoded table is valid. -/
structure RationalGarbling (a : InformationAlphabet) where
  reports : ℕ
  kernel : a.Profile → Lottery ℚ (Fin reports)

noncomputable def RationalGarbling.disclosure {a : InformationAlphabet}
    (g : RationalGarbling a) : SignalDisclosure a.Index a.Signal where
  Output := Fin g.reports
  kernel := fun v => lotteryToReal (g.kernel v)

/-- Positive tag, weak violation, or partial-disclosure violation. No negative constructor
omits its counterexample data. -/
inductive CertificationOutput (a : InformationAlphabet)
  | accept
  | weakViolation (smaller larger added : Finset a.Index)
  | disclosureViolation (A B : Finset a.Index) (garbling : RationalGarbling a)

private def subsetAtoms {a : InformationAlphabet} (S : Finset a.Index) : List Atom :=
  List.ofFn fun i : a.Index => .bit (decide (i ∈ S))

def CertificationOutput.atoms {a : InformationAlphabet} :
    CertificationOutput a → List Atom
  | .accept => [.integer 0]
  | .weakViolation smaller larger added =>
      [.integer 1] ++ subsetAtoms smaller ++ subsetAtoms larger ++ subsetAtoms added
  | .disclosureViolation A B g =>
      [.integer 2] ++ subsetAtoms A ++ subsetAtoms B ++
      [.integer (Int.ofNat g.reports)] ++
      a.profiles.flatMap (fun v => a.profileAtoms v ++
        List.ofFn (fun r : Fin g.reports => .rational ((g.kernel v).val r)))

def CertificationOutput.code {a : InformationAlphabet}
    (o : CertificationOutput a) : Code := tableCode o.atoms

/-- The disclosure lies between A intersect B and A; it cannot inspect the state or
additional signals. Finite witnesses do not redefine the strong property. -/
def CertificationOutput.Valid (I : RationalInformationInput)
    (property : InformationalProperty) : CertificationOutput I.alphabet → Prop
  | .accept => HasInformationalProperty I.source property
  | .weakViolation smaller larger added =>
      (property = .weakSubstitutes ∨ property = .weakComplements) ∧
      larger ∩ added ⊆ smaller ∧ smaller ⊆ larger ∧
      ViolatesMarginal property
        (weakSignalValue I.source (added ∪ smaller) - weakSignalValue I.source smaller)
        (weakSignalValue I.source (added ∪ larger) - weakSignalValue I.source larger)
  | .disclosureViolation A B g =>
      (property = .moderateSubstitutes ∨ property = .moderateComplements ∨
        property = .strongSubstitutes ∨ property = .strongComplements) ∧
      ((property = .moderateSubstitutes ∨ property = .moderateComplements) →
        SignalDisclosure.IsDeterministicOn I.source g.disclosure) ∧
      IsBlackwellBelowOn I.source (wholeSignalDisclosure (A ∩ B)) g.disclosure ∧
      IsBlackwellBelowOn I.source g.disclosure (wholeSignalDisclosure A) ∧
      ViolatesMarginal property
        (disclosureWithWholeValue I.source B g.disclosure - disclosureValue I.source g.disclosure)
        (weakSignalValue I.source (A ∪ B) - weakSignalValue I.source A)

/-- Well-formed fixed-grammar rational input with convex score as a promise. -/
def ValidCertificationInput (property : InformationalProperty) (input : Code) : Prop :=
  ∃ I : RationalInformationInput, I.code property = input

/-- Every valid interpretation of the input must validate a certificate represented by the
very output bitstream. -/
def CertificationSolution (property : InformationalProperty)
    (input output : Code) : Prop :=
  ∀ I : RationalInformationInput, I.code property = input →
    ∃ certificate : CertificationOutput I.alphabet,
      certificate.code = output ∧ certificate.Valid I property

/-- One program for all dimensions and inputs of this specialization. Writing the
certificate is included in the actual interpreter execution. -/
def RationalExpressionCertificationQuestion (property : InformationalProperty) : Prop :=
  WordRAM.Search.PolynomiallySolvable
    (ValidCertificationInput property) (CertificationSolution property)

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Correctness contracts for proposed characterizations

These predicates check a supplied concrete criterion. They do not use the tautological
existence claim that some arbitrary predicate equals the target. Structural,
geometric, sufficient/necessary and special-case directions remain independent, with
scope fixed before the criterion.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- Semantic packaging of posterior laws for every general disclosure. Computational
inputs must instead describe the prior and score explicitly. -/
structure PosteriorGeometry
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  score : SimplexExpectedScore State
  wholeMass : Finset SignalIndex → SignalProfile SignalIndex Signal → ℝ
  wholePosterior : Finset SignalIndex → SignalProfile SignalIndex Signal → State → ℝ
  disclosureLaw : (d : GeneralSignalDisclosure SignalIndex Signal) → Measure d.Output
  disclosurePosterior : (d : GeneralSignalDisclosure SignalIndex Signal) → d.Output → State → ℝ
  withWholeLaw : Finset SignalIndex → (d : GeneralSignalDisclosure SignalIndex Signal) →
    SignalProfile SignalIndex Signal → Measure d.Output
  withWholePosterior : Finset SignalIndex → (d : GeneralSignalDisclosure SignalIndex Signal) →
    SignalProfile SignalIndex Signal → d.Output → State → ℝ

noncomputable def posteriorGeometry
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) :
    PosteriorGeometry State SignalIndex Signal where
  score := fun p => source.score p.1
  wholeMass := observationProbability source
  wholePosterior := posterior source
  disclosureLaw := generalDisclosureMeasure source
  disclosurePosterior := generalDisclosurePosterior source
  withWholeLaw := generalDisclosureWithWholeMeasure source
  withWholePosterior := generalDisclosureWithWholePosterior source

/-- A criterion on prior and score across finite alphabets. The criterion is mathematical
data, not itself a certified computation. -/
abbrev StructuralCriterion :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
    [Fintype State] [Nonempty State]
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
    [∀ i, DecidableEq (Signal i)],
    Lottery ℝ (State × SignalProfile SignalIndex Signal) →
      SimplexExpectedScore State → Prop

/-- A domain fixed before proposing the criterion. -/
abbrev SourceScope :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
    [Fintype State] [Nonempty State]
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
    [∀ i, DecidableEq (Signal i)],
    FiniteBayesianInformation State SignalIndex Signal → Prop

/-- Every source, without independence or score-family restrictions. -/
def allSources : SourceScope := fun _ _ _ => fun _ => True

/-- Correctness of a supplied criterion. -/
def StructuralCharacterizationQuestion (scope : SourceScope)
    (property : InformationalProperty) (criterion : StructuralCriterion) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)]
      (source : FiniteBayesianInformation State SignalIndex Signal),
    scope State SignalIndex Signal source →
      (criterion State SignalIndex Signal source.jointPrior
          (fun p => source.score p.1) ↔ HasInformationalProperty source property)

abbrev PosteriorGeometricCriterion :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
    [Fintype State] [Nonempty State]
    [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
    [∀ i, DecidableEq (Signal i)],
    PosteriorGeometry State SignalIndex Signal → Prop

/-- Posterior-geometric characterization without assuming global differentiability. -/
def PosteriorGeometricCharacterizationQuestion (scope : SourceScope)
    (property : InformationalProperty) (criterion : PosteriorGeometricCriterion) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)]
      (source : FiniteBayesianInformation State SignalIndex Signal),
    scope State SignalIndex Signal source →
      (criterion State SignalIndex Signal (posteriorGeometry source) ↔
        HasInformationalProperty source property)

/-- Correctness on one specified class. The target does not require solving all example
classes simultaneously. -/
def SpecialCaseClassificationQuestion (scope : SourceScope)
    (property : InformationalProperty) (criterion : StructuralCriterion) : Prop :=
  StructuralCharacterizationQuestion scope property criterion

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


section

/-!
## Encoded positive certificates and negative witnesses

This strengthens the accept-or-counterexample interface with actual finite positive
certificates. A fixed Word-RAM checker must be sound and complete for the selected
property on the named rational-expression domain. Neither its existence nor the
completeness of finite negative garblings is assumed. The program pays to emit the
certificate; a semantic accept tag alone is insufficient.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
open WordRAM.FiniteData

abbrev PositiveInformationVerifier := WordRAM.Certificates.Verifier

/-- The fixed executable checker may accept only mathematically positive inputs. -/
def PositiveInformationVerifier.Sound (verifier : PositiveInformationVerifier)
    (property : InformationalProperty) : Prop :=
  ∀ I : RationalInformationInput, ∀ certificate,
    verifier.Accepts (I.code property) certificate →
      HasInformationalProperty I.source property

/-- Completeness is a substantive obligation, not supplied by a constructor. Polynomial
output size is additionally enforced by the certifying solver. -/
def PositiveInformationVerifier.Complete (verifier : PositiveInformationVerifier)
    (property : InformationalProperty) : Prop :=
  ∀ I : RationalInformationInput, HasInformationalProperty I.source property →
    ∃ certificate, verifier.Accepts (I.code property) certificate

/-- A positive branch contains a checker-readable certificate; a negative branch contains
the existing structurally encoded counterexample. -/
inductive CheckedCertificationOutput (alphabet : InformationAlphabet)
  | positive (certificate : Code)
  | negative (counterexample : CertificationOutput alphabet)

def CheckedCertificationOutput.code {alphabet : InformationAlphabet} :
    CheckedCertificationOutput alphabet → Code
  | .positive certificate => true :: certificate
  | .negative counterexample => false :: counterexample.code

def CheckedCertificationOutput.Valid (verifier : PositiveInformationVerifier)
    (property : InformationalProperty) (I : RationalInformationInput) :
    CheckedCertificationOutput I.alphabet → Prop
  | .positive certificate => verifier.Accepts (I.code property) certificate
  | .negative counterexample =>
      counterexample ≠ .accept ∧ counterexample.Valid I property

/-- Every interpretation of the fixed input code must validate the emitted certificate. A
tag cannot invoke a property-computing output decoder. -/
def CheckedCertificationSolution (verifier : PositiveInformationVerifier)
    (property : InformationalProperty) (input output : Code) : Prop :=
  ∀ I : RationalInformationInput, I.code property = input →
    ∃ certificate : CheckedCertificationOutput I.alphabet,
      certificate.code = output ∧ certificate.Valid verifier property I

/-- The checker and property are fixed before choosing the certifying program.
Soundness/completeness are required, not presumed from their types. -/
def CheckedRationalExpressionCertificationQuestion
    (verifier : PositiveInformationVerifier) (property : InformationalProperty) : Prop :=
  verifier.Sound property ∧ verifier.Complete property ∧
    WordRAM.Search.PolynomiallySolvable
      (ValidCertificationInput property) (CheckedCertificationSolution verifier property)

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements

/-- A structural characterization of the selected informational property. -/
theorem structuralCharacterization (property : InformationalProperty) :
    StructuralCharacterizationQuestion allSources property (answer(sorry)) := by
  sorry

/-- A posterior-geometric characterization of the selected informational property. -/
theorem posteriorCharacterization (property : InformationalProperty) :
    PosteriorGeometricCharacterizationQuestion allSources property (answer(sorry)) := by
  sorry

/-- Explicit rational-expression specialization with encoded positive and negative
certificates. -/
theorem algorithmicCertification (verifier : PositiveInformationVerifier)
    (property : InformationalProperty) :
    answer(sorry) ↔ CheckedRationalExpressionCertificationQuestion verifier property := by
  sorry

/-- A characterization on the specified class of information sources. -/
theorem specialCaseCharacterization (scope : SourceScope) (property : InformationalProperty) :
    SpecialCaseClassificationQuestion scope property (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.InformationalSubstitutesComplements
