/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.Util.Answer
import EconCSLib.OpenProblem.Util.Complexity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace EconCSLib.OpenProblem.EconCSBench.InformationalSubstitutesComplements

universe uSignalIndex uSignal uCounterexample

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- A real vector is a probability distribution on a finite state space. -/
def IsProbabilityVector
    {State : Type*} [Fintype State] (p : State → ℝ) : Prop :=
  (∀ e, 0 ≤ p e) ∧ ∑ e, p e = 1

/-- Two total Lean functions represent the same expected-score function on
the mathematical domain `Δ(State)` when they agree on every probability
vector. -/
def ScoresAgreeOnSimplex
    {State : Type*} [Fintype State]
    (first second : (State → ℝ) → ℝ) : Prop :=
  ∀ p, IsProbabilityVector p → first p = second p

/-- Expected-score functions restricted to their mathematical domain, the
finite probability simplex. -/
abbrev SimplexExpectedScore (State : Type*) [Fintype State] :=
  {p : State → ℝ // IsProbabilityVector p} → ℝ

/-- A finite Bayesian information source together with a convex expected-score
function on posterior vectors. -/
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
  /-- The expected score is measurable.  This analytic regularity is implicit
  in the Markdown expectation notation and prevents the measure-theoretic
  integral used for continuous disclosures from collapsing to Lean's default
  value for non-measurable functions. -/
  score_measurable : Measurable score
  /-- A finite convex score on the finite probability simplex is bounded; the
  bound is stored explicitly so arbitrary-output disclosure values are genuine
  integrals rather than relying on an unformalized convex-analysis lemma. -/
  score_bounded_on_simplex :
    ∃ bound : ℝ, ∀ p,
      IsProbabilityVector p → |score p| ≤ bound

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

/-- Posterior on the state after observing the selected base signals.  A
zero-probability observation uses Lean's total division convention, but its
term in the outer expectation has zero weight. -/
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

/-- The induced value `E[G(P(State | A_S))]` of a subset of whole base
signals.  Summing over full profiles is valid because profiles agreeing on
`S` induce the same posterior and their masses aggregate. -/
noncomputable def weakSignalValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (S : Finset SignalIndex) : ℝ :=
  ∑ a, signalProfileProbability source a * source.score (posterior source S a)

/-- Diminishing marginal value on a disclosure lattice, in the exact lattice
form used for informational substitutes. -/
def IsLatticeSubmodular
    {L : Type*} [Lattice L] (value : L → ℝ) : Prop :=
  ∀ A' A B, A ⊓ B ≤ A' → A' ≤ A →
    value (B ⊔ A) - value A ≤ value (B ⊔ A') - value A'

/-- Increasing marginal value on a disclosure lattice. -/
def IsLatticeSupermodular
    {L : Type*} [Lattice L] (value : L → ℝ) : Prop :=
  ∀ A' A B, A ⊓ B ≤ A' → A' ≤ A →
    value (B ⊔ A') - value A' ≤ value (B ⊔ A) - value A

/-- A finite-output randomized partial disclosure (garbling) of the complete
finite signal profile.  This is sufficient for deterministic summaries in the
moderate notion, and remains useful for finite certificates, but the strong
notion below uses `GeneralSignalDisclosure` instead. -/
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

/-- An arbitrary randomized partial disclosure of the complete finite signal
profile.  The report space may be infinite or continuous (for example a noisy
real-valued report), and `kernel input` is its conditional probability law.

The source alphabet is finite, so it is enough to store the family of output
measures directly; no extra measurability condition in the source argument is
needed.  This is the disclosure class quantified over by strong substitutes
and complements in Chen--Waggoner's continuous signal lattice. -/
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

/-- Blackwell order for arbitrary-output disclosures: `less ≼ more` when a
Markov post-processing of `more` produces exactly the conditional law of
`less` for every source realization. -/
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

/-- Blackwell order: `less ≤ more` when `less` is obtained by a stochastic
post-processing of `more`. -/
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

/-- Canonical output profile that records exactly the signals in `S` and uses
fixed dummy values outside `S`. -/
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

/-- Whole-signal disclosure embedded in the arbitrary-output kernel model.
The maximal measurable structure is the discrete measurable structure on this
finite output type. -/
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

/-- Output measure generated jointly by state `e`, the prior on finite signal
profiles, and an arbitrary-output disclosure kernel. -/
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

/-- Posterior probability of state `e` at an arbitrary disclosure output,
represented by the Radon--Nikodym derivative of its state-output measure with
respect to the marginal output law. -/
noncomputable def generalDisclosurePosterior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal)
    (output : disclosure.Output) (e : State) : ℝ :=
  ((generalDisclosureStateMeasure source disclosure e).rnDeriv
      (generalDisclosureMeasure source disclosure) output).toReal

/-- Expected score of an arbitrary-output disclosure.  This Bochner integral
specializes to the finite sum in `disclosureValue` for finite report spaces. -/
noncomputable def generalDisclosureValue
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) : ℝ :=
  ∫ output,
    source.score (generalDisclosurePosterior source disclosure output)
      ∂generalDisclosureMeasure source disclosure

/-- State-output measure after additionally fixing the observed whole-signal
profile on `B`. -/
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

/-- Marginal disclosure-output law conditional on one masked realization of
the additional whole signals `B`. -/
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

/-- Posterior after observing both the whole signals in `B` and an arbitrary
disclosure output. -/
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

/-- Expected score after jointly observing whole signals `B` and an
arbitrary-output disclosure. -/
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

/-- Joint mass after observing both all signals in `B` and a partial
disclosure. -/
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

/-- Probability of jointly observing the whole signals in `B` and one output
of a partial disclosure. -/
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

/-- Posterior generated by jointly observing the whole signals in `B` and one
output of a partial disclosure. -/
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

/-- Moderate substitutes quantify over deterministic summaries between the
meet disclosure and the whole disclosure of `A`. -/
def IsModerateSubstitutes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : SignalDisclosure SignalIndex Signal,
      disclosure.IsDeterministic →
      IsBlackwellBelow (wholeSignalDisclosure (A ∩ B)) disclosure →
      IsBlackwellBelow disclosure (wholeSignalDisclosure A) →
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
      disclosure.IsDeterministic →
      IsBlackwellBelow (wholeSignalDisclosure (A ∩ B)) disclosure →
      IsBlackwellBelow disclosure (wholeSignalDisclosure A) →
        disclosureWithWholeValue source B disclosure -
            disclosureValue source disclosure ≤
          weakSignalValue source (A ∪ B) - weakSignalValue source A

/-- Strong substitutes use every randomized garbling, including disclosures
with infinite or continuous report spaces. -/
def IsStrongSubstitutes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : GeneralSignalDisclosure SignalIndex Signal,
      IsGeneralBlackwellBelow
          (generalWholeSignalDisclosure (A ∩ B)) disclosure →
      IsGeneralBlackwellBelow disclosure (generalWholeSignalDisclosure A) →
        weakSignalValue source (A ∪ B) - weakSignalValue source A ≤
          generalDisclosureWithWholeValue source B disclosure -
            generalDisclosureValue source disclosure

/-- Strong complements use the same arbitrary-output disclosure class and
reverse the marginal-value inequality. -/
def IsStrongComplements
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) : Prop :=
  ∀ A B : Finset SignalIndex,
    ∀ disclosure : GeneralSignalDisclosure SignalIndex Signal,
      IsGeneralBlackwellBelow
          (generalWholeSignalDisclosure (A ∩ B)) disclosure →
      IsGeneralBlackwellBelow disclosure (generalWholeSignalDisclosure A) →
        generalDisclosureWithWholeValue source B disclosure -
            generalDisclosureValue source disclosure ≤
          weakSignalValue source (A ∪ B) - weakSignalValue source A

/-!
## Exact characterization interfaces

The Markdown accepts several different forms of a solution.  The interfaces
below keep those forms separate: a structural criterion, a posterior-geometric
criterion, an efficient certification procedure, and complete classifications
of explicitly named special cases.  The first two answers are criteria whose
correctness is checked by an `iff`; they are not merely existential claims that
some unnamed characterization exists.
-/

/-- The six substitute/complement properties requested in the Research Goal. -/
inductive InformationalProperty
  | weakSubstitutes
  | weakComplements
  | moderateSubstitutes
  | moderateComplements
  | strongSubstitutes
  | strongComplements
deriving DecidableEq

/-- Interpretation of each requested property for one finite information
source. -/
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

/-- A proposed structural test stated directly as a predicate of the primitive
joint distribution `P`, the convex expected-score function `G`, and the
requested substitute/complement property. -/
structure StructuralCharacterizationCandidate
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  condition :
    Lottery ℝ (State × SignalProfile SignalIndex Signal) →
      SimplexExpectedScore State → InformationalProperty → Prop

/-- A structural characterization is correct exactly when its condition is
necessary and sufficient for every convex expected-score source on the fixed
finite alphabets. -/
def IsCorrectStructuralCharacterization
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (candidate :
      StructuralCharacterizationCandidate State SignalIndex Signal) : Prop :=
  ∀ source property,
    candidate.condition source.jointPrior
        (fun belief => source.score belief.1) property ↔
      HasInformationalProperty source property

/-- Prior distribution on the decision-relevant state. -/
noncomputable def statePrior
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal)
    (e : State) : ℝ :=
  ∑ input, source.jointPrior.val (e, input)

/-- All posterior-belief and probability data relevant to the three signal
lattices, together with the convex expected-score geometry.  A criterion that
receives this structure cannot inspect the original signal labels or any data
other than posterior arrangements, their masses, and `G`. -/
structure PosteriorGeometry
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  score : SimplexExpectedScore State
  prior : State → ℝ
  subsetProbability :
    Finset SignalIndex → SignalProfile SignalIndex Signal → ℝ
  subsetPosterior :
    Finset SignalIndex → SignalProfile SignalIndex Signal → State → ℝ
  disclosureProbability :
    (disclosure : SignalDisclosure SignalIndex Signal) →
      disclosure.Output → ℝ
  disclosurePosterior :
    (disclosure : SignalDisclosure SignalIndex Signal) →
      disclosure.Output → State → ℝ
  withWholeProbability :
    (B : Finset SignalIndex) →
      (disclosure : SignalDisclosure SignalIndex Signal) →
        (SignalProfile SignalIndex Signal × disclosure.Output) → ℝ
  withWholePosterior :
    (B : Finset SignalIndex) →
      (disclosure : SignalDisclosure SignalIndex Signal) →
        (SignalProfile SignalIndex Signal × disclosure.Output) → State → ℝ
  subsetExpectedScore : Finset SignalIndex → ℝ
  disclosureExpectedScore :
    SignalDisclosure SignalIndex Signal → ℝ
  withWholeExpectedScore :
    Finset SignalIndex → SignalDisclosure SignalIndex Signal → ℝ
  generalDisclosureMeasure :
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) →
      Measure disclosure.Output
  generalDisclosurePosterior :
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) →
      disclosure.Output → State → ℝ
  generalWithWholeMeasure :
    (B : Finset SignalIndex) →
      (disclosure : GeneralSignalDisclosure SignalIndex Signal) →
        SignalProfile SignalIndex Signal → Measure disclosure.Output
  generalWithWholePosterior :
    (B : Finset SignalIndex) →
      (disclosure : GeneralSignalDisclosure SignalIndex Signal) →
        SignalProfile SignalIndex Signal → disclosure.Output → State → ℝ
  generalDisclosureExpectedScore :
    GeneralSignalDisclosure SignalIndex Signal → ℝ
  generalWithWholeExpectedScore :
    Finset SignalIndex → GeneralSignalDisclosure SignalIndex Signal → ℝ
  priorExpectedScore : ℝ

/-- Posterior geometry induced by a finite Bayesian information source. -/
noncomputable def posteriorGeometry
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) :
    PosteriorGeometry State SignalIndex Signal where
  score := fun belief => source.score belief.1
  prior := statePrior source
  subsetProbability := observationProbability source
  subsetPosterior := posterior source
  disclosureProbability := disclosureProbability source
  disclosurePosterior := disclosurePosterior source
  withWholeProbability := disclosureWithWholeProbability source
  withWholePosterior := disclosureWithWholePosterior source
  subsetExpectedScore := weakSignalValue source
  disclosureExpectedScore := disclosureValue source
  withWholeExpectedScore := disclosureWithWholeValue source
  generalDisclosureMeasure := generalDisclosureMeasure source
  generalDisclosurePosterior := generalDisclosurePosterior source
  generalWithWholeMeasure := generalDisclosureWithWholeMeasure source
  generalWithWholePosterior := generalDisclosureWithWholePosterior source
  generalDisclosureExpectedScore := generalDisclosureValue source
  generalWithWholeExpectedScore := generalDisclosureWithWholeValue source
  priorExpectedScore := weakSignalValue source ∅

/-- Expected convex-score gain over the prior generated by a disclosure.  This
Jensen gap equals the expected generalized Bregman divergence from the prior:
the affine subgradient term cancels after averaging.  It therefore expresses
the Bregman-geometric quantity without adding a differentiability assumption
on `G`, which the Markdown does not impose. -/
noncomputable def PosteriorGeometry.bregmanInformation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (geometry : PosteriorGeometry State SignalIndex Signal)
    (disclosure : SignalDisclosure SignalIndex Signal) : ℝ :=
  geometry.disclosureExpectedScore disclosure - geometry.priorExpectedScore

/-- Expected Bregman information gained by additionally observing all signals
in `B`, conditional on an existing partial disclosure.  This is the exact
quantity `E[D_G(p_{a',b},p_{a'})]` in Chen--Waggoner's divergence
characterization. -/
noncomputable def PosteriorGeometry.marginalBregmanInformation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (geometry : PosteriorGeometry State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : SignalDisclosure SignalIndex Signal) : ℝ :=
  geometry.withWholeExpectedScore B disclosure -
    geometry.disclosureExpectedScore disclosure

/-- Expected Bregman information generated by a possibly continuous-output
disclosure. -/
noncomputable def PosteriorGeometry.generalBregmanInformation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (geometry : PosteriorGeometry State SignalIndex Signal)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) : ℝ :=
  geometry.generalDisclosureExpectedScore disclosure -
    geometry.priorExpectedScore

/-- Marginal Bregman information of adding whole signals `B` after an
arbitrary-output disclosure. -/
noncomputable def PosteriorGeometry.generalMarginalBregmanInformation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (geometry : PosteriorGeometry State SignalIndex Signal)
    (B : Finset SignalIndex)
    (disclosure : GeneralSignalDisclosure SignalIndex Signal) : ℝ :=
  geometry.generalWithWholeExpectedScore B disclosure -
    geometry.generalDisclosureExpectedScore disclosure

/-- The same expected Bregman information gain when the existing information
and the added information are both collections of whole base signals. -/
noncomputable def PosteriorGeometry.wholeSignalMarginalBregmanInformation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (geometry : PosteriorGeometry State SignalIndex Signal)
    (A B : Finset SignalIndex) : ℝ :=
  geometry.subsetExpectedScore (A ∪ B) -
    geometry.subsetExpectedScore A

/-- A proposed posterior-geometric test for all six requested properties. -/
structure PosteriorGeometricCharacterizationCandidate
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  condition :
    PosteriorGeometry State SignalIndex Signal →
      InformationalProperty → Prop

/-- A posterior-geometric characterization is correct when it classifies every
source exactly from its posterior geometry and convex-score evaluations. -/
def IsCorrectPosteriorGeometricCharacterization
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (candidate :
      PosteriorGeometricCharacterizationCandidate State SignalIndex Signal) :
    Prop :=
  ∀ source property,
    candidate.condition (posteriorGeometry source) property ↔
      HasInformationalProperty source property

/-!
## Explicit special-case families

The fourth acceptable form in the Markdown asks for complete classifications
of important base cases.  The following answer domain contains each concrete
family named there: binary state with two finite signals, binary state with
arbitrarily many binary signals, logarithmic score, quadratic score, and finite
graphical information structures.
-/

/-- Expected optimal logarithmic score, with Lean's `0 * log 0 = 0`
convention. -/
noncomputable def logExpectedScore
    {State : Type*} [Fintype State] (p : State → ℝ) : ℝ :=
  ∑ e, p e * Real.log (p e)

/-- Expected optimal quadratic (Brier) score, up to an irrelevant affine
normalization. -/
noncomputable def quadraticExpectedScore
    {State : Type*} [Fintype State] (p : State → ℝ) : ℝ :=
  ∑ e, (p e) ^ 2

/-- One joint assignment to the state and all signal variables. -/
abbrev InformationOutcome
    (State : Type*) {SignalIndex : Type*} (Signal : SignalIndex → Type*) :=
  State × SignalProfile SignalIndex Signal

/-- Agreement of two joint assignments at one information-graph node. -/
def SameAtInformationNode
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    (node : Option SignalIndex)
    (x y : InformationOutcome State Signal) : Prop :=
  match node with
  | none => x.1 = y.1
  | some i => x.2 i = y.2 i

/-- Agreement on all nodes in a finite parent set. -/
def SameOnInformationNodes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    (nodes : Finset (Option SignalIndex))
    (x y : InformationOutcome State Signal) : Prop :=
  ∀ node, node ∈ nodes → SameAtInformationNode node x y

/-- A finite Bayesian-network factorization of the joint information source.
Each local conditional mass may depend only on the node's realized value and
the realized values of its listed parents, the parent relation is acyclic, and
the product of the local conditional masses equals the given joint prior. -/
structure BayesianNetworkRepresentation
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  parents : Option SignalIndex → Finset (Option SignalIndex)
  localProbability :
    Option SignalIndex → InformationOutcome State Signal → ℝ
  nonnegative :
    ∀ node (outcome : InformationOutcome State Signal),
      0 ≤ localProbability node outcome
  normalized :
    ∀ node (outcome : InformationOutcome State Signal),
      match node with
      | none =>
          ∑ e : State, localProbability none (e, outcome.2) = 1
      | some i =>
          ∑ value : Signal i,
            localProbability (some i)
              (outcome.1, Function.update outcome.2 i value) = 1
  depends_only_on_node_and_parents :
    ∀ node (x y : InformationOutcome State Signal),
      SameAtInformationNode node x y →
        SameOnInformationNodes (parents node) x y →
        localProbability node x = localProbability node y
  acyclic :
    ∃ rank : Option SignalIndex → ℕ,
      ∀ node parent, parent ∈ parents node → rank parent < rank node
  factorizes :
    ∀ e input,
      source.jointPrior.val (e, input) =
        ∏ node : Option SignalIndex,
          localProbability node (e, input)

/-- The explicitly named families offered as examples of a complete
special-case classification. -/
inductive SpecialCaseKind
  | binaryStateTwoSignals
  | binaryStateBinarySignals
  | logarithmicScore
  | quadraticScore
  | graphical
deriving DecidableEq

/-- Inputs belonging to the five explicitly named special-case families.  The
constructors retain the hypotheses that put a source in the relevant family,
so a proposed classification cannot silently assume them for general sources. -/
inductive SpecialCaseInstance
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  | binaryStateTwoSignals
      (source : FiniteBayesianInformation State SignalIndex Signal)
      (state_binary : Fintype.card State = 2)
      (two_signals : Fintype.card SignalIndex = 2)
  | binaryStateBinarySignals
      (source : FiniteBayesianInformation State SignalIndex Signal)
      (state_binary : Fintype.card State = 2)
      (signals_binary : ∀ i, Fintype.card (Signal i) = 2)
  | logarithmicScore
      (source : FiniteBayesianInformation State SignalIndex Signal)
      (score_eq : ScoresAgreeOnSimplex source.score logExpectedScore)
  | quadraticScore
      (source : FiniteBayesianInformation State SignalIndex Signal)
      (score_eq : ScoresAgreeOnSimplex source.score quadraticExpectedScore)
  | graphical
      (source : FiniteBayesianInformation State SignalIndex Signal)
      (network : BayesianNetworkRepresentation source)

/-- Underlying Bayesian source of a named special-case input. -/
def SpecialCaseInstance.source
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] :
    SpecialCaseInstance State SignalIndex Signal →
      FiniteBayesianInformation State SignalIndex Signal
  | .binaryStateTwoSignals source _ _ => source
  | .binaryStateBinarySignals source _ _ => source
  | .logarithmicScore source _ => source
  | .quadraticScore source _ => source
  | .graphical source _ => source

/-- Which named family a special-case input belongs to. -/
def SpecialCaseInstance.kind
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] :
    SpecialCaseInstance State SignalIndex Signal → SpecialCaseKind
  | .binaryStateTwoSignals _ _ _ => .binaryStateTwoSignals
  | .binaryStateBinarySignals _ _ _ => .binaryStateBinarySignals
  | .logarithmicScore _ _ => .logarithmicScore
  | .quadraticScore _ _ => .quadraticScore
  | .graphical _ _ => .graphical

/-- A proposed complete classification of all six properties on every named
special-case family. -/
structure SpecialCaseClassificationCandidate
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  condition :
    SpecialCaseInstance State SignalIndex Signal →
      InformationalProperty → Prop

/-- Correctness of a proposed complete classification on one named family.
The Markdown offers the families as alternative examples, so correctness for
one family is not coupled to correctness for the others. -/
def IsCorrectSpecialCaseClassificationFor
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (kind : SpecialCaseKind)
    (candidate :
      SpecialCaseClassificationCandidate State SignalIndex Signal) : Prop :=
  ∀ caseInstance, caseInstance.kind = kind →
    ∀ property,
      candidate.condition caseInstance property ↔
        HasInformationalProperty caseInstance.source property

/-- A certification result either proves the requested property or returns an
explicit counterexample together with a proof that it refutes the property. -/
inductive CertificationResult
    (claim : Prop)
    (Counterexample : Type uCounterexample) : Type uCounterexample where
  | certified (proof : claim)
  | counterexample (witness : Counterexample) (refutes : ¬ claim)

/-- A violated weak-substitutes marginal-value inequality. -/
structure WeakSubstitutesCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  smaller : Finset SignalIndex
  larger : Finset SignalIndex
  added : Finset SignalIndex
  meet_le : larger ∩ added ⊆ smaller
  smaller_le : smaller ⊆ larger
  violation :
    weakSignalValue source (added ∪ smaller) -
        weakSignalValue source smaller <
      weakSignalValue source (added ∪ larger) -
        weakSignalValue source larger

/-- A violated weak-complements marginal-value inequality. -/
structure WeakComplementsCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  smaller : Finset SignalIndex
  larger : Finset SignalIndex
  added : Finset SignalIndex
  meet_le : larger ∩ added ⊆ smaller
  smaller_le : smaller ⊆ larger
  violation :
    weakSignalValue source (added ∪ larger) -
        weakSignalValue source larger <
      weakSignalValue source (added ∪ smaller) -
        weakSignalValue source smaller

/-- A deterministic disclosure witnessing failure of moderate substitutes. -/
structure ModerateSubstitutesCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  A : Finset SignalIndex
  B : Finset SignalIndex
  disclosure : SignalDisclosure SignalIndex Signal
  deterministic : disclosure.IsDeterministic
  meet_below :
    IsBlackwellBelow (wholeSignalDisclosure (A ∩ B)) disclosure
  below_A : IsBlackwellBelow disclosure (wholeSignalDisclosure A)
  violation :
    disclosureWithWholeValue source B disclosure -
        disclosureValue source disclosure <
      weakSignalValue source (A ∪ B) - weakSignalValue source A

/-- A deterministic disclosure witnessing failure of moderate complements. -/
structure ModerateComplementsCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (source : FiniteBayesianInformation State SignalIndex Signal) where
  A : Finset SignalIndex
  B : Finset SignalIndex
  disclosure : SignalDisclosure SignalIndex Signal
  deterministic : disclosure.IsDeterministic
  meet_below :
    IsBlackwellBelow (wholeSignalDisclosure (A ∩ B)) disclosure
  below_A : IsBlackwellBelow disclosure (wholeSignalDisclosure A)
  violation :
    weakSignalValue source (A ∪ B) - weakSignalValue source A <
      disclosureWithWholeValue source B disclosure -
        disclosureValue source disclosure

/-- An arbitrary-output randomized disclosure witnessing failure of strong
substitutes. -/
structure StrongSubstitutesCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) where
  A : Finset SignalIndex
  B : Finset SignalIndex
  disclosure : GeneralSignalDisclosure SignalIndex Signal
  meet_below :
    IsGeneralBlackwellBelow
      (generalWholeSignalDisclosure (A ∩ B)) disclosure
  below_A :
    IsGeneralBlackwellBelow disclosure (generalWholeSignalDisclosure A)
  violation :
    generalDisclosureWithWholeValue source B disclosure -
        generalDisclosureValue source disclosure <
      weakSignalValue source (A ∪ B) - weakSignalValue source A

/-- An arbitrary-output randomized disclosure witnessing failure of strong
complements. -/
structure StrongComplementsCounterexample
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
  (source : FiniteBayesianInformation State SignalIndex Signal) where
  A : Finset SignalIndex
  B : Finset SignalIndex
  disclosure : GeneralSignalDisclosure SignalIndex Signal
  meet_below :
    IsGeneralBlackwellBelow
      (generalWholeSignalDisclosure (A ∩ B)) disclosure
  below_A :
    IsGeneralBlackwellBelow disclosure (generalWholeSignalDisclosure A)
  violation :
    weakSignalValue source (A ∪ B) - weakSignalValue source A <
      generalDisclosureWithWholeValue source B disclosure -
        generalDisclosureValue source disclosure

/-- Six source-dependent certification procedures, each returning either a
formal certificate or a concrete violated inequality/disclosure. -/
structure OperationalCertificationProcedures
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)] where
  weakSubstitutes :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsWeakSubstitutes source)
        (WeakSubstitutesCounterexample source)
  weakComplements :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsWeakComplements source)
        (WeakComplementsCounterexample source)
  moderateSubstitutes :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsModerateSubstitutes source)
        (ModerateSubstitutesCounterexample source)
  moderateComplements :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsModerateComplements source)
        (ModerateComplementsCounterexample source)
  strongSubstitutes :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsStrongSubstitutes source)
        (StrongSubstitutesCounterexample source)
  strongComplements :
    ∀ source : FiniteBayesianInformation State SignalIndex Signal,
      CertificationResult
        (IsStrongComplements source)
        (StrongComplementsCounterexample source)

/-- A fixed finite expression language for succinct score functions.  The
language includes arithmetic, maxima, and logarithms, so it can express
polyhedral scores, polynomial scores (including the quadratic score), and the
finite-state logarithmic score.  Convexity is imposed as a promise below
rather than by restricting the grammar to a small syntactic fragment. -/
inductive SuccinctScoreExpression (State : Type*)
  | constant (value : ℝ)
  | coordinate (state : State)
  | add (left right : SuccinctScoreExpression State)
  | subtract (left right : SuccinctScoreExpression State)
  | multiply (left right : SuccinctScoreExpression State)
  | maximum (left right : SuccinctScoreExpression State)
  | negate (body : SuccinctScoreExpression State)
  | logarithm (body : SuccinctScoreExpression State)

/-- Denotation of the fixed succinct score-expression language. -/
noncomputable def SuccinctScoreExpression.evaluate
    {State : Type*} :
    SuccinctScoreExpression State → (State → ℝ) → ℝ
  | .constant value, _ => value
  | .coordinate state, belief => belief state
  | .add left right, belief => left.evaluate belief + right.evaluate belief
  | .subtract left right, belief => left.evaluate belief - right.evaluate belief
  | .multiply left right, belief => left.evaluate belief * right.evaluate belief
  | .maximum left right, belief => max (left.evaluate belief) (right.evaluate belief)
  | .negate body, belief => -body.evaluate belief
  | .logarithm body, belief => Real.log (body.evaluate belief)

/-- Analytic promise on a succinct expression.  The three fields are exactly
the properties needed by `FiniteBayesianInformation` and by continuous-output
disclosure integrals. -/
structure IsAdmissibleSuccinctScore
    {State : Type*} [Fintype State]
    (expression : SuccinctScoreExpression State) : Prop where
  convex :
    ∀ p q : State → ℝ,
      IsProbabilityVector p → IsProbabilityVector q →
      ∀ weight : ℝ, 0 ≤ weight → weight ≤ 1 →
      expression.evaluate
          (fun e => weight * p e + (1 - weight) * q e) ≤
        weight * expression.evaluate p +
          (1 - weight) * expression.evaluate q
  measurable : Measurable expression.evaluate
  bounded_on_simplex :
    ∃ bound : ℝ, ∀ p,
      IsProbabilityVector p → |expression.evaluate p| ≤ bound

/-- Concrete operational input syntax: the complete finite prior table and a
score expression from the fixed grammar, carrying only the analytic promise
that the expression denotes an admissible convex expected score. -/
structure OperationalSourceCode
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)] where
  prior : Lottery ℝ (State × SignalProfile SignalIndex Signal)
  score : SuccinctScoreExpression State
  score_admissible : IsAdmissibleSuccinctScore score

/-- Mathematical information source denoted by a concrete operational code. -/
noncomputable def OperationalSourceCode.denotes
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (code : OperationalSourceCode State SignalIndex Signal) :
    FiniteBayesianInformation State SignalIndex Signal where
  jointPrior := code.prior
  score := code.score.evaluate
  score_convex := code.score_admissible.convex
  score_measurable := code.score_admissible.measurable
  score_bounded_on_simplex := code.score_admissible.bounded_on_simplex

/-- Canonical prefix encoding of a succinct score expression.  State labels
are represented by their fixed `Fintype.equivFin` indices; binary nodes carry
the length of the left subtree, so the word stream is unambiguous. -/
noncomputable def succinctScoreExpressionWords
    {State : Type*} [Fintype State] :
    SuccinctScoreExpression State → List UnitCostRAM.Word
  | .constant value => [.integer 0, .real value]
  | .coordinate state =>
      [.integer 1, .integer (Fintype.equivFin State state).val]
  | .add left right =>
      .integer 2 :: .integer (succinctScoreExpressionWords left).length ::
        succinctScoreExpressionWords left ++ succinctScoreExpressionWords right
  | .subtract left right =>
      .integer 3 :: .integer (succinctScoreExpressionWords left).length ::
        succinctScoreExpressionWords left ++ succinctScoreExpressionWords right
  | .multiply left right =>
      .integer 4 :: .integer (succinctScoreExpressionWords left).length ::
        succinctScoreExpressionWords left ++ succinctScoreExpressionWords right
  | .maximum left right =>
      .integer 5 :: .integer (succinctScoreExpressionWords left).length ::
        succinctScoreExpressionWords left ++ succinctScoreExpressionWords right
  | .negate body => .integer 6 :: succinctScoreExpressionWords body
  | .logarithm body => .integer 7 :: succinctScoreExpressionWords body

/-- Canonical structural words for an operational source: alphabet sizes,
the complete tagged joint-prior table, and the fixed score-expression syntax.
Every table row carries the indices of its state and all signal values, so a
single program can interpret the table even though `Fintype.equivFin` need not
enumerate dependent signal profiles lexicographically. -/
noncomputable def operationalSourceWords
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    (code : OperationalSourceCode State SignalIndex Signal) :
    List UnitCostRAM.Word := by
  classical
  let signalSizes : List UnitCostRAM.Word :=
    List.ofFn fun i : Fin (Fintype.card SignalIndex) =>
      .integer (Fintype.card (Signal ((Fintype.equivFin SignalIndex).symm i)))
  let priorWords : List UnitCostRAM.Word :=
    (List.ofFn fun row : Fin
        (Fintype.card (State × SignalProfile SignalIndex Signal)) =>
      let outcome :=
        (Fintype.equivFin
          (State × SignalProfile SignalIndex Signal)).symm row
      let signalValueIndices : List UnitCostRAM.Word :=
        List.ofFn fun column : Fin (Fintype.card SignalIndex) =>
          let signalIndex := (Fintype.equivFin SignalIndex).symm column
          .integer
            (Fintype.equivFin (Signal signalIndex)
              (outcome.2 signalIndex)).val
      [.integer (Fintype.equivFin State outcome.1).val] ++
        signalValueIndices ++ [.real (code.prior.val outcome)]).flatten
  let scoreWords := succinctScoreExpressionWords code.score
  exact
    [.integer (Fintype.card State), .integer (Fintype.card SignalIndex)] ++
      signalSizes ++ [.integer priorWords.length] ++ priorWords ++
        [.integer scoreWords.length] ++ scoreWords

/-- Fixed one-word representation of a Boolean decision.  Correctness is not
performed by this decoder; it appears as an external `iff` in the procedure
structure below. -/
def operationalDecisionEncoding : UnitCostRAM.Encoding Bool where
  encode decision := [.bit decision]
  decode
    | [.bit decision] => some decision
    | _ => none
  decode_encode _ := rfl

/-- The source encoder must be lossless and must use exactly the canonical
structural word stream above.  It can no longer choose an empty source type or
an ad-hoc denotation map. -/
structure OperationalCertificationRepresentations
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)] where
  source : UnitCostRAM.Encoding
    (OperationalSourceCode State SignalIndex Signal)
  source_is_canonical : ∀ code, source.encode code = operationalSourceWords code
  sourceCodeNonempty :
    Nonempty (OperationalSourceCode State SignalIndex Signal)

/-- Six Boolean decision functions on the concrete source language.  The
machine decoder merely reads one bit; each `correct_*` field separately proves
that this bit decides the intended semantic property. -/
structure EncodedOperationalCertificationProcedures
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (representation :
      OperationalCertificationRepresentations State SignalIndex Signal) where
  weakSubstitutes : OperationalSourceCode State SignalIndex Signal → Bool
  correct_weakSubstitutes : ∀ code,
    weakSubstitutes code = true ↔ IsWeakSubstitutes code.denotes
  weakComplements : OperationalSourceCode State SignalIndex Signal → Bool
  correct_weakComplements : ∀ code,
    weakComplements code = true ↔ IsWeakComplements code.denotes
  moderateSubstitutes : OperationalSourceCode State SignalIndex Signal → Bool
  correct_moderateSubstitutes : ∀ code,
    moderateSubstitutes code = true ↔ IsModerateSubstitutes code.denotes
  moderateComplements : OperationalSourceCode State SignalIndex Signal → Bool
  correct_moderateComplements : ∀ code,
    moderateComplements code = true ↔ IsModerateComplements code.denotes
  strongSubstitutes : OperationalSourceCode State SignalIndex Signal → Bool
  correct_strongSubstitutes : ∀ code,
    strongSubstitutes code = true ↔ IsStrongSubstitutes code.denotes
  strongComplements : OperationalSourceCode State SignalIndex Signal → Bool
  correct_strongComplements : ∀ code,
    strongComplements code = true ↔ IsStrongComplements code.denotes

/-- The six finite programs are chosen once for the entire indexed family of
finite alphabets. -/
structure OperationalCertificationProgramSuite where
  weakSubstitutes : UnitCostRAM.Program Empty
  weakComplements : UnitCostRAM.Program Empty
  moderateSubstitutes : UnitCostRAM.Program Empty
  moderateComplements : UnitCostRAM.Program Empty
  strongSubstitutes : UnitCostRAM.Program Empty
  strongComplements : UnitCostRAM.Program Empty

/-- A strict certificate's displayed polynomial is bounded by the one pair of
constants shared by all six procedures.  Combined with the certificate's
`time_bound`, this bounds the actual interpreter execution. -/
def strictCertificateRunsWithin
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

/-- Each Boolean decision function is implemented by a finite
instruction-level unit-cost real-RAM program.  All six use the same canonical
one-bit output encoding, and the same polynomial constants bound every
program. -/
def EncodedOperationalCertificationProcedures.IsEfficient
    {State SignalIndex : Type*} {Signal : SignalIndex → Type*}
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)]
    (representation :
      OperationalCertificationRepresentations State SignalIndex Signal)
    (procedures : EncodedOperationalCertificationProcedures representation)
    (programs : OperationalCertificationProgramSuite)
    (coefficient exponent : ℕ) : Prop :=
  (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.weakSubstitutes,
      certificate.program = programs.weakSubstitutes ∧
        strictCertificateRunsWithin certificate coefficient exponent) ∧
    (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.weakComplements,
      certificate.program = programs.weakComplements ∧
        strictCertificateRunsWithin certificate coefficient exponent) ∧
    (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.moderateSubstitutes,
      certificate.program = programs.moderateSubstitutes ∧
        strictCertificateRunsWithin certificate coefficient exponent) ∧
    (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.moderateComplements,
      certificate.program = programs.moderateComplements ∧
        strictCertificateRunsWithin certificate coefficient exponent) ∧
    (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.strongSubstitutes,
      certificate.program = programs.strongSubstitutes ∧
        strictCertificateRunsWithin certificate coefficient exponent) ∧
    (∃ certificate : StrictRAMComputableInPolyTime representation.source
      operationalDecisionEncoding.dependent procedures.strongComplements,
      certificate.program = programs.strongComplements ∧
        strictCertificateRunsWithin certificate coefficient exponent)

/-- A complete operational characterization: the same six semantically
correct Boolean decision procedures must satisfy the strict efficiency
requirement. -/
structure OperationalCharacterization
    (State SignalIndex : Type*) (Signal : SignalIndex → Type*)
    (coefficient exponent : ℕ)
    (programs : OperationalCertificationProgramSuite)
    [Fintype State] [Fintype SignalIndex] [DecidableEq SignalIndex]
    [∀ i, Fintype (Signal i)] [∀ i, DecidableEq (Signal i)]
    [∀ i, Nonempty (Signal i)] where
  representation :
    OperationalCertificationRepresentations State SignalIndex Signal
  procedures :
    EncodedOperationalCertificationProcedures representation
  efficient : procedures.IsEfficient representation programs
    coefficient exponent

/-!
## The four alternative accepted Research-Goal outputs

The Markdown says that any one of the four forms is a satisfactory solution.
Accordingly, the final statement below is a disjunction; it does not require a
future contributor to solve all four programs simultaneously.
-/

/-- Alternative 1: a necessary-and-sufficient structural characterization on
every finite alphabet. -/
def StructuralInformationalCharacterizationStatement : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    ∃ candidate :
        StructuralCharacterizationCandidate State SignalIndex Signal,
      IsCorrectStructuralCharacterization candidate

/-- Alternative 2: a necessary-and-sufficient posterior/Bregman-geometric
characterization on every finite alphabet. -/
def PosteriorGeometricInformationalCharacterizationStatement : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    ∃ candidate :
        PosteriorGeometricCharacterizationCandidate
          State SignalIndex Signal,
      IsCorrectPosteriorGeometricCharacterization candidate

/-- Research Goal 3, in its algorithmic-certification form. -/
def OperationalInformationalCharacterizationStatement : Prop :=
  ∃ coefficient exponent : ℕ,
  ∃ programs : OperationalCertificationProgramSuite,
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
        [Fintype State] [Nonempty State]
        [Fintype SignalIndex] [DecidableEq SignalIndex]
        [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
        [∀ i, DecidableEq (Signal i)],
      Nonempty
        (OperationalCharacterization State SignalIndex Signal
          coefficient exponent programs)

/-- Alternative 4: choose and completely classify one of the five special-case
families explicitly listed by the Markdown. -/
def SpecialCaseInformationalClassificationStatement : Prop :=
  ∃ kind : SpecialCaseKind,
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
        [Fintype State] [Nonempty State]
        [Fintype SignalIndex] [DecidableEq SignalIndex]
        [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
        [∀ i, DecidableEq (Signal i)],
      ∃ candidate :
          SpecialCaseClassificationCandidate State SignalIndex Signal,
        IsCorrectSpecialCaseClassificationFor kind candidate

/-!
## Typed answer domain

The Markdown asks the solver to *supply* one of four kinds of characterization.
The following answer structures retain that data instead of allowing the
`answer` marker to be filled by copying an existential/disjunctive proposition.
As with any open-ended notion of a "useful characterization", human review must
still reject a candidate whose `condition` merely calls
`HasInformationalProperty` again under another name.
-/

/-- A uniform family of structural criteria, one for every finite alphabet. -/
structure StructuralInformationalCharacterizationAnswer where
  candidate :
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
        StructuralCharacterizationCandidate State SignalIndex Signal

/-- Correctness of a supplied uniform structural characterization. -/
def IsCorrectStructuralInformationalCharacterizationAnswer
    (result : StructuralInformationalCharacterizationAnswer) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    IsCorrectStructuralCharacterization
      (result.candidate State SignalIndex Signal)

/-- A uniform family of posterior-geometric criteria. -/
structure PosteriorGeometricInformationalCharacterizationAnswer where
  candidate :
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
        PosteriorGeometricCharacterizationCandidate
          State SignalIndex Signal

/-- Correctness of a supplied uniform posterior-geometric characterization. -/
def IsCorrectPosteriorGeometricInformationalCharacterizationAnswer
    (result : PosteriorGeometricInformationalCharacterizationAnswer) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    IsCorrectPosteriorGeometricCharacterization
      (result.candidate State SignalIndex Signal)

/-- A uniform family of operational certification procedures.  Correctness of
the returned certificates/counterexamples is carried by their dependent
result types; efficiency is carried by `OperationalCharacterization`. -/
structure OperationalInformationalCharacterizationAnswer where
  /-- Uniform polynomial coefficient, fixed before every finite alphabet. -/
  coefficient : ℕ
  /-- Uniform polynomial exponent, fixed before every finite alphabet. -/
  exponent : ℕ
  /-- One program per requested property, shared by every finite alphabet. -/
  programs : OperationalCertificationProgramSuite
  characterization :
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
        OperationalCharacterization State SignalIndex Signal
          coefficient exponent programs

/-- Correctness interface for an operational answer. -/
def IsCorrectOperationalInformationalCharacterizationAnswer
    (result : OperationalInformationalCharacterizationAnswer) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    (result.characterization State SignalIndex Signal).procedures.IsEfficient
      (result.characterization State SignalIndex Signal).representation
      result.programs result.coefficient result.exponent

/-- One chosen named family together with a uniform proposed classification. -/
structure SpecialCaseInformationalClassificationAnswer where
  kind : SpecialCaseKind
  candidate :
    ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
        SpecialCaseClassificationCandidate State SignalIndex Signal

/-- Correctness of the supplied classification on its chosen named family. -/
def IsCorrectSpecialCaseInformationalClassificationAnswer
    (result : SpecialCaseInformationalClassificationAnswer) : Prop :=
  ∀ (State SignalIndex : Type) (Signal : SignalIndex → Type)
      [Fintype State] [Nonempty State]
      [Fintype SignalIndex] [DecidableEq SignalIndex]
      [∀ i, Fintype (Signal i)] [∀ i, Nonempty (Signal i)]
      [∀ i, DecidableEq (Signal i)],
    IsCorrectSpecialCaseClassificationFor result.kind
      (result.candidate State SignalIndex Signal)

/-- A solver may submit any one of the four answer forms accepted by the
Markdown. -/
inductive InformationalSubstitutesComplementsAnswer
  | structural (result : StructuralInformationalCharacterizationAnswer)
  | posteriorGeometric
      (result : PosteriorGeometricInformationalCharacterizationAnswer)
  | operational (result : OperationalInformationalCharacterizationAnswer)
  | specialCase (result : SpecialCaseInformationalClassificationAnswer)

/-- Correctness predicate for the selected answer form. -/
def IsCorrectInformationalSubstitutesComplementsAnswer :
    InformationalSubstitutesComplementsAnswer → Prop
  | .structural result =>
      IsCorrectStructuralInformationalCharacterizationAnswer result
  | .posteriorGeometric result =>
      IsCorrectPosteriorGeometricInformationalCharacterizationAnswer result
  | .operational result =>
      IsCorrectOperationalInformationalCharacterizationAnswer result
  | .specialCase result =>
      IsCorrectSpecialCaseInformationalClassificationAnswer result

/-- Exactly one satisfactory output form is enough, as specified in the
Markdown Research Goal. -/
def InformationalSubstitutesComplementsStatement : Prop :=
  StructuralInformationalCharacterizationStatement ∨
    PosteriorGeometricInformationalCharacterizationStatement ∨
    OperationalInformationalCharacterizationStatement ∨
    SpecialCaseInformationalClassificationStatement

/-- Typed answer to: "Can informational substitutes and complements be given
any one of the four accepted structural, geometric, operational, or
special-case characterizations?"  The replacement must choose a constructor
and supply the corresponding characterization data; copying the disjunction
above is not an answer. -/
theorem informationalSubstitutesComplements :
    IsCorrectInformationalSubstitutesComplementsAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.InformationalSubstitutesComplements
