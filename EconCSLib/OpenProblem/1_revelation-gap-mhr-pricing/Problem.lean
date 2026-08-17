/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.EconCSBench.Common
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Kernel.Basic

namespace EconCSLib.OpenProblem.EconCSBench.RevelationGapMHROneSample

open MeasureTheory ProbabilityTheory

/-!
## Value distributions and the MHR condition
-/

/-- A probability distribution of a nonnegative buyer value.  Finiteness of
the monopoly benchmark is included so that approximation factors are
real-valued. -/
structure ValueDistribution where
  /-- Law of the buyer value and of the seller's independent sample. -/
  measure : Measure ℝ
  /-- The law has total mass one. -/
  probability : IsProbabilityMeasure measure
  /-- Negative buyer values have probability zero. -/
  nonnegative_support : measure (Set.Iio 0) = 0
  /-- Posted-price revenues are bounded above. -/
  monopoly_bounded :
    BddAbove
      (Set.range fun p : {p : ℝ // 0 ≤ p} =>
        p.1 * ENNReal.toReal (measure (Set.Ici p.1)))

/-- Probability that a buyer accepts a posted price `p`.  The closed event
`p ≤ v` also handles distributions with atoms. -/
noncomputable def ValueDistribution.saleProbability
    (F : ValueDistribution) (p : ℝ) : ℝ :=
  ENNReal.toReal (F.measure (Set.Ici p))

/-- Monopoly posted-price revenue `sup_{p ≥ 0} p Pr[v ≥ p]`. -/
noncomputable def ValueDistribution.monopolyRevenue
    (F : ValueDistribution) : ℝ :=
  ⨆ p : {p : ℝ // 0 ≤ p}, p.1 * F.saleProbability p.1

/-- Distribution-free formulation of monotone hazard rate: the survival
function is log-concave.  For absolutely continuous laws this is equivalent to
the usual requirement that `density / survival` is nondecreasing, and it also
allows atomic limiting cases used in the cited lower bounds. -/
def ValueDistribution.IsMHR (F : ValueDistribution) : Prop :=
  ∀ (x y t : ℝ), 0 ≤ t → t ≤ 1 →
    (F.saleProbability x) ^ t *
        (F.saleProbability y) ^ (1 - t) ≤
      F.saleProbability (t * x + (1 - t) * y)

/-- The concrete family of nonnegative MHR value distributions. -/
def MHRDistribution := {F : ValueDistribution // F.IsMHR}

/-!
## Scale-invariant truthful sample pricing
-/

/-- A truthful sample-pricing rule maps the observed sample to a possibly
random posted price.  Scale invariance is imposed exactly on this price law. -/
structure TruthfulSamplePricing where
  /-- Conditional distribution of the posted price given the sample. -/
  price : Kernel ℝ ℝ
  /-- A genuine probability law of prices for every sample. -/
  price_isProbability : IsMarkovKernel price
  /-- Posted prices are nonnegative. -/
  price_nonnegative : ∀ s, price s (Set.Iio 0) = 0
  /-- Scaling the sample scales the price distribution by the same factor. -/
  scale_invariant :
    ∀ (c : ℝ), 0 < c → ∀ s,
      Measure.map (fun p : ℝ => c * p) (price s) = price (c * s)
  /-- The iterated expected posted-price revenue is well-defined for every MHR
  distribution. -/
  revenue_integrable :
    ∀ F : MHRDistribution,
      (∀ᵐ s ∂F.1.measure,
        Integrable
          (fun p => p * F.1.saleProbability p)
          (price s)) ∧
      Integrable
        (fun s => ∫ p, p * F.1.saleProbability p ∂price s)
        F.1.measure

/-- Expected revenue of a scale-invariant sample-pricing rule.  The value and
the sample are independent draws from `F`; conditional on a sampled price `p`,
the sale probability is `Pr[v ≥ p]`. -/
noncomputable def truthfulSamplePricingRevenue
    (P : TruthfulSamplePricing) (F : MHRDistribution) : ℝ :=
  ∫ s, (∫ p, p * F.1.saleProbability p ∂P.price s) ∂F.1.measure

/-!
## Prior-independent one-bid mechanisms
-/

/-- The action space in the Feng--Hartline--Li baseline: either opt out or
submit one nonnegative bid before observing the seller's hidden sample. -/
abbrev OneBidAction := Option {b : ℝ // 0 ≤ b}

/-- A prior-independent one-bid protocol.  Fixing the action space prevents
this baseline class from silently including the richer distribution-report or
multi-round message spaces discussed separately in the Markdown. -/
structure OneSampleProtocol where
  /-- Allocation probability as a function of the bid and hidden sample. -/
  allocation : OneBidAction → ℝ → ℝ
  /-- Payment as a function of the bid and hidden sample. -/
  payment : OneBidAction → ℝ → ℝ
  /-- Allocation probabilities lie in `[0,1]`. -/
  allocation_mem : ∀ a s, 0 ≤ allocation a s ∧ allocation a s ≤ 1
  /-- The seller never pays the buyer. -/
  payment_nonnegative : ∀ a s, 0 ≤ payment a s
  /-- Allocation and payment are measurable in the hidden sample. -/
  allocation_measurable : ∀ a, Measurable (allocation a)
  payment_measurable : ∀ a, Measurable (payment a)
  /-- Every MHR distribution gives finite interim allocations and payments. -/
  sample_integrable :
    ∀ (F : MHRDistribution) (a : OneBidAction),
      Integrable (allocation a) F.1.measure ∧
        Integrable (payment a) F.1.measure
  /-- An explicit outside option guarantees interim individual rationality. -/
  optOut_allocation : ∀ s, allocation none s = 0
  optOut_payment : ∀ s, payment none s = 0

/-- The concrete sample-bid format from Feng--Hartline--Li.  Besides the
outside option, actions are nonnegative bids; bid `b` wins exactly when
`b ≥ s` and pays `α min{b,s}` whether or not it wins. -/
def OneSampleProtocol.IsSampleBid
    (M : OneSampleProtocol) (α : ℝ) : Prop :=
  0 < α ∧
    ∀ (b : {b : ℝ // 0 ≤ b}) (s : ℝ), 0 ≤ s →
      M.allocation (some b) s =
          (if s ≤ b.1 then 1 else 0) ∧
        M.payment (some b) s = α * min b.1 s

/-- Allocation probability averaged over the seller's hidden sample. -/
noncomputable def OneSampleProtocol.expectedAllocation
    (M : OneSampleProtocol) (F : MHRDistribution)
    (a : OneBidAction) : ℝ :=
  ∫ s, M.allocation a s ∂F.1.measure

/-- Payment averaged over the seller's hidden sample. -/
noncomputable def OneSampleProtocol.expectedPayment
    (M : OneSampleProtocol) (F : MHRDistribution)
    (a : OneBidAction) : ℝ :=
  ∫ s, M.payment a s ∂F.1.measure

/-- Interim utility when value `v` chooses strategic action `a`. -/
noncomputable def OneSampleProtocol.expectedUtility
    (M : OneSampleProtocol) (F : MHRDistribution)
    (v : ℝ) (a : OneBidAction) : ℝ :=
  v * M.expectedAllocation F a - M.expectedPayment F a

/-- The buyer may use knowledge of `F` to choose any utility-maximizing
strategy; this is precisely where non-revelation mechanisms can outperform
prior-independent truthful mechanisms. -/
def OneSampleProtocol.IsBestResponse
    (M : OneSampleProtocol) (F : MHRDistribution)
    (v : ℝ) (a : OneBidAction) : Prop :=
  ∀ alternative : OneBidAction,
    M.expectedUtility F v alternative ≤ M.expectedUtility F v a

/-- A measurable-in-payments Bayes best-response selection.  Requiring
best-response only almost everywhere is the appropriate condition for expected
revenue. -/
structure OneSampleEquilibrium
    (M : OneSampleProtocol) (F : MHRDistribution) where
  /-- Strategy selected for every realized value. -/
  action : ℝ → OneBidAction
  /-- Almost every type chooses a best response. -/
  best_response :
    ∀ᵐ v ∂F.1.measure, M.IsBestResponse F v (action v)
  /-- The induced payment is measurable and integrable. -/
  payment_integrable :
    Integrable (fun v => M.expectedPayment F (action v)) F.1.measure

/-- Revenue at one equilibrium selection. -/
noncomputable def OneSampleEquilibrium.revenue
    {M : OneSampleProtocol} {F : MHRDistribution}
    (equilibrium : OneSampleEquilibrium M F) : ℝ :=
  ∫ v, M.expectedPayment F (equilibrium.action v) ∂F.1.measure

/-- An admissible prior-independent one-bid mechanism includes an explicit
Bayes-equilibrium selection for every MHR distribution.  This makes the
equilibrium used to evaluate revenue part of the mathematical model instead of
silently imposing pessimistic or favorable tie-breaking. -/
structure OneSampleMechanism extends OneSampleProtocol where
  equilibrium :
    ∀ F : MHRDistribution, OneSampleEquilibrium toOneSampleProtocol F

/-- Revenue under the mechanism's explicitly declared equilibrium selection. -/
noncomputable def OneSampleMechanism.revenue
    (M : OneSampleMechanism) (F : MHRDistribution) : ℝ :=
  (M.equilibrium F).revenue

/-!
## Tight factors and their ratio
-/

/-- A scale-invariant truthful sample-pricing rule achieves factor `β`. -/
def TruthfulSamplePricing.AchievesFactor
    (P : TruthfulSamplePricing) (β : ℝ) : Prop :=
  1 ≤ β ∧
    ∀ F : MHRDistribution,
      F.1.monopolyRevenue ≤ β * truthfulSamplePricingRevenue P F

/-- A prior-independent one-bid mechanism achieves factor `β`. -/
def OneSampleMechanism.AchievesFactor
    (M : OneSampleMechanism) (β : ℝ) : Prop :=
  1 ≤ β ∧
    ∀ F : MHRDistribution,
      F.1.monopolyRevenue ≤ β * M.revenue F

/-- Some truthful scale-invariant sample-pricing rule achieves factor `β`. -/
def TruthfulMHRGuarantee (β : ℝ) : Prop :=
  ∃ P : TruthfulSamplePricing, P.AchievesFactor β

/-- Some admissible prior-independent one-bid mechanism achieves factor `β`. -/
def AllMechanismsMHRGuarantee (β : ℝ) : Prop :=
  ∃ M : OneSampleMechanism, M.AchievesFactor β

/-- `β` is the tight value of an approximation factor for which smaller is
better.  This characterization does not assume that the infimum is attained:
every strictly weaker factor above `β` must be achievable, and every
strictly stronger factor in `[1, β)` must be impossible. -/
def IsTightMHRFactor (guarantee : ℝ → Prop) (β : ℝ) : Prop :=
  1 ≤ β ∧
    (∀ γ : ℝ, β < γ → guarantee γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ guarantee γ

/-- The three numerical quantities whose exact values the research goal asks
to identify. -/
structure MHRRevelationGapAnswer where
  truthfulFactor : ℝ
  allMechanismsFactor : ℝ
  gap : ℝ

/-- Correctness specification for the three requested numerical answers.  The
two factors must separately close their optimization gaps, and the revelation
gap must be their ratio. -/
def IsCorrectMHRRevelationGapAnswer
    (result : MHRRevelationGapAnswer) : Prop :=
  IsTightMHRFactor TruthfulMHRGuarantee result.truthfulFactor ∧
    IsTightMHRFactor AllMechanismsMHRGuarantee
      result.allMechanismsFactor ∧
    result.gap = result.truthfulFactor / result.allMechanismsFactor

/-- Open-problem statement: the two tight factors and their revelation-gap
ratio can be identified. -/
def TightMHRRevelationGapStatement : Prop :=
  ∃ result : MHRRevelationGapAnswer,
    IsCorrectMHRRevelationGapAnswer result

/-- Typed answer to: "What is the tight revelation gap between truthful sample
pricing and all prior-independent one-bid mechanisms in the Feng--Hartline--Li
MHR baseline?"  The three numerical values must be identified explicitly;
reusing the defining infimum or the correctness predicate is not a solution. -/
theorem tightMHRRevelationGap :
    IsCorrectMHRRevelationGapAnswer (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.EconCSBench.RevelationGapMHROneSample
