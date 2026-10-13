/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic

/-!
# 19. The MHR pricing revelation gap
-/



section

/-!
## MHR sample pricing and hidden-sample one-bid protocols

The protocol is fixed before the prior. The buyer knows her value and prior, but not
the independent sample. MHR means log-concave survival, including endpoint atoms.
Interim payments are finite in this baseline. Limit bids and equilibrium selection are
explicit [FHL21, Sections 2–4 and 7]. A scalar bid does not itself prohibit encoding
prior information; no claim covers all distribution-report or multi-round protocols.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A nonnegative value distribution with finite monopoly revenue. -/
structure ValueDistribution where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  nonnegative_support : measure (Set.Iio 0) = 0
  monopoly_bounded :
    BddAbove (Set.range fun p : {p : ℝ // 0 ≤ p} =>
      p.1 * (measure (Set.Ici p.1)).toReal)

/-- Sale at equality uses `v ≥ p`, including atoms. -/
def ValueDistribution.saleProbability (F : ValueDistribution) (p : ℝ) : ℝ :=
  (F.measure (Set.Ici p)).toReal

/-- Monopoly-revenue supremum, with no attainment assumption. -/
def ValueDistribution.monopolyRevenue (F : ValueDistribution) : ℝ :=
  ⨆ p : {p : ℝ // 0 ≤ p}, p.1 * F.saleProbability p.1

/-- Log-concavity of survival, equivalent to increasing hazard under suitable density
assumptions; not log-concavity of the density. -/
def ValueDistribution.IsMHR (F : ValueDistribution) : Prop :=
  ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    (F.saleProbability x) ^ t * (F.saleProbability y) ^ (1 - t) ≤
      F.saleProbability (t * x + (1 - t) * y)

/-- The fixed distribution class of the baseline question. -/
abbrev MHRDistribution := {F : ValueDistribution // F.IsMHR}

/-- A separate limit action represents an infinite bid; it is not a machine word. -/
inductive OneBidAction where
  | optOut
  | bid (value : {b : ℝ // 0 ≤ b})
  | limitBid

/-- Finite bids and the limit-bid variant are not identified. -/
inductive BidConvention where
  | finiteOnly
  | withLimitBid
  deriving DecidableEq

/-- Actions admitted by the selected bid convention. -/
def BidConvention.Allows : BidConvention → OneBidAction → Prop
  | .finiteOnly, .limitBid => False
  | _, _ => True

/-- A fixed protocol sees only action and sample. Allocation probabilities and expected
payments summarize seller randomness under risk-neutral utility. Only `IsSampleBid`
ties the limit action to a specific limiting formula. -/
structure OneSampleProtocol where
  allocation : OneBidAction → ℝ → ℝ
  payment : OneBidAction → ℝ → ℝ
  allocation_mem : ∀ a s, 0 ≤ allocation a s ∧ allocation a s ≤ 1
  payment_nonnegative : ∀ a s, 0 ≤ payment a s
  allocation_measurable : ∀ a, Measurable (allocation a)
  payment_measurable : ∀ a, Measurable (payment a)
  sample_payment_integrable : ∀ (F : MHRDistribution) (a : OneBidAction),
    Integrable (payment a) F.1.measure
  optOut_allocation : ∀ s, allocation .optOut s = 0
  optOut_payment : ∀ s, payment .optOut s = 0

/-- Interim allocation probability, averaging over the independent hidden sample. -/
def OneSampleProtocol.expectedAllocation
    (M : OneSampleProtocol) (F : MHRDistribution) (a : OneBidAction) : ℝ :=
  ∫ s, M.allocation a s ∂F.1.measure

/-- Finite expected payment over the independent hidden sample. -/
def OneSampleProtocol.expectedPayment
    (M : OneSampleProtocol) (F : MHRDistribution) (a : OneBidAction) : ℝ :=
  ∫ s, M.payment a s ∂F.1.measure

/-- A deviation changes the action, keeping the true value and prior fixed. -/
def OneSampleProtocol.expectedUtility (M : OneSampleProtocol)
    (F : MHRDistribution) (v : ℝ) (a : OneBidAction) : ℝ :=
  v * M.expectedAllocation F a - M.expectedPayment F a

/-- Best response among all allowed actions; uniqueness is not required. -/
def OneSampleProtocol.IsBestResponse (M : OneSampleProtocol)
    (bids : BidConvention) (F : MHRDistribution) (v : ℝ)
    (a : OneBidAction) : Prop :=
  bids.Allows a ∧ ∀ alternative, bids.Allows alternative →
    M.expectedUtility F v alternative ≤ M.expectedUtility F v a

/-- A measurable best-response selection depending on value, not sample. Joint outcome
conditions ensure well-defined expectations under two independent draws. -/
structure OneSampleEquilibrium (M : OneSampleProtocol)
    (bids : BidConvention) (F : MHRDistribution) where
  action : ℝ → OneBidAction
  best_response : ∀ᵐ v ∂F.1.measure, M.IsBestResponse bids F v (action v)
  allocation_measurable :
    AEStronglyMeasurable (fun z : ℝ × ℝ => M.allocation (action z.1) z.2)
      (F.1.measure.prod F.1.measure)
  payment_integrable :
    Integrable (fun z : ℝ × ℝ => M.payment (action z.1) z.2)
      (F.1.measure.prod F.1.measure)

/-- Revenue is expected payment, not allocation probability. -/
def OneSampleEquilibrium.revenue
    {M : OneSampleProtocol} {bids : BidConvention} {F : MHRDistribution}
    (e : OneSampleEquilibrium M bids F) : ℝ :=
  ∫ z : ℝ × ℝ, M.payment (e.action z.1) z.2 ∂(F.1.measure.prod F.1.measure)

/-- Existential favorable equilibrium selection versus guarantees for every equilibrium. -/
inductive EquilibriumConvention where
  | selected
  | robust
  deriving DecidableEq

/-- Every prior must admit an equilibrium, including in the robust branch. -/
def OneSampleProtocol.AchievesFactor (M : OneSampleProtocol)
    (bids : BidConvention) (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∀ F : MHRDistribution,
    match ties with
    | .selected => ∃ e : OneSampleEquilibrium M bids F,
        F.1.monopolyRevenue ≤ β * e.revenue
    | .robust => Nonempty (OneSampleEquilibrium M bids F) ∧
        ∀ e : OneSampleEquilibrium M bids F,
          F.1.monopolyRevenue ≤ β * e.revenue

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end


section

/-!
## One-bid questions beyond MHR

These extensions retain the hidden-sample action/outcome interface. Nonnegative
extended payments allow heavy-tailed regular priors: an action with infinite expected
payment has utility negative infinity, rather than the default zero of a nonintegrable
Bochner integral. `IsSmoothRegular` states the continuous positive-density reference
convention explicitly; no equivalence to every discrete or endpoint-atom extension of
regularity is claimed. A real action may encode rich reports; no equivalence to
general interactive mechanisms is proved merely from the choice of action type.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- A distribution family is fixed before any mechanism is chosen. -/
abbrev DistributionFamily := Set ValueDistribution

/-- MHR priors with the shared finite monopoly benchmark. -/
def mhrFamily : DistributionFamily := {F | F.IsMHR}

/-- An arbitrary sample-dependent price kernel, without scale invariance. -/
structure GeneralSamplePricing where
  price : Kernel ℝ ℝ
  price_isProbability : IsMarkovKernel price
  price_nonnegative : ∀ s, price s (Set.Iio 0) = 0

/-- The scale-invariant truthful comparison used in the FHL baseline. -/
structure ExtendedSamplePricing extends GeneralSamplePricing where
  scale_invariant : ∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 ≤ s →
    Measure.map (fun p : ℝ => c * p) (price s) = price (c * s)

/-- Expected price revenue as a nonnegative extended integral. -/
def GeneralSamplePricing.revenue (P : GeneralSamplePricing)
    (F : ValueDistribution) : ℝ≥0∞ :=
  ∫⁻ s, (∫⁻ p, ENNReal.ofReal (p * F.saleProbability p) ∂P.price s) ∂F.measure

/-- The same expected revenue for the scale-invariant subclass. -/
def ExtendedSamplePricing.revenue (P : ExtendedSamplePricing)
    (F : ValueDistribution) : ℝ≥0∞ :=
  P.toGeneralSamplePricing.revenue F

/-- A single truthful pricing rule works on the entire specified family. -/
def FamilyTruthfulGuarantee (D : DistributionFamily) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ P : ExtendedSamplePricing, ∀ F ∈ D,
    ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * P.revenue F

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end


section

/-!
## Hidden-sample mechanisms with arbitrary actions

The seller fixes an action space and actual sample-dependent outcomes before the prior
is known [FHL21, Section 2]. The buyer's action may depend on both value and prior,
but cannot inspect the hidden sample. Measurability is imposed on actual outcomes, not
on a freely chosen decoder. Best responses and IR hold at every nonnegative value.
Selected and worst-equilibrium guarantees are distinct, and neither can exploit an
empty equilibrium set.

Actions can be reports or complete contingent plans. This specification does not
itself prove a reduction from an extensive-form protocol to this model.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A fixed arbitrary action space with actual hidden-sample outcomes. -/
structure StrategicSampleMechanism where
  Action : Type
  allocation : Action → ℝ → ℝ
  payment : Action → ℝ → ℝ
  allocation_mem : ∀ a s, 0 ≤ allocation a s ∧ allocation a s ≤ 1
  payment_nonnegative : ∀ a s, 0 ≤ payment a s
  allocation_measurable : ∀ a, Measurable (allocation a)
  payment_measurable : ∀ a, Measurable (payment a)

/-- Expected service is bounded even when a payment expectation is infinite. -/
def StrategicSampleMechanism.expectedAllocation (M : StrategicSampleMechanism)
    (F : ValueDistribution) (a : M.Action) : ℝ :=
  ∫ s, M.allocation a s ∂F.measure

/-- A nonnegative extended payment expectation, without an off-path integrability promise. -/
def StrategicSampleMechanism.expectedPayment (M : StrategicSampleMechanism)
    (F : ValueDistribution) (a : M.Action) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (M.payment a s) ∂F.measure

/-- Infinite expected payments give negative infinite utility. -/
def StrategicSampleMechanism.expectedUtility (M : StrategicSampleMechanism)
    (F : ValueDistribution) (v : ℝ) (a : M.Action) : EReal :=
  ((v * M.expectedAllocation F a : ℝ) : EReal) -
    (M.expectedPayment F a : EReal)

/-- Every action is an available deviation; no bid syntax limits the comparison. -/
def StrategicSampleMechanism.IsBestResponse (M : StrategicSampleMechanism)
    (F : ValueDistribution) (v : ℝ) (a : M.Action) : Prop :=
  ∀ alternative, M.expectedUtility F v alternative ≤ M.expectedUtility F v a

/-- A prior-dependent buyer strategy with pointwise optimality and interim IR. Only its
induced outcome needs to carry a measurable representation. -/
structure StrategicSampleEquilibrium (M : StrategicSampleMechanism)
    (F : ValueDistribution) where
  action : ℝ → M.Action
  best_response : ∀ v, 0 ≤ v → M.IsBestResponse F v (action v)
  individually_rational : ∀ v, 0 ≤ v → 0 ≤ M.expectedUtility F v (action v)
  allocation_measurable :
    Measurable (fun z : ℝ × ℝ => M.allocation (action z.1) z.2)
  payment_measurable :
    Measurable (fun z : ℝ × ℝ => M.payment (action z.1) z.2)

/-- Revenue integrates the actual payment over independent value and sample draws. -/
def StrategicSampleEquilibrium.revenue {M : StrategicSampleMechanism}
    {F : ValueDistribution} (e : StrategicSampleEquilibrium M F) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (M.payment (e.action z.1) z.2)
    ∂(F.measure.prod F.measure)

/-- One mechanism works across the fixed class; strategies may adapt to the prior. -/
def FamilyStrategicGuarantee (D : DistributionFamily)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ M : StrategicSampleMechanism, ∀ F ∈ D,
    match ties with
    | .selected => ∃ e : StrategicSampleEquilibrium M F,
        ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * e.revenue
    | .robust => Nonempty (StrategicSampleEquilibrium M F) ∧
        ∀ e : StrategicSampleEquilibrium M F,
          ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * e.revenue

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end


section

/-!
## Candidate tight factors and the MHR revelation gap

Questions take numerical candidates, rather than treating an infimum's existence as a
solution. The baseline compares scale-invariant truthful sample pricing with the
defined hidden-action interface. A scalar real action may encode richer reports, but
no equivalence to every interactive protocol is claimed.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

noncomputable section

/-- Characterize an infimum without requiring endpoint attainment. -/
def IsTightFactor (guarantee : ℝ → Prop) (β : ℝ) : Prop :=
  1 ≤ β ∧
    (∀ γ : ℝ, β < γ → guarantee γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ guarantee γ

/-- The arbitrary-action MHR comparison, with robust tie handling and pointwise best
responses. The action space is fixed with the mechanism, before the prior. -/
def StrategicMHRRevelationGapQuestion
    (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  IsTightFactor (FamilyTruthfulGuarantee mhrFamily) truthfulFactor ∧
    IsTightFactor (FamilyStrategicGuarantee mhrFamily .robust) strategicFactor ∧
    gap = truthfulFactor / strategicFactor

/-- Reference strategic-action question. Extensive-form equivalence is not assumed. -/
abbrev ReferenceMHRRevelationGapQuestion := StrategicMHRRevelationGapQuestion

/-- A numerical answer supplies both factors as well as their ratio. -/
structure MHRGapAnswer where
  truthfulFactor : ℝ
  strategicFactor : ℝ
  gap : ℝ

/-- Correctness of a numerical answer; no defining infimum counts as an explicit answer. -/
def MHRGapAnswer.IsCorrect (answer : MHRGapAnswer) : Prop :=
  ReferenceMHRRevelationGapQuestion answer.truthfulFactor answer.strategicFactor answer.gap

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

/-- Supply both tight factors and their ratio under the stated prior/equilibrium
conventions. -/
theorem mhrRevelationGap :
    MHRGapAnswer.IsCorrect (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample
