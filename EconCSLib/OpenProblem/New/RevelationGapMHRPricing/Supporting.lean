/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.RevelationGapMHRPricing.Problem

/-!
# RevelationGapMHRPricing: supporting material

Auxiliary definitions and lemmas for the problem statement.
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

/-- A prior-independent, scale-invariant price kernel. Integrability concerns expected
revenue, not running time. -/
structure TruthfulSamplePricing where
  price : Kernel ℝ ℝ
  price_isProbability : IsMarkovKernel price
  price_nonnegative : ∀ s, price s (Set.Iio 0) = 0
  scale_invariant : ∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 ≤ s →
    Measure.map (fun p : ℝ => c * p) (price s) = price (c * s)
  revenue_integrable : ∀ F : MHRDistribution,
    (∀ᵐ s ∂F.1.measure,
      Integrable (fun p => p * F.1.saleProbability p) (price s)) ∧
    Integrable (fun s => ∫ p, p * F.1.saleProbability p ∂price s) F.1.measure

/-- The sample and value are independent draws from the same prior. -/
def TruthfulSamplePricing.revenue
    (P : TruthfulSamplePricing) (F : MHRDistribution) : ℝ :=
  ∫ s, (∫ p, p * F.1.saleProbability p ∂P.price s) ∂F.1.measure

/-- Sample-bid allocation; negative samples lie outside the economic domain. -/
def sampleBidAllocation : OneBidAction → ℝ → ℝ
  | .optOut, _ => 0
  | .bid b, s => if s ≤ b.1 then 1 else 0
  | .limitBid, _ => 1

/-- Sample-bid payments are charged even on losing bids; the limit action pays the scaled
sample. -/
def sampleBidPayment (a : ℝ) : OneBidAction → ℝ → ℝ
  | .optOut, _ => 0
  | .bid b, s => a * min b.1 (max s 0)
  | .limitBid, s => a * max s 0

/-- Both allocation and payment are specified for every admissible action, not just
equilibrium behavior. -/
def OneSampleProtocol.IsSampleBid (M : OneSampleProtocol) (a : ℝ) : Prop :=
  0 < a ∧ ∀ action s, 0 ≤ s →
    M.allocation action s = sampleBidAllocation action s ∧
    M.payment action s = sampleBidPayment a action s

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

/-- The cumulative distribution function, including equality at atoms. -/
def ValueDistribution.cdf (F : ValueDistribution) (x : ℝ) : ℝ :=
  (F.measure (Set.Iic x)).toReal

/-- Continuous positive-density regularity on the interior quantiles [FHL21, Section 2].
This named smooth subclass is not a definition of all possible atomic regular priors. -/
def ValueDistribution.IsSmoothRegular (F : ValueDistribution) : Prop :=
  NoAtoms F.measure ∧ ∃ density : ℝ → ℝ,
    (∀ x : ℝ, 0 < F.cdf x → 0 < F.saleProbability x →
      HasDerivAt F.cdf (density x) x ∧ 0 < density x) ∧
    MonotoneOn (fun x => x - F.saleProbability x / density x)
      {x | 0 < F.cdf x ∧ 0 < F.saleProbability x}

/-- Smooth regular priors, allowing unbounded support and infinite mean. -/
def smoothRegularFamily : DistributionFamily := {F | F.IsSmoothRegular}

/-- All nonnegative priors with finite monopoly benchmark, without regularity. -/
def unrestrictedFamily : DistributionFamily := Set.univ

/-- A one-message hidden-sample protocol; every realized payment is finite and
nonnegative. Expected payment may be infinite under a heavy-tailed prior. -/
structure ExtendedOneSampleProtocol where
  allocation : OneBidAction → ℝ → ℝ
  payment : OneBidAction → ℝ → ℝ
  allocation_mem : ∀ a s, 0 ≤ allocation a s ∧ allocation a s ≤ 1
  payment_nonnegative : ∀ a s, 0 ≤ payment a s
  allocation_measurable : ∀ a, Measurable (allocation a)
  payment_measurable : ∀ a, Measurable (payment a)
  optOut_allocation : ∀ s, allocation .optOut s = 0
  optOut_payment : ∀ s, payment .optOut s = 0

/-- Interim allocation is bounded, hence its ordinary expectation is well defined. -/
def ExtendedOneSampleProtocol.expectedAllocation (M : ExtendedOneSampleProtocol)
    (F : ValueDistribution) (a : OneBidAction) : ℝ :=
  ∫ s, M.allocation a s ∂F.measure

/-- Nonnegative expected payment, retaining the possibility of infinity. -/
def ExtendedOneSampleProtocol.expectedPayment (M : ExtendedOneSampleProtocol)
    (F : ValueDistribution) (a : OneBidAction) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (M.payment a s) ∂F.measure

/-- Finite expected value minus possibly infinite expected payment. -/
def ExtendedOneSampleProtocol.expectedUtility (M : ExtendedOneSampleProtocol)
    (F : ValueDistribution) (v : ℝ) (a : OneBidAction) : EReal :=
  ((v * M.expectedAllocation F a : ℝ) : EReal) -
    (M.expectedPayment F a : EReal)

/-- Best responses include the opt-out action and every other allowed action. -/
def ExtendedOneSampleProtocol.IsBestResponse (M : ExtendedOneSampleProtocol)
    (bids : BidConvention) (F : ValueDistribution) (v : ℝ) (a : OneBidAction) : Prop :=
  bids.Allows a ∧ ∀ alternative, bids.Allows alternative →
    M.expectedUtility F v alternative ≤ M.expectedUtility F v a

/-- The buyer's strategy cannot inspect the independent hidden sample. -/
structure ExtendedOneSampleEquilibrium (M : ExtendedOneSampleProtocol)
    (bids : BidConvention) (F : ValueDistribution) where
  action : ℝ → OneBidAction
  best_response : ∀ᵐ v ∂F.measure, M.IsBestResponse bids F v (action v)
  allocation_measurable :
    Measurable (fun z : ℝ × ℝ => M.allocation (action z.1) z.2)
  payment_measurable :
    Measurable (fun z : ℝ × ℝ => M.payment (action z.1) z.2)

/-- Expected equilibrium revenue under independent buyer-value and sample draws. -/
def ExtendedOneSampleEquilibrium.revenue
    {M : ExtendedOneSampleProtocol} {bids : BidConvention} {F : ValueDistribution}
    (e : ExtendedOneSampleEquilibrium M bids F) : ℝ≥0∞ :=
  ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (M.payment (e.action z.1) z.2)
    ∂(F.measure.prod F.measure)

/-- General truthful sample pricing on an arbitrary family. No scale-invariance
restriction may create an artificial loss on a non-scale-closed family. -/
def FamilyUnrestrictedTruthfulGuarantee (D : DistributionFamily) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ P : GeneralSamplePricing, ∀ F ∈ D,
    ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * P.revenue F

/-- Removing scale invariance can only enlarge the achievable guarantee set. -/
theorem FamilyTruthfulGuarantee.unrestricted {D : DistributionFamily} {β : ℝ}
    (h : FamilyTruthfulGuarantee D β) : FamilyUnrestrictedTruthfulGuarantee D β := by
  obtain ⟨hβ, P, hP⟩ := h
  exact ⟨hβ, P.toGeneralSamplePricing, hP⟩

/-- A fixed protocol admits equilibria and satisfies the chosen equilibrium guarantee. -/
def FamilyOneBidGuarantee (D : DistributionFamily) (bids : BidConvention)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ M : ExtendedOneSampleProtocol, ∀ F ∈ D,
    match ties with
    | .selected => ∃ e : ExtendedOneSampleEquilibrium M bids F,
        ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * e.revenue
    | .robust => Nonempty (ExtendedOneSampleEquilibrium M bids F) ∧
        ∀ e : ExtendedOneSampleEquilibrium M bids F,
          ENNReal.ofReal F.monopolyRevenue ≤ ENNReal.ofReal β * e.revenue

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

/-- The old action interface is a concrete instance of the arbitrary-action data. -/
def ExtendedOneSampleProtocol.toStrategic (M : ExtendedOneSampleProtocol) :
    StrategicSampleMechanism where
  Action := OneBidAction
  allocation := M.allocation
  payment := M.payment
  allocation_mem := M.allocation_mem
  payment_nonnegative := M.payment_nonnegative
  allocation_measurable := M.allocation_measurable
  payment_measurable := M.payment_measurable

/-- Bounded measurable service has a genuine expectation for every allowed prior. -/
theorem StrategicSampleMechanism.allocation_integrable (M : StrategicSampleMechanism)
    (F : ValueDistribution) (a : M.Action) :
    Integrable (M.allocation a) F.measure := by
  letI : IsProbabilityMeasure F.measure := F.probability
  refine (integrable_const (1 : ℝ)).mono'
    (M.allocation_measurable a).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (M.allocation_mem a s).1]
    exact (M.allocation_mem a s).2

/-- All utility maximizers give the same utility, even with extended payments. -/
theorem StrategicSampleMechanism.IsBestResponse.utility_eq
    {M : StrategicSampleMechanism} {F : ValueDistribution} {v : ℝ}
    {a b : M.Action} (ha : M.IsBestResponse F v a) (hb : M.IsBestResponse F v b) :
    M.expectedUtility F v a = M.expectedUtility F v b :=
  le_antisymm (hb a) (ha b)

/-- Once an IR equilibrium exists, IR cannot exclude any other best response. This
single-buyer fact does not assume an added withdrawal action. -/
theorem StrategicSampleEquilibrium.ir_of_best_response
    {M : StrategicSampleMechanism} {F : ValueDistribution}
    (e : StrategicSampleEquilibrium M F) (v : ℝ) (hv : 0 ≤ v)
    (a : M.Action) (ha : M.IsBestResponse F v a) :
    0 ≤ M.expectedUtility F v a :=
  (e.individually_rational v hv).trans (ha (e.action v))

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end


section

/-!
## Pointwise mixed best responses

These auxiliary results concern one fixed buyer value and prior. They do not change
the open question or assert completeness for mixed, value-dependent, or interactive
protocols. In particular, pointwise almost-everywhere statements must not be
interchanged with a simultaneous statement at every real value.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- An integrable function bounded above by its own mean equals that bound a.e. -/
theorem ae_eq_constant_of_integral_ge {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] {u : Seed → ℝ} {c : ℝ}
    (hu : Integrable u μ) (hle : ∀ᵐ seed ∂μ, u seed ≤ c)
    (hge : c ≤ ∫ seed, u seed ∂μ) : u =ᵐ[μ] (fun _ => c) := by
  have hupper : (∫ seed, u seed ∂μ) ≤ c := by
    simpa using integral_mono_ae hu (integrable_const c) hle
  apply (integral_eq_iff_of_ae_le hu (integrable_const c) hle).mp
  simpa using le_antisymm hupper hge

theorem StrategicSampleMechanism.expectedAllocation_mem_unitInterval
    (M : StrategicSampleMechanism) (F : ValueDistribution) (a : M.Action) :
    0 ≤ M.expectedAllocation F a ∧ M.expectedAllocation F a ≤ 1 := by
  letI : IsProbabilityMeasure F.measure := F.probability
  refine ⟨integral_nonneg (fun s => (M.allocation_mem a s).1), ?_⟩
  have h := integral_mono (M.allocation_integrable F a) (integrable_const (1 : ℝ))
    (fun s => (M.allocation_mem a s).2)
  simpa [expectedAllocation] using h

/-- A nonnegative extended quasilinear utility cannot pay infinite expectation. -/
theorem payment_ne_top_of_utility_nonnegative (service : ℝ) (payment : ℝ≥0∞)
    (h : 0 ≤ (service : EReal) - (payment : EReal)) : payment ≠ ∞ := by
  intro hp
  simp [hp] at h

/-- Finite expected payments make the existing extended utility an honest real value. -/
theorem StrategicSampleMechanism.expectedUtility_eq_coe
    (M : StrategicSampleMechanism) (F : ValueDistribution) (v : ℝ) (a : M.Action)
    (hp : M.expectedPayment F a ≠ ∞) :
    M.expectedUtility F v a =
      ((v * M.expectedAllocation F a - (M.expectedPayment F a).toReal : ℝ) : EReal) := by
  rw [expectedUtility, EReal.coe_sub, EReal.coe_ennreal_toReal hp]

/-- Mixed utility uses the same interim allocation and nonnegative extended payment. No
integrability default is used for payments. -/
def StrategicSampleMechanism.mixedUtility {Seed : Type*} [MeasurableSpace Seed]
    (M : StrategicSampleMechanism) (F : ValueDistribution) (v : ℝ)
    (μ : Measure Seed) (action : Seed → M.Action) : EReal :=
  ((v * ∫ seed, M.expectedAllocation F (action seed) ∂μ : ℝ) : EReal) -
    ((∫⁻ seed, M.expectedPayment F (action seed) ∂μ : ℝ≥0∞) : EReal)

/-- With a pure IR maximizer, any mixed response weakly beating every pure deviation
chooses pure best responses almost surely. Measurability is required only for this
particular action lottery's actual interim outcomes. Finiteness of mixed payment and
integrability of its utility are consequences, not premises. -/
theorem StrategicSampleMechanism.ae_best_response_of_mixed_best_response
    {Seed : Type*} [MeasurableSpace Seed]
    (M : StrategicSampleMechanism) (F : ValueDistribution) (v : ℝ)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (action : Seed → M.Action)
    (a₀ : M.Action) (hbest₀ : M.IsBestResponse F v a₀)
    (hIR₀ : 0 ≤ M.expectedUtility F v a₀)
    (halloc : Measurable (fun seed => M.expectedAllocation F (action seed)))
    (hpay : Measurable (fun seed => M.expectedPayment F (action seed)))
    (hmixed : ∀ a, M.expectedUtility F v a ≤ M.mixedUtility F v μ action) :
    ∀ᵐ seed ∂μ, M.IsBestResponse F v (action seed) := by
  let q : Seed → ℝ := fun seed => M.expectedAllocation F (action seed)
  let p : Seed → ℝ≥0∞ := fun seed => M.expectedPayment F (action seed)
  let u : Seed → ℝ := fun seed => v * q seed - (p seed).toReal
  let c : ℝ := v * M.expectedAllocation F a₀ - (M.expectedPayment F a₀).toReal
  have hp₀ : M.expectedPayment F a₀ ≠ ∞ :=
    payment_ne_top_of_utility_nonnegative _ _ hIR₀
  have hfinite : (∫⁻ seed, p seed ∂μ) ≠ ∞ :=
    payment_ne_top_of_utility_nonnegative _ _ (hIR₀.trans (hmixed a₀))
  have hp_ae : ∀ᵐ seed ∂μ, p seed < ∞ := ae_lt_top hpay hfinite
  have hq : Integrable q μ := by
    refine (integrable_const (1 : ℝ)).mono' halloc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun seed => by
      rw [Real.norm_eq_abs, abs_of_nonneg (M.expectedAllocation_mem_unitInterval F _).1]
      exact (M.expectedAllocation_mem_unitInterval F _).2
  have hp : Integrable (fun seed => (p seed).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hpay.aemeasurable hfinite
  have hu : Integrable u μ := (hq.const_mul v).sub hp
  have hu_eq : ∀ᵐ seed ∂μ,
      M.expectedUtility F v (action seed) = (u seed : EReal) := by
    filter_upwards [hp_ae] with seed hs
    exact M.expectedUtility_eq_coe F v (action seed) hs.ne
  have hc_eq : M.expectedUtility F v a₀ = (c : EReal) :=
    M.expectedUtility_eq_coe F v a₀ hp₀
  have hmean : M.mixedUtility F v μ action = ((∫ seed, u seed ∂μ : ℝ) : EReal) := by
    rw [show (∫ seed, u seed ∂μ) =
        v * (∫ seed, q seed ∂μ) - (∫⁻ seed, p seed ∂μ).toReal by
      rw [show u = (fun seed => v * q seed - (p seed).toReal) from rfl,
        integral_sub (hq.const_mul v) hp, integral_const_mul,
        integral_toReal hpay.aemeasurable hp_ae]]
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hfinite]
    rfl
  have hle : ∀ᵐ seed ∂μ, u seed ≤ c := by
    filter_upwards [hu_eq] with seed hs
    exact EReal.coe_le_coe_iff.mp (by simpa [hs, hc_eq] using hbest₀ (action seed))
  have hge : c ≤ ∫ seed, u seed ∂μ :=
    EReal.coe_le_coe_iff.mp (by simpa [hc_eq, hmean] using hmixed a₀)
  have heq := ae_eq_constant_of_integral_ge μ hu hle hge
  filter_upwards [hu_eq, heq] with seed hs heq
  intro alternative
  calc
    M.expectedUtility F v alternative ≤ M.expectedUtility F v a₀ := hbest₀ alternative
    _ = M.expectedUtility F v (action seed) := by rw [hc_eq, hs, heq]

/-- Every lower bound holding at all pure maximizers also holds in expectation for a mixed
maximizer, at this fixed value and prior. -/
theorem StrategicSampleMechanism.mixed_payment_lower_bound_of_pure
    {Seed : Type*} [MeasurableSpace Seed]
    (M : StrategicSampleMechanism) (F : ValueDistribution) (v : ℝ)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (action : Seed → M.Action)
    (a₀ : M.Action) (hbest₀ : M.IsBestResponse F v a₀)
    (hIR₀ : 0 ≤ M.expectedUtility F v a₀)
    (halloc : Measurable (fun seed => M.expectedAllocation F (action seed)))
    (hpay : Measurable (fun seed => M.expectedPayment F (action seed)))
    (hmixed : ∀ a, M.expectedUtility F v a ≤ M.mixedUtility F v μ action)
    (lower : ℝ≥0∞)
    (hlower : ∀ a, M.IsBestResponse F v a → lower ≤ M.expectedPayment F a) :
    lower ≤ ∫⁻ seed, M.expectedPayment F (action seed) ∂μ := by
  have hsupport := M.ae_best_response_of_mixed_best_response
    F v μ action a₀ hbest₀ hIR₀ halloc hpay hmixed
  have hbound : ∀ᵐ seed ∂μ, lower ≤ M.expectedPayment F (action seed) :=
    hsupport.mono fun seed hs => hlower (action seed) hs
  simpa using lintegral_mono_ae hbound

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

/-- A randomized price rule is fixed before the prior. -/
def TruthfulMHRGuarantee (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ P : TruthfulSamplePricing, ∀ F : MHRDistribution,
    F.1.monopolyRevenue ≤ β * P.revenue F

/-- One finite-interim-payment protocol works for all priors; buyer best responses may
depend on the prior. The extended reference is defined below. -/
def OneBidMHRGuarantee (bids : BidConvention)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  ∃ M : OneSampleProtocol, M.AchievesFactor bids ties β

/-- The multiplier and sample-bid protocol are chosen before all priors. -/
def SampleBidMHRGuarantee (bids : BidConvention)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  ∃ a : ℝ, ∃ M : OneSampleProtocol,
    M.IsSampleBid a ∧ M.AchievesFactor bids ties β

/-- Candidate optimal factor for truthful sample pricing. -/
def TruthfulMHRFactorQuestion (β : ℝ) : Prop :=
  IsTightFactor TruthfulMHRGuarantee β

/-- Candidate factor for the specified one-bid and equilibrium conventions. -/
def OneBidMHRFactorQuestion (bids : BidConvention)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  IsTightFactor (OneBidMHRGuarantee bids ties) β

/-- Determine both factors and their ratio; each factor is at least one. -/
def OneBidMHRRevelationGapQuestion (bids : BidConvention)
    (ties : EquilibriumConvention) (truthfulFactor oneBidFactor gap : ℝ) : Prop :=
  TruthfulMHRFactorQuestion truthfulFactor ∧
    OneBidMHRFactorQuestion bids ties oneBidFactor ∧
    gap = truthfulFactor / oneBidFactor

/-- Sample-bid optimality within the finite-interim-payment subclass, without requiring a
minimizing multiplier. -/
def SampleBidFamilyOptimalityQuestion (bids : BidConvention)
    (ties : EquilibriumConvention) (β : ℝ) : Prop :=
  OneBidMHRFactorQuestion bids ties β ∧
    IsTightFactor (SampleBidMHRGuarantee bids ties) β

/-- A particular multiplier attains the finite-interim subclass's optimal factor. -/
def SampleBidAttainsOptimalFactorQuestion (bids : BidConvention)
    (ties : EquilibriumConvention) (a β : ℝ) : Prop :=
  OneBidMHRFactorQuestion bids ties β ∧
    ∃ M : OneSampleProtocol, M.IsSampleBid a ∧ M.AchievesFactor bids ties β

/-- The original finite-interim-payment subclass, retained explicitly. -/
def FiniteInterimMHRRevelationGapQuestion
    (truthfulFactor oneBidFactor gap : ℝ) : Prop :=
  OneBidMHRRevelationGapQuestion .withLimitBid .robust
    truthfulFactor oneBidFactor gap

/-- MHR comparison allowing infinite expected payments on unused actions. Best responses
still compare against the finite zero-payment opt-out action. -/
def ExtendedMHRRevelationGapQuestion
    (truthfulFactor oneBidFactor gap : ℝ) : Prop :=
  IsTightFactor (FamilyTruthfulGuarantee mhrFamily) truthfulFactor ∧
    IsTightFactor (FamilyOneBidGuarantee mhrFamily .withLimitBid .robust)
      oneBidFactor ∧ gap = truthfulFactor / oneBidFactor

/-- Tight truthful and one-bid factors on the explicitly smooth regular family. -/
def SmoothRegularGapQuestion (truthfulFactor oneBidFactor gap : ℝ) : Prop :=
  IsTightFactor (FamilyTruthfulGuarantee smoothRegularFamily) truthfulFactor ∧
    IsTightFactor (FamilyOneBidGuarantee smoothRegularFamily .withLimitBid .robust)
      oneBidFactor ∧ gap = truthfulFactor / oneBidFactor

/-- Beyond regularity: arbitrarily large finite-factor gaps on nonempty subfamilies.
Truthful pricing is unrestricted, so a choice of scale cannot artificially penalize
that side. -/
def UnboundedFiniteOneBidRevelationGapsStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∃ D : DistributionFamily, D.Nonempty ∧
    ∃ truthfulFactor oneBidFactor : ℝ,
      IsTightFactor (FamilyUnrestrictedTruthfulGuarantee D) truthfulFactor ∧
      IsTightFactor (FamilyOneBidGuarantee D .withLimitBid .robust) oneBidFactor ∧
      R ≤ truthfulFactor / oneBidFactor

/-- Compatibility name for the finite-factor subfamily variant only. -/
abbrev UnboundedOneBidRevelationGapsStatement := UnboundedFiniteOneBidRevelationGapsStatement

/-- A separate infinite-factor possibility: no finite truthful guarantee, but some finite
guarantee in the stated non-revelation interface. -/
def InfiniteTruthfulFiniteOneBidGapStatement : Prop :=
  ∃ D : DistributionFamily, D.Nonempty ∧
    (∀ β : ℝ, ¬ FamilyUnrestrictedTruthfulGuarantee D β) ∧
      ∃ β : ℝ, FamilyOneBidGuarantee D .withLimitBid .robust β

/-- The smooth regular question with arbitrary actions. -/
def StrategicSmoothRegularGapQuestion (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  IsTightFactor (FamilyTruthfulGuarantee smoothRegularFamily) truthfulFactor ∧
    IsTightFactor (FamilyStrategicGuarantee smoothRegularFamily .robust) strategicFactor ∧
    gap = truthfulFactor / strategicFactor

/-- Unbounded finite-factor gaps over nonempty families in the arbitrary-action model. -/
def UnboundedFiniteStrategicRevelationGapsStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∃ D : DistributionFamily, D.Nonempty ∧
    ∃ truthfulFactor strategicFactor : ℝ,
      IsTightFactor (FamilyUnrestrictedTruthfulGuarantee D) truthfulFactor ∧
      IsTightFactor (FamilyStrategicGuarantee D .robust) strategicFactor ∧
      R ≤ truthfulFactor / strategicFactor

/-- A separate infinite truthful factor with a finite arbitrary-action guarantee. -/
def InfiniteTruthfulFiniteStrategicGapStatement : Prop :=
  ∃ D : DistributionFamily, D.Nonempty ∧
    (∀ β : ℝ, ¬ FamilyUnrestrictedTruthfulGuarantee D β) ∧
      ∃ β : ℝ, FamilyStrategicGuarantee D .robust β

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapMHROneSample

end
