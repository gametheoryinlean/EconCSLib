import EconCSLib.MechanismDesign.Auction.AuctionBasic
import EconCSLib.MechanismDesign.Auction.MechBayesian
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# EconCSLib.MechanismDesign.Auction.BayesianSingleItem

Single-item auctions in incomplete-information settings, modeled as direct
Bayesian mechanisms with transfers.

This file specializes the general interface from `MechanismDesign/Auction/MechBayesian` to the
standard direct-revelation single-item auction environment:

* each agent reports a scalar type in `ℝ`
* the type profile is drawn from a common prior measure
* each agent receives a winning probability `Q_i(t) ∈ [0,1]`
* payments are determined by the mechanism's payment rule

The continuous private-value data are recorded separately via
`ContinuousTypeProfile`, so Myerson-style regularity assumptions can be attached
without forcing them into the core mechanism fields.

Interim objects are defined against an explicit family of opponent-type priors
`μᵢ` on profiles `t₋ᵢ`. This keeps the generic measure-based definitions
separate from any density-based formulas one may later derive under
independence.

## Main definitions and tools

* `BayesianSingleItemAuction`, the single-item specialization of
  `DirectBayesianMechanismWithTransfers`;
* `IsFeasible` and `isFeasible_of_optionalWinnerAllocation`, including a
  reusable feasibility route for deterministic optional-winner rules;
* seller-side revenue and reserve-value surplus objects:
  `sellerRevenue`, `expectedSellerRevenue`, `withheldProbability`,
  `sellerSurplusWithReserveValue`;
* product-prior and opponent-prior constructions, together with atomless and
  almost-everywhere support facts under independent type priors;
* interim allocation, payment, utility, and integrability interfaces;
* Fubini-style identities and almost-everywhere congruence lemmas for expected
  payment revenue.
-/

open MeasureTheory

/-- A scalar type distribution on the interval `[0, ω]`, recorded by its CDF. -/
structure TypeCDF (ω : ℝ) where
  /-- Upper bound of the support interval is nonnegative. -/
  omega_nonneg : 0 ≤ ω
  /-- Cumulative distribution function. -/
  cdf : ℝ → ℝ
  /-- Monotonicity of the CDF on the support interval. -/
  monotoneOn_cdf : MonotoneOn cdf (Set.Icc 0 ω)
  /-- Normalization at the lower endpoint. -/
  cdf_zero : cdf 0 = 0
  /-- Normalization at the upper endpoint. -/
  cdf_upper : cdf ω = 1
  /-- Smoothness assumption used in continuous-type auction theory. -/
  differentiableOn_cdf : DifferentiableOn ℝ cdf (Set.Ioo 0 ω)

/-- Agent-specific continuous private-value data. -/
structure ContinuousTypeProfile (I : Type*) where
  /-- Agent-specific upper bounds `ωᵢ` for the type support. -/
  omega : I → ℝ
  /-- Agent-specific CDFs `Fᵢ` on `[0, ωᵢ]`. -/
  cdf : ∀ i, TypeCDF (omega i)

/-- Opponent profiles for agent `i`, with constant coordinate type `X`. -/
abbrev OpponentProfile (I : Type*) (X : Type*) (i : I) := ∀ _ : {j // j ≠ i}, X

/-- Opponent type profiles for real-valued auction types. -/
abbrev OpponentTypeProfile (I : Type*) (i : I) := OpponentProfile I ℝ i

/-- A direct Bayesian single-item auction with scalar private types and
probabilistic allocation.

The allocation rule returns a function `Q : I → ℝ`, where `Q i` is agent `i`'s
probability of receiving the item under the reported type profile. This matches
the allocation/payment shape of `SingleParameterMechanism I ℝ`.

The mechanism is direct: the message space equals the type space, which is taken
to be `ℝ` for each agent, and payments are real-valued. Continuous-type data
are stored separately in `typeData`, while the Bayesian prior is recorded by
extra fields. -/

structure BayesianSingleItemAuction (I : Type*)
    extends SingleParameterMechanism I ℝ where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ _ : I, ℝ)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Opponent-type prior `μᵢ` used for interim expectations conditional on a
  fixed report by agent `i`. -/
  opponentPrior : (i : I) → MeasureTheory.Measure (OpponentTypeProfile I i)
  /-- Each opponent-type prior is a probability measure. -/
  prob_opponentPrior :
    ∀ i : I, MeasureTheory.IsProbabilityMeasure (opponentPrior i)
  /-- Continuous private-value support and CDF data for each agent. -/
  typeData : ContinuousTypeProfile I

-- Intentionally global so integration lemmas can recover the auction prior
-- from the auction term without repeated local instance setup.
attribute [instance] BayesianSingleItemAuction.prob_prior

namespace BayesianSingleItemAuction

variable {I : Type*}

section profile

variable {X : Type*}

/-- Insert one coordinate into an opponent profile. -/
noncomputable def profileInsert (i : I) (x : X) (t : OpponentProfile I X i) :
    ∀ _ : I, X := by
  classical
  exact fun j => if h : j = i then x else t ⟨j, h⟩

/-- The inserted coordinate is the inserted value. -/
@[simp] theorem profileInsert_self (i : I) (x : X) (t : OpponentProfile I X i) :
    profileInsert i x t i = x := by
  simp [profileInsert]

/-- Other coordinates come from the opponent profile. -/
@[simp] theorem profileInsert_of_ne
    (i : I) (x : X) (t : OpponentProfile I X i) {j : I} (hji : j ≠ i) :
    profileInsert i x t j = t ⟨j, hji⟩ := by
  simp [profileInsert, hji]

end profile

instance (A : BayesianSingleItemAuction I) (i : I) :
    MeasureTheory.IsProbabilityMeasure (A.opponentPrior i) :=
  A.prob_opponentPrior i

/-- View an incomplete-information single-item auction as the corresponding
direct Bayesian mechanism with transfers. -/
def toDirectBayesianMechanismWithTransfers (A : BayesianSingleItemAuction I) :
    DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ where
  prior := A.prior
  prob_prior := A.prob_prior
  allocationRule := A.allocationRule
  paymentRule := A.paymentRule

instance : Coe (BayesianSingleItemAuction I)
    (DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ) where
  coe := toDirectBayesianMechanismWithTransfers

/-- The allocation rule respects the single-item probability budget. -/
def RespectsSingleItemCapacity [Fintype I] (A : BayesianSingleItemAuction I) : Prop :=
  ∀ t : ∀ _ : I, ℝ, (∑ i, A.allocationRule t i) ≤ 1

/-- Feasibility for a probabilistic single-item auction:

* each winning probability lies in `[0,1]`
* the total allocation probability is at most `1` -/
def IsFeasible [Fintype I] (A : BayesianSingleItemAuction I) : Prop :=
  A.IsAllocFeasible ∧ A.RespectsSingleItemCapacity

/-- A deterministic optional winner, encoded as a `{0,1}` allocation vector, is feasible. -/
theorem isFeasible_of_optionalWinnerAllocation
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    (winner : (I → ℝ) → Option I)
    (halloc : A.allocationRule = fun b i => if winner b = some i then (1 : ℝ) else 0) :
    A.IsFeasible := by
  constructor
  · intro b i
    rw [halloc]
    by_cases hwin : winner b = some i <;> simp [hwin]
  · intro b
    rw [halloc]
    cases hwin : winner b with
    | none =>
        simp [hwin]
    | some k =>
        simp [hwin, Finset.mem_univ]

/-- Seller revenue at a report profile. -/
noncomputable def sellerRevenue [Fintype I]
    (A : BayesianSingleItemAuction I) (t : ∀ _ : I, ℝ) : ℝ :=
  ∑ i, A.paymentRule t i

/-- Ex-ante seller revenue. -/
noncomputable def expectedSellerRevenue [Fintype I]
    (A : BayesianSingleItemAuction I) : ℝ :=
  ∫ t, A.sellerRevenue t ∂A.prior

/-- Probability that the item is withheld at a report profile.

For feasible allocation rules this is the leftover single-item mass. -/
noncomputable def withheldProbability [Fintype I]
    (A : BayesianSingleItemAuction I) (t : ∀ _ : I, ℝ) : ℝ :=
  1 - ∑ i, A.allocationRule t i

/-- Seller surplus at a report profile when the seller values retaining the item
at `sellerValue`. This extends seller revenue by adding the seller's value for
the unsold item. -/
noncomputable def sellerSurplusWithReserveValue [Fintype I]
    (A : BayesianSingleItemAuction I) (sellerValue : ℝ) (t : ∀ _ : I, ℝ) : ℝ :=
  A.sellerRevenue t + sellerValue * A.withheldProbability t

/-- Ex-ante seller surplus with a seller reservation value. -/
noncomputable def expectedSellerSurplusWithReserveValue [Fintype I]
    (A : BayesianSingleItemAuction I) (sellerValue : ℝ) : ℝ :=
  ∫ t, A.sellerSurplusWithReserveValue sellerValue t ∂A.prior

/-- Zero seller value recovers pointwise seller revenue. -/
@[simp] theorem sellerSurplusWithReserveValue_zero [Fintype I]
    (A : BayesianSingleItemAuction I) (t : ∀ _ : I, ℝ) :
    A.sellerSurplusWithReserveValue 0 t = A.sellerRevenue t := by
  simp [sellerSurplusWithReserveValue]

/-- Zero seller value recovers expected seller revenue. -/
@[simp] theorem expectedSellerSurplusWithReserveValue_zero [Fintype I]
    (A : BayesianSingleItemAuction I) :
    A.expectedSellerSurplusWithReserveValue 0 = A.expectedSellerRevenue := by
  simp [expectedSellerSurplusWithReserveValue, expectedSellerRevenue]

/-- Agent `i`'s one-dimensional density, defined as the derivative of the
stored CDF `Fᵢ`. -/
noncomputable def typeDensity (A : BayesianSingleItemAuction I) (i : I) : ℝ → ℝ :=
  deriv (A.typeData.cdf i).cdf

/-- Type measure generated by `fᵢ` on `[0, ωᵢ]`. -/
noncomputable def typeMeasure (A : BayesianSingleItemAuction I) (i : I) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (A.typeData.omega i))).withDensity
    fun v => ENNReal.ofReal (A.typeDensity i v)

/-- The joint density `f(t)` of the type profile under independence.

If the agents' types are independent with agent-specific one-dimensional
densities `fᵢ`, then the profile density is the product `∏ᵢ fᵢ(tᵢ)`. -/
noncomputable def jointDensity [Fintype I] (A : BayesianSingleItemAuction I)
    (t : ∀ _ : I, ℝ) : ℝ :=
  Finset.univ.prod fun i => A.typeDensity i (t i)

/-- Product type prior. -/
noncomputable def productPrior [Fintype I] (A : BayesianSingleItemAuction I) :
    Measure (∀ _ : I, ℝ) :=
  Measure.pi fun i => A.typeMeasure i

/-- Product prior over `i`'s opponents. -/
noncomputable def opponentProductPrior [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (i : I) : Measure (OpponentTypeProfile I i) :=
  Measure.pi fun j : {j // j ≠ i} => A.typeMeasure j

/-- Stored priors are the product priors. -/
def HasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) : Prop :=
  A.prior = A.productPrior ∧
    ∀ i : I, A.opponentPrior i = A.opponentProductPrior i

/-- Auctions over the same Bayesian selling environment. -/
def HasSameSellingEnvironment
    (A B : BayesianSingleItemAuction I) : Prop :=
  B.prior = A.prior ∧
    B.opponentPrior = A.opponentPrior ∧
      B.typeData = A.typeData

theorem HasSameSellingEnvironment.prior_eq
    {A B : BayesianSingleItemAuction I}
    (h : A.HasSameSellingEnvironment B) :
    B.prior = A.prior :=
  h.1

theorem HasSameSellingEnvironment.opponentPrior_eq
    {A B : BayesianSingleItemAuction I}
    (h : A.HasSameSellingEnvironment B) :
    B.opponentPrior = A.opponentPrior :=
  h.2.1

theorem HasSameSellingEnvironment.typeData_eq
    {A B : BayesianSingleItemAuction I}
    (h : A.HasSameSellingEnvironment B) :
    B.typeData = A.typeData :=
  h.2.2

instance productPrior_isProbabilityMeasure [Fintype I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] :
    IsProbabilityMeasure A.productPrior := by
  dsimp [productPrior]
  infer_instance

instance opponentProductPrior_isProbabilityMeasure [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (i : I)
    [∀ j : I, IsProbabilityMeasure (A.typeMeasure j)] :
    IsProbabilityMeasure (A.opponentProductPrior i) := by
  dsimp [opponentProductPrior]
  infer_instance

/-- Each one-dimensional type measure is atomless: it is obtained from a
restriction of Lebesgue measure by a density. -/
instance typeMeasure_noAtoms (A : BayesianSingleItemAuction I) (i : I) :
    NoAtoms (A.typeMeasure i) := by
  dsimp [typeMeasure]
  infer_instance

/-- A one-dimensional type drawn from `A.typeMeasure i` lies in its support
interval almost surely. -/
theorem ae_typeMeasure_mem_Ioc (A : BayesianSingleItemAuction I) (i : I) :
    ∀ᵐ v ∂A.typeMeasure i, v ∈ Set.Ioc 0 (A.typeData.omega i) := by
  dsimp [typeMeasure]
  exact
    (withDensity_absolutelyContinuous
      (volume.restrict (Set.Ioc 0 (A.typeData.omega i)))
      (fun v => ENNReal.ofReal (A.typeDensity i v))).ae_le
      (ae_restrict_mem measurableSet_Ioc)

/-- A one-dimensional type drawn from `A.typeMeasure i` is nonnegative almost
surely. -/
theorem ae_typeMeasure_nonneg (A : BayesianSingleItemAuction I) (i : I) :
    ∀ᵐ v ∂A.typeMeasure i, 0 ≤ v := by
  filter_upwards [A.ae_typeMeasure_mem_Ioc i] with v hv
  exact le_of_lt hv.1

/-- Under the product prior, a fixed bidder's type is almost surely different
from any fixed scalar. -/
theorem ae_eval_ne_productPrior [Fintype I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (i : I) (x : ℝ) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.productPrior, t i ≠ x := by
  simpa [productPrior] using
    (Measure.ae_eval_ne (μ := fun j : I => A.typeMeasure j) i x)

/-- Under the opponent product prior, a fixed opponent coordinate is almost
surely different from any fixed scalar. -/
theorem ae_eval_ne_opponentProductPrior [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (i : I) (j : {j // j ≠ i}) (x : ℝ) :
    ∀ᵐ t : OpponentTypeProfile I i ∂A.opponentProductPrior i, t j ≠ x := by
  simpa [opponentProductPrior] using
    (Measure.ae_eval_ne (μ := fun k : {j // j ≠ i} => A.typeMeasure k) j x)

/-- Under the product prior, a fixed bidder's type lies in its support interval
almost surely. -/
theorem ae_eval_mem_Ioc_productPrior [Fintype I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (i : I) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.productPrior, t i ∈ Set.Ioc 0 (A.typeData.omega i) := by
  exact
    (measurePreserving_eval (μ := fun j : I => A.typeMeasure j) i).quasiMeasurePreserving.ae
      (A.ae_typeMeasure_mem_Ioc i)

/-- Under the product prior, a fixed bidder's type is nonnegative almost surely. -/
theorem ae_eval_nonneg_productPrior [Fintype I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (i : I) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.productPrior, 0 ≤ t i := by
  exact
    (measurePreserving_eval (μ := fun j : I => A.typeMeasure j) i).quasiMeasurePreserving.ae
      (A.ae_typeMeasure_nonneg i)

/-- Under independent atomless type priors, a fixed bidder's type is almost
surely different from any fixed scalar. -/
theorem ae_eval_ne_prior_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) (x : ℝ) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, t i ≠ x := by
  rw [h.1]
  exact A.ae_eval_ne_productPrior i x

/-- Under independent type priors, a fixed bidder's type lies in its support
interval almost surely. -/
theorem ae_eval_mem_Ioc_prior_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, t i ∈ Set.Ioc 0 (A.typeData.omega i) := by
  rw [h.1]
  exact A.ae_eval_mem_Ioc_productPrior i

/-- Under independent type priors, a fixed bidder's type is nonnegative almost
surely. -/
theorem ae_eval_nonneg_prior_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, 0 ≤ t i := by
  rw [h.1]
  exact A.ae_eval_nonneg_productPrior i

/-- Under independent atomless type priors, all coordinates are almost surely
different from a fixed scalar. -/
theorem ae_forall_eval_ne_const_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (x : ℝ) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, ∀ i : I, t i ≠ x := by
  exact ae_all_iff.mpr fun i =>
    A.ae_eval_ne_prior_of_hasIndependentTypePriors h i x

/-- Under independent type priors, all coordinates are nonnegative almost
surely. -/
theorem ae_forall_eval_nonneg_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, ∀ i : I, 0 ≤ t i := by
  exact ae_all_iff.mpr fun i =>
    A.ae_eval_nonneg_prior_of_hasIndependentTypePriors h i

/-- Under independent atomless type priors, the selected highest bid is almost
surely not equal to any fixed scalar. -/
theorem ae_argmaxBid_ne_const_prior_of_hasIndependentTypePriors
    [Fintype I] [Nontrivial I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (x : ℝ) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, x ≠ t (Auction.argmaxBid t) := by
  filter_upwards [A.ae_forall_eval_ne_const_prior_of_hasIndependentTypePriors h x] with t ht
  exact (ht (Auction.argmaxBid t)).symm

theorem productPrior_map_eval [Fintype I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) :
    A.productPrior.map (Function.eval i) = A.typeMeasure i := by
  simpa [productPrior] using
    (measurePreserving_eval (μ := fun j : I => A.typeMeasure j) i).map_eq

theorem opponentProductPrior_map_eval [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I)
    (j : {j // j ≠ i}) :
    (A.opponentProductPrior i).map (Function.eval j) = A.typeMeasure j := by
  simpa [opponentProductPrior] using
    (measurePreserving_eval (μ := fun k : {j // j ≠ i} => A.typeMeasure k) j).map_eq

theorem prior_map_eval_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) :
    A.prior.map (Function.eval i) = A.typeMeasure i := by
  rw [h.1]
  exact A.productPrior_map_eval i

theorem opponentPrior_map_eval_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) (j : {j // j ≠ i}) :
    (A.opponentPrior i).map (Function.eval j) = A.typeMeasure j := by
  rw [h.2 i]
  exact A.opponentProductPrior_map_eval i j

theorem integrable_comp_eval_productPrior [Fintype I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] {i : I} {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f (A.typeMeasure i)) :
    Integrable (fun t : ∀ _ : I, ℝ => f (t i)) A.productPrior := by
  simpa [productPrior] using
    (integrable_comp_eval (μ := fun j : I => A.typeMeasure j) (i := i) hf)

theorem integrable_comp_eval_opponentProductPrior [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] {i : I}
    {j : {j // j ≠ i}} {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f (A.typeMeasure j)) :
    Integrable (fun t : OpponentTypeProfile I i => f (t j)) (A.opponentProductPrior i) := by
  simpa [opponentProductPrior] using
    (integrable_comp_eval (μ := fun k : {j // j ≠ i} => A.typeMeasure k) (i := j) hf)

theorem integral_comp_eval_productPrior [Fintype I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] {i : I} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (A.typeMeasure i)) :
    (∫ t : ∀ _ : I, ℝ, f (t i) ∂A.productPrior) =
      ∫ v, f v ∂A.typeMeasure i := by
  simpa [productPrior] using
    (integral_comp_eval (μ := fun j : I => A.typeMeasure j) (i := i) hf)

theorem integral_comp_eval_opponentProductPrior [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] {i : I}
    {j : {j // j ≠ i}} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E}
    (hf : AEStronglyMeasurable f (A.typeMeasure j)) :
    (∫ t : OpponentTypeProfile I i, f (t j) ∂A.opponentProductPrior i) =
      ∫ v, f v ∂A.typeMeasure j := by
  simpa [opponentProductPrior] using
    (integral_comp_eval (μ := fun k : {j // j ≠ i} => A.typeMeasure k) (i := j) hf)

theorem integrable_comp_eval_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i : I} {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f (A.typeMeasure i)) :
    Integrable (fun t : ∀ _ : I, ℝ => f (t i)) A.prior := by
  rw [h.1]
  exact A.integrable_comp_eval_productPrior hf

theorem integrable_comp_eval_opponentPrior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i : I} {j : {j // j ≠ i}} {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f (A.typeMeasure j)) :
    Integrable (fun t : OpponentTypeProfile I i => f (t j)) (A.opponentPrior i) := by
  rw [h.2 i]
  exact A.integrable_comp_eval_opponentProductPrior hf

theorem integral_comp_eval_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i : I} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (A.typeMeasure i)) :
    (∫ t : ∀ _ : I, ℝ, f (t i) ∂A.prior) =
      ∫ v, f v ∂A.typeMeasure i := by
  rw [h.1]
  exact A.integral_comp_eval_productPrior hf

theorem integral_comp_eval_opponentPrior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i : I} {j : {j // j ≠ i}} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (A.typeMeasure j)) :
    (∫ t : OpponentTypeProfile I i, f (t j) ∂A.opponentPrior i) =
      ∫ v, f v ∂A.typeMeasure j := by
  rw [h.2 i]
  exact A.integral_comp_eval_opponentProductPrior hf

/-- Integral against `typeMeasure` as an interval integral. -/
theorem integral_typeMeasure_eq_intervalIntegral_smul
    (A : BayesianSingleItemAuction I) (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v) :
    (∫ v, g v ∂A.typeMeasure i) =
      ∫ v in 0..A.typeData.omega i, A.typeDensity i v • g v := by
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have htop :
      ∀ᵐ v ∂(volume.restrict s),
        ENNReal.ofReal (A.typeDensity i v) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  calc
    (∫ v, g v ∂A.typeMeasure i)
        = ∫ v, (ENNReal.ofReal (A.typeDensity i v)).toReal • g v
            ∂volume.restrict s := by
          simpa [typeMeasure, s] using
            (integral_withDensity_eq_integral_toReal_smul₀
              (μ := volume.restrict s) hmeas htop g)
    _ = ∫ v in s, A.typeDensity i v • g v ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hnonneg] with v hv
          rw [ENNReal.toReal_ofReal hv]
    _ = ∫ v in 0..A.typeData.omega i, A.typeDensity i v • g v := by
          exact (intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg).symm

/-- Real-valued form of `integral_typeMeasure_eq_intervalIntegral_smul`. -/
theorem integral_typeMeasure_eq_intervalIntegral_mul
    (A : BayesianSingleItemAuction I) (i : I) (g : ℝ → ℝ)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v) :
    (∫ v, g v ∂A.typeMeasure i) =
      ∫ v in 0..A.typeData.omega i, g v * A.typeDensity i v := by
  have h :=
    A.integral_typeMeasure_eq_intervalIntegral_smul i g hmeas hnonneg
  calc
    (∫ v, g v ∂A.typeMeasure i)
        = ∫ v in 0..A.typeData.omega i, A.typeDensity i v * g v := by
          simpa [smul_eq_mul] using h
    _ = ∫ v in 0..A.typeData.omega i, g v * A.typeDensity i v := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with v _hv
          ring

section incentive_compatible

/-- The reported type profile obtained by combining `zᵢ` with an opponent
profile `t₋ᵢ`. -/
noncomputable def reportProfile (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    ∀ _ : I, ℝ :=
  profileInsert i z_i t

/-- The inserted coordinate is `zᵢ`. -/
@[simp] theorem reportProfile_self (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    reportProfile i z_i t i = z_i := by
  simp [reportProfile]

/-- Other coordinates come from the opponent profile. -/
@[simp] theorem reportProfile_of_ne
    (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) {j : I} (hji : j ≠ i) :
    reportProfile i z_i t j = t ⟨j, hji⟩ := by
  simp [reportProfile, hji]

/-- Updating coordinate `i` replaces the inserted report. -/
@[simp] theorem update_reportProfile_self
    [DecidableEq I] (i : I) (z_i y_i : ℝ) (t : OpponentTypeProfile I i) :
    Function.update (reportProfile i z_i t) i y_i = reportProfile i y_i t := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

/-- Split a profile into coordinate `i` and its opponents. -/
noncomputable def profileSplitMeasurableEquiv
    (i : I) : (∀ _ : I, ℝ) ≃ᵐ ℝ × OpponentTypeProfile I i where
  toFun t := (t i, fun j => t j)
  invFun p := reportProfile i p.1 p.2
  left_inv := by
    intro t
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [reportProfile, hji]
  right_inv := by
    rintro ⟨v, t⟩
    ext j
    · simp
    · simp [reportProfile, j.property]
  measurable_toFun := (measurable_pi_apply i).prodMk <|
    measurable_pi_iff.2 fun j => measurable_pi_apply j.1
  measurable_invFun := measurable_pi_iff.2 fun j => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simpa [reportProfile, hji] using
        (measurable_pi_apply (⟨j, hji⟩ : {j // j ≠ i})).comp measurable_snd

@[simp] theorem profileSplitMeasurableEquiv_apply_fst
    (i : I) (t : ∀ _ : I, ℝ) :
    (profileSplitMeasurableEquiv i t).1 = t i := rfl

@[simp] theorem profileSplitMeasurableEquiv_apply_snd
    (i : I) (t : ∀ _ : I, ℝ) (j : {j // j ≠ i}) :
    (profileSplitMeasurableEquiv i t).2 j = t j := rfl

@[simp] theorem profileSplitMeasurableEquiv_symm_apply
    (i : I) (v : ℝ) (t : OpponentTypeProfile I i) :
    (profileSplitMeasurableEquiv i).symm (v, t) = reportProfile i v t := rfl

theorem measurePreserving_profileSplitMeasurableEquiv_productPrior
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) :
    MeasurePreserving (profileSplitMeasurableEquiv i) A.productPrior
      ((A.typeMeasure i).prod (A.opponentProductPrior i)) := by
  letI : Subsingleton {j : I // j = i} :=
    ⟨fun a b => Subtype.ext (a.property.trans b.property.symm)⟩
  letI : Unique {j : I // j = i} := uniqueOfSubsingleton ⟨i, rfl⟩
  letI : Fintype {j : I // j = i} := Subtype.fintype fun j : I => j = i
  let e₀ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℝ) (fun j => j = i)
  let e₁ :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.piUnique fun _ : {j : I // j = i} => ℝ)
      (MeasurableEquiv.refl (OpponentTypeProfile I i))
  have h₀ :
      MeasurePreserving e₀ A.productPrior
        ((Measure.pi fun j : {j : I // j = i} => A.typeMeasure j).prod
          (A.opponentProductPrior i)) := by
    simpa [e₀, productPrior, opponentProductPrior] using
      (measurePreserving_piEquivPiSubtypeProd
        (fun j : I => A.typeMeasure j) (fun j : I => j = i))
  have hfirst :
      MeasurePreserving
        (MeasurableEquiv.piUnique fun _ : {j : I // j = i} => ℝ)
        (Measure.pi fun j : {j : I // j = i} => A.typeMeasure j)
        (A.typeMeasure i) := by
    simpa using
      (measurePreserving_piUnique fun j : {j : I // j = i} => A.typeMeasure j)
  have hright :
      MeasurePreserving (MeasurableEquiv.refl (OpponentTypeProfile I i))
        (A.opponentProductPrior i) (A.opponentProductPrior i) := by
    simpa using MeasurePreserving.id (A.opponentProductPrior i)
  have h₁ :
      MeasurePreserving e₁
        ((Measure.pi fun j : {j : I // j = i} => A.typeMeasure j).prod
          (A.opponentProductPrior i))
        ((A.typeMeasure i).prod (A.opponentProductPrior i)) := by
    simpa [e₁, MeasurableEquiv.prodCongr] using hfirst.prod hright
  simpa [profileSplitMeasurableEquiv, e₀, e₁] using h₀.trans h₁

theorem productPrior_map_profileSplitMeasurableEquiv
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) :
    A.productPrior.map (profileSplitMeasurableEquiv i) =
      (A.typeMeasure i).prod (A.opponentProductPrior i) :=
  (A.measurePreserving_profileSplitMeasurableEquiv_productPrior i).map_eq

theorem prior_map_profileSplitMeasurableEquiv_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) :
    A.prior.map (profileSplitMeasurableEquiv i) =
      (A.typeMeasure i).prod (A.opponentProductPrior i) := by
  rw [h.1]
  exact A.productPrior_map_profileSplitMeasurableEquiv i

/-- Under the product prior, two distinct bidder coordinates are almost surely
different. -/
theorem ae_eval_ne_eval_productPrior [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    {i j : I} (hji : j ≠ i) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.productPrior, t i ≠ t j := by
  let j' : {j // j ≠ i} := ⟨j, hji⟩
  let s : Set (ℝ × OpponentTypeProfile I i) := {p | p.1 ≠ p.2 j'}
  have hmeas_j : Measurable (fun t : OpponentTypeProfile I i => t j') :=
    measurable_pi_apply j'
  have hs : MeasurableSet s := by
    dsimp [s]
    exact (measurableSet_eq_fun measurable_fst (hmeas_j.comp measurable_snd)).compl
  have hprod :
      ∀ᵐ p : ℝ × OpponentTypeProfile I i
        ∂(A.typeMeasure i).prod (A.opponentProductPrior i),
        p ∈ s := by
    refine (Measure.ae_prod_iff_ae_ae
      hs).2 ?_
    filter_upwards with v
    filter_upwards [A.ae_eval_ne_opponentProductPrior i j' v] with t ht
    exact ht.symm
  have hmap :
      ∀ᵐ p : ℝ × OpponentTypeProfile I i
        ∂A.productPrior.map (profileSplitMeasurableEquiv i),
        p ∈ s := by
    simpa [A.productPrior_map_profileSplitMeasurableEquiv i] using hprod
  have hpull :
      ∀ᵐ t : (∀ _ : I, ℝ) ∂A.productPrior,
        profileSplitMeasurableEquiv i t ∈ s :=
    (ae_map_iff (profileSplitMeasurableEquiv i).measurable.aemeasurable hs).1 hmap
  simpa [s, j'] using hpull

/-- Under independent atomless type priors, two distinct bidder coordinates are
almost surely different. -/
theorem ae_eval_ne_eval_prior_of_hasIndependentTypePriors [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i j : I} (hji : j ≠ i) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, t i ≠ t j := by
  rw [h.1]
  exact A.ae_eval_ne_eval_productPrior hji

/-- Under independent atomless type priors, every bidder is almost surely
different from every other bidder. -/
theorem ae_pairwise_eval_ne_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior, ∀ i j : I, i ≠ j → t i ≠ t j := by
  refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ hne => False.elim (hne hij)
  · filter_upwards
      [A.ae_eval_ne_eval_prior_of_hasIndependentTypePriors h (fun hji => hij hji.symm)]
      with t ht _hne
    exact ht

/-- Under independent atomless type priors, the selected highest bid is almost
surely unique. -/
theorem ae_unique_argmaxBid_prior_of_hasIndependentTypePriors
    [Fintype I] [Nontrivial I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) :
    ∀ᵐ t : (∀ _ : I, ℝ) ∂A.prior,
      ∀ j, j ≠ Auction.argmaxBid t → t j < t (Auction.argmaxBid t) := by
  filter_upwards [A.ae_pairwise_eval_ne_prior_of_hasIndependentTypePriors h] with t ht
  intro j hj
  exact lt_of_le_of_ne (Auction.bid_le_maxBid t j) (ht j (Auction.argmaxBid t) hj)

theorem integral_comp_profileSplitMeasurableEquiv_productPrior
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ × OpponentTypeProfile I i → E) :
    (∫ t, g (profileSplitMeasurableEquiv i t) ∂A.productPrior) =
      ∫ p, g p ∂(A.typeMeasure i).prod (A.opponentProductPrior i) :=
  (A.measurePreserving_profileSplitMeasurableEquiv_productPrior i).integral_comp' g

theorem integrable_productPrior_of_integrable_profileSplit
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) {E : Type*}
    [NormedAddCommGroup E] {f : (∀ _ : I, ℝ) → E}
    (hf :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2))
        ((A.typeMeasure i).prod (A.opponentProductPrior i))) :
    Integrable f A.productPrior := by
  let e := profileSplitMeasurableEquiv i
  have hmap := A.productPrior_map_profileSplitMeasurableEquiv i
  have hf_map :
      Integrable (fun p : ℝ × OpponentTypeProfile I i => f (e.symm p))
        (A.productPrior.map e) := by
    rw [hmap]
    simpa [e] using hf
  have hcomp :=
    (integrable_map_equiv e (fun p : ℝ × OpponentTypeProfile I i => f (e.symm p))).1
      hf_map
  refine hcomp.congr ?_
  filter_upwards with t
  exact congrArg f (e.left_inv t)

theorem integrable_prior_of_integrable_profileSplit_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) {E : Type*}
    [NormedAddCommGroup E] {f : (∀ _ : I, ℝ) → E}
    (hf :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2))
        ((A.typeMeasure i).prod (A.opponentPrior i))) :
    Integrable f A.prior := by
  rw [h.1]
  apply A.integrable_productPrior_of_integrable_profileSplit i
  rwa [h.2 i] at hf

/-- Fubini decomposition under the product prior. -/
theorem integral_productPrior_eq_integral_typeMeasure_opponentProductPrior
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (∀ _ : I, ℝ) → E)
    (hf :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2))
        ((A.typeMeasure i).prod (A.opponentProductPrior i))) :
    (∫ t, f t ∂A.productPrior) =
      ∫ v, ∫ t, f (reportProfile i v t) ∂A.opponentProductPrior i ∂A.typeMeasure i := by
  have hsplit :
      (∫ t, f t ∂A.productPrior) =
        ∫ p : ℝ × OpponentTypeProfile I i,
          f ((profileSplitMeasurableEquiv i).symm p)
            ∂(A.typeMeasure i).prod (A.opponentProductPrior i) := by
    simpa using
      (A.integral_comp_profileSplitMeasurableEquiv_productPrior i
        (fun p : ℝ × OpponentTypeProfile I i =>
          f ((profileSplitMeasurableEquiv i).symm p)))
  calc
    (∫ t, f t ∂A.productPrior)
        = ∫ p : ℝ × OpponentTypeProfile I i,
            f ((profileSplitMeasurableEquiv i).symm p)
              ∂(A.typeMeasure i).prod (A.opponentProductPrior i) := hsplit
    _ = ∫ p : ℝ × OpponentTypeProfile I i, f (reportProfile i p.1 p.2)
          ∂(A.typeMeasure i).prod (A.opponentProductPrior i) := by
          refine integral_congr_ae ?_
          filter_upwards with p
          rcases p with ⟨v, t⟩
          simp
    _ = ∫ v, ∫ t, f (reportProfile i v t) ∂A.opponentProductPrior i
          ∂A.typeMeasure i := by
          exact integral_prod
            (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2)) hf

theorem integral_prior_eq_integral_typeMeasure_opponentProductPrior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (∀ _ : I, ℝ) → E)
    (hf :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2))
        ((A.typeMeasure i).prod (A.opponentProductPrior i))) :
    (∫ t, f t ∂A.prior) =
      ∫ v, ∫ t, f (reportProfile i v t) ∂A.opponentProductPrior i ∂A.typeMeasure i := by
  rw [h.1]
  exact A.integral_productPrior_eq_integral_typeMeasure_opponentProductPrior i f hf

theorem integral_prior_eq_integral_typeMeasure_opponentPrior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (∀ _ : I, ℝ) → E)
    (hf :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i => f (reportProfile i p.1 p.2))
        ((A.typeMeasure i).prod (A.opponentPrior i))) :
    (∫ t, f t ∂A.prior) =
      ∫ v, ∫ t, f (reportProfile i v t) ∂A.opponentPrior i ∂A.typeMeasure i := by
  rw [h.2 i] at hf ⊢
  exact
    A.integral_prior_eq_integral_typeMeasure_opponentProductPrior_of_hasIndependentTypePriors
      h i f hf

/-- Interim expectation of a full-profile observable after report `zᵢ`. -/
noncomputable def interimExpectation
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ)
    (φ : (∀ _ : I, ℝ) → ℝ) : ℝ :=
  ∫ t, φ (reportProfile i z_i t) ∂A.opponentPrior i

/-- Allocation integrand for interim probability. -/
noncomputable def interimAllocationIntegrand
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    ℝ :=
  A.allocationRule (reportProfile i z_i t) i

/-- Payment integrand for interim payment. -/
noncomputable def interimPaymentIntegrand
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    ℝ :=
  A.paymentRule (reportProfile i z_i t) i

/-- Quasi-linear utility integrand. -/
noncomputable def interimQuasiLinearUtilityIntegrand
    (A : BayesianSingleItemAuction I) (i : I) (t_i z_i : ℝ)
    (t : OpponentTypeProfile I i) : ℝ :=
  t_i * A.interimAllocationIntegrand i z_i t - A.interimPaymentIntegrand i z_i t

/-- Allocation integrands are integrable. -/
def HasIntegrableInterimAllocation (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (z_i : ℝ),
    Integrable (fun t => A.interimAllocationIntegrand i z_i t) (A.opponentPrior i)

/-- Payment integrands are integrable. -/
def HasIntegrableInterimPayment (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (z_i : ℝ),
    Integrable (fun t => A.interimPaymentIntegrand i z_i t) (A.opponentPrior i)

/-- Allocation and payment integrability. -/
def HasIntegrableInterimObjects (A : BayesianSingleItemAuction I) : Prop :=
  A.HasIntegrableInterimAllocation ∧ A.HasIntegrableInterimPayment

/-- Bounded a.e. strongly measurable allocation integrands are integrable. -/
theorem hasIntegrableInterimAllocation_of_aestronglyMeasurable_of_bound
    (A : BayesianSingleItemAuction I)
    (hmeas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i))
    (hbound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimAllocationIntegrand i z_i t‖ ≤ C) :
    A.HasIntegrableInterimAllocation := by
  intro i z_i
  rcases hbound i z_i with ⟨C, hC⟩
  exact Integrable.of_bound (hmeas i z_i) C hC

/-- Bounded a.e. strongly measurable payment integrands are integrable. -/
theorem hasIntegrableInterimPayment_of_aestronglyMeasurable_of_bound
    (A : BayesianSingleItemAuction I)
    (hmeas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimPaymentIntegrand i z_i t)
          (A.opponentPrior i))
    (hbound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimPaymentIntegrand i z_i t‖ ≤ C) :
    A.HasIntegrableInterimPayment := by
  intro i z_i
  rcases hbound i z_i with ⟨C, hC⟩
  exact Integrable.of_bound (hmeas i z_i) C hC

/-- A.e. strong measurability and bounds imply interim integrability. -/
theorem hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound
    (A : BayesianSingleItemAuction I)
    (halloc_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i))
    (hpay_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimPaymentIntegrand i z_i t)
          (A.opponentPrior i))
    (halloc_bound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimAllocationIntegrand i z_i t‖ ≤ C)
    (hpay_bound :
      ∀ i z_i,
        ∃ C : ℝ,
          ∀ᵐ t ∂A.opponentPrior i, ‖A.interimPaymentIntegrand i z_i t‖ ≤ C) :
    A.HasIntegrableInterimObjects :=
  ⟨A.hasIntegrableInterimAllocation_of_aestronglyMeasurable_of_bound
      halloc_meas halloc_bound,
    A.hasIntegrableInterimPayment_of_aestronglyMeasurable_of_bound
      hpay_meas hpay_bound⟩

/-- Feasibility and a.e. strong measurability imply allocation integrability. -/
theorem hasIntegrableInterimAllocation_of_isFeasible_of_aestronglyMeasurable
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible)
    (hmeas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => A.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i)) :
    A.HasIntegrableInterimAllocation := by
  refine A.hasIntegrableInterimAllocation_of_aestronglyMeasurable_of_bound hmeas ?_
  intro i z_i
  refine ⟨1, Filter.Eventually.of_forall ?_⟩
  intro t
  have hx := hfeas.1 (reportProfile i z_i t) i
  simpa [interimAllocationIntegrand, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- Interim allocation probability `q_i(z_i)`. -/
noncomputable def interimAllocProb
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) : ℝ :=
  A.interimExpectation i z_i fun r => A.allocationRule r i

/-- Interim expected payment `m_i(z_i)`. -/
noncomputable def interimExpectedPayment
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) : ℝ :=
  A.interimExpectation i z_i fun r => A.paymentRule r i

/-- The generic interim expectation specializes to the allocation integrand. -/
theorem interimAllocProb_eq_integral_interimAllocationIntegrand
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) :
    A.interimAllocProb i z_i =
      ∫ t, A.interimAllocationIntegrand i z_i t ∂A.opponentPrior i := by
  rfl

/-- The generic interim expectation specializes to the payment integrand. -/
theorem interimExpectedPayment_eq_integral_interimPaymentIntegrand
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) :
    A.interimExpectedPayment i z_i =
      ∫ t, A.interimPaymentIntegrand i z_i t ∂A.opponentPrior i := by
  rfl

/-- Product-side integrability gives interval integrability of `m_i f_i`. -/
theorem intervalIntegrable_interimExpectedPayment_mul_typeDensity_of_profileSplit_integrable
    {A B : BayesianSingleItemAuction I} (i : I)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v)
    (hpay :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i))) :
    IntervalIntegrable
      (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have hinner :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.paymentRule (reportProfile i v t) i ∂B.opponentPrior i)
        (A.typeMeasure i) := by
    simpa using hpay.integral_prod_left
  have htop :
      ∀ᵐ v ∂(volume.restrict s),
        ENNReal.ofReal (A.typeDensity i v) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hinner' :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.paymentRule (reportProfile i v t) i ∂B.opponentPrior i)
        ((volume.restrict s).withDensity fun v => ENNReal.ofReal (A.typeDensity i v)) := by
    simpa [typeMeasure, s] using hinner
  have hsmul :
      Integrable
        (fun v : ℝ =>
          (ENNReal.ofReal (A.typeDensity i v)).toReal •
            (∫ t, B.paymentRule (reportProfile i v t) i ∂B.opponentPrior i))
        (volume.restrict s) :=
    (integrable_withDensity_iff_integrable_smul₀' hmeas htop).mp hinner'
  have hmul :
      Integrable
        (fun v : ℝ =>
          (∫ t, B.paymentRule (reportProfile i v t) i ∂B.opponentPrior i) *
            A.typeDensity i v)
        (volume.restrict s) := by
    refine hsmul.congr ?_
    filter_upwards [hnonneg] with v hv
    rw [ENNReal.toReal_ofReal hv]
    simp [smul_eq_mul, mul_comm]
  have hint :
      Integrable
        (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
        (volume.restrict s) := by
    simpa [interimExpectedPayment, interimPaymentIntegrand, s] using hmul
  rw [intervalIntegrable_iff, Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg]
  simpa [IntegrableOn, s] using hint

/-- Feasible auctions have nonnegative interim allocation probabilities. -/
theorem interimAllocProb_nonneg_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) (i : I) (z_i : ℝ) :
    0 ≤ A.interimAllocProb i z_i := by
  exact integral_nonneg fun t => (hfeas.1 (reportProfile i z_i t) i).1

/-- Feasible auctions have interim allocation probabilities at most `1`. -/
theorem interimAllocProb_le_one_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) (hint : A.HasIntegrableInterimAllocation)
    (i : I) (z_i : ℝ) :
    A.interimAllocProb i z_i ≤ 1 := by
  have hle :
      A.interimAllocProb i z_i ≤
        ∫ _ : OpponentTypeProfile I i, (1 : ℝ) ∂A.opponentPrior i := by
    exact integral_mono (hint i z_i) (integrable_const (1 : ℝ)) fun t =>
      (hfeas.1 (reportProfile i z_i t) i).2
  simpa using hle

/-- Feasible interim allocation probabilities lie in `[0, 1]`. -/
theorem interimAllocProb_mem_Icc_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) (hint : A.HasIntegrableInterimAllocation)
    (i : I) (z_i : ℝ) :
    A.interimAllocProb i z_i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨A.interimAllocProb_nonneg_of_isFeasible hfeas i z_i,
    A.interimAllocProb_le_one_of_isFeasible hfeas hint i z_i⟩

/-! ## Payment revenue through interim payments -/

/-- Expected total payment revenue under the base prior. -/
noncomputable def expectedPaymentRevenueInEnvironment [Fintype I]
    (A : BayesianSingleItemAuction I) (p : (I → ℝ) → I → ℝ) : ℝ :=
  ∫ t, (∑ i, p t i) ∂A.prior

/-- Expected seller revenue of `B`, evaluated in environment `A`. -/
noncomputable def expectedSellerRevenueInEnvironment [Fintype I]
    (A B : BayesianSingleItemAuction I) : ℝ :=
  A.expectedPaymentRevenueInEnvironment B.paymentRule

/-- Expected total payment revenue is unchanged by an almost-everywhere equal
payment profile. -/
theorem expectedPaymentRevenueInEnvironment_congr_ae [Fintype I]
    (A : BayesianSingleItemAuction I)
    {p q : (I → ℝ) → I → ℝ}
    (h : p =ᵐ[A.prior] q) :
    A.expectedPaymentRevenueInEnvironment p =
      A.expectedPaymentRevenueInEnvironment q := by
  dsimp [expectedPaymentRevenueInEnvironment]
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

/-- Pointwise bidder-wise almost-everywhere equality is enough for equality of
expected total payment revenue. -/
theorem expectedPaymentRevenueInEnvironment_congr_ae_pointwise [Fintype I]
    (A : BayesianSingleItemAuction I)
    {p q : (I → ℝ) → I → ℝ}
    (h : ∀ i : I, (fun t => p t i) =ᵐ[A.prior] fun t => q t i) :
    A.expectedPaymentRevenueInEnvironment p =
      A.expectedPaymentRevenueInEnvironment q := by
  dsimp [expectedPaymentRevenueInEnvironment]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.mpr h] with t ht
  exact Finset.sum_congr rfl fun i _hi => ht i

/-- Expected seller revenue is unchanged when the evaluated auction's payment
rule is almost everywhere equal. -/
theorem expectedSellerRevenueInEnvironment_congr_paymentRule_ae [Fintype I]
    (A B C : BayesianSingleItemAuction I)
    (h : B.paymentRule =ᵐ[A.prior] C.paymentRule) :
    A.expectedSellerRevenueInEnvironment B =
      A.expectedSellerRevenueInEnvironment C := by
  simpa [expectedSellerRevenueInEnvironment] using
    (A.expectedPaymentRevenueInEnvironment_congr_ae
      (p := B.paymentRule) (q := C.paymentRule) h)

/-- Bidder-wise almost-everywhere equality of payment rules is enough for
equality of expected seller revenue. -/
theorem expectedSellerRevenueInEnvironment_congr_paymentRule_ae_pointwise [Fintype I]
    (A B C : BayesianSingleItemAuction I)
    (h : ∀ i : I, (fun t => B.paymentRule t i) =ᵐ[A.prior] fun t => C.paymentRule t i) :
    A.expectedSellerRevenueInEnvironment B =
      A.expectedSellerRevenueInEnvironment C := by
  simpa [expectedSellerRevenueInEnvironment] using
    (A.expectedPaymentRevenueInEnvironment_congr_ae_pointwise
      (p := B.paymentRule) (q := C.paymentRule) h)

/-- Ex-ante revenue through interim expected payments. -/
noncomputable def expectedInterimPaymentRevenue [Fintype I]
    (A B : BayesianSingleItemAuction I) : ℝ :=
  ∑ i, ∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v

/-- Evaluating an auction's seller revenue in its own environment is its
ordinary expected seller revenue. -/
@[simp] theorem expectedSellerRevenueInEnvironment_self [Fintype I]
    (A : BayesianSingleItemAuction I) :
    A.expectedSellerRevenueInEnvironment A = A.expectedSellerRevenue := by
  rfl

/-- Ex-ante revenue agrees with the interim-payment expression. -/
def HasExpectedRevenueInterimPaymentIdentity [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.expectedSellerRevenueInEnvironment B =
    A.expectedInterimPaymentRevenue B

/-- Payment-side Fubini hypotheses connecting ex-ante and interim expressions. -/
structure PaymentInterimFubiniAssumptions [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop where
  payment_integrable :
    ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior
  payment_interim_fubini :
    ∀ i : I,
      (∫ t, B.paymentRule t i ∂A.prior) =
        ∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v

theorem PaymentInterimFubiniAssumptions.expectedPaymentRevenueIntegrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.PaymentInterimFubiniAssumptions B) :
    Integrable (fun t => ∑ i, B.paymentRule t i) A.prior :=
  integrable_finsetSum Finset.univ fun i _ => h.payment_integrable i

theorem PaymentInterimFubiniAssumptions.hasExpectedRevenueInterimPaymentIdentity
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.PaymentInterimFubiniAssumptions B) :
    A.HasExpectedRevenueInterimPaymentIdentity B := by
  dsimp [
    HasExpectedRevenueInterimPaymentIdentity,
    expectedSellerRevenueInEnvironment,
    expectedPaymentRevenueInEnvironment,
    expectedInterimPaymentRevenue]
  calc
    (∫ t, ∑ i, B.paymentRule t i ∂A.prior)
        = ∑ i, ∫ t, B.paymentRule t i ∂A.prior := by
          simpa using
            (integral_finsetSum (s := Finset.univ)
              (f := fun i t => B.paymentRule t i)
              (fun i _ => h.payment_integrable i))
    _ = ∑ i, ∫ v in 0..A.typeData.omega i,
          B.interimExpectedPayment i v * A.typeDensity i v := by
          exact Finset.sum_congr rfl fun i _ => h.payment_interim_fubini i

/-- Build payment-side interim Fubini hypotheses from type-measure Fubini. -/
theorem paymentInterimFubiniAssumptions_of_typeMeasure_fubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hdens_meas :
      ∀ i : I,
        AEMeasurable
          (fun v => ENNReal.ofReal (A.typeDensity i v))
          (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hpay_int : ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior)
    (hpay_fubini :
      ∀ i : I,
        (∫ t, B.paymentRule t i ∂A.prior) =
          ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i) :
    A.PaymentInterimFubiniAssumptions B where
  payment_integrable := hpay_int
  payment_interim_fubini := by
    intro i
    calc
      (∫ t, B.paymentRule t i ∂A.prior)
          = ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i :=
            hpay_fubini i
      _ = ∫ v in 0..A.typeData.omega i,
            B.interimExpectedPayment i v * A.typeDensity i v := by
            exact A.integral_typeMeasure_eq_intervalIntegral_mul i
              (B.interimExpectedPayment i)
              (hdens_meas i)
              (hdens_ae i)

/-- Independent priors and product-side payment integrability imply the
payment-side interim Fubini package. -/
theorem paymentInterimFubiniAssumptions_of_independentTypePriors
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hdens_meas :
      ∀ i : I,
        AEMeasurable
          (fun v => ENNReal.ofReal (A.typeDensity i v))
          (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B)
    (hpay_prod_int :
      ∀ i : I,
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod (B.opponentPrior i))) :
    A.PaymentInterimFubiniAssumptions B := by
  refine A.paymentInterimFubiniAssumptions_of_typeMeasure_fubini
    hdens_meas hdens_ae ?_ ?_
  · intro i
    apply A.integrable_prior_of_integrable_profileSplit_of_hasIndependentTypePriors hind i
    have hprod := hpay_prod_int i
    rwa [henv.opponentPrior_eq] at hprod
  · intro i
    have hprod :
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod (A.opponentPrior i)) := by
      have h := hpay_prod_int i
      rwa [henv.opponentPrior_eq] at h
    have hfubini :=
      A.integral_prior_eq_integral_typeMeasure_opponentPrior_of_hasIndependentTypePriors
        hind i (fun t => B.paymentRule t i) hprod
    calc
      (∫ t, B.paymentRule t i ∂A.prior)
          = ∫ v, ∫ t, B.paymentRule (reportProfile i v t) i
              ∂A.opponentPrior i ∂A.typeMeasure i := hfubini
      _ = ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i := by
            refine integral_congr_ae ?_
            filter_upwards with v
            simp [interimExpectedPayment, interimExpectation, henv.opponentPrior_eq]

/-- Supportwise interval integrability of `q_i`. -/
def HasIntervalIntegrableInterimAllocationOnSupport
    (A : BayesianSingleItemAuction I) : Prop :=
  ∀ i : I,
    IntervalIntegrable (A.interimAllocProb i) volume 0 (A.typeData.omega i)

/-- Global interval integrability of `q_i`. -/
def HasIntervalIntegrableInterimAllocation
    (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (a b : ℝ),
    IntervalIntegrable (A.interimAllocProb i) volume a b

/-- Interim utility `q_i(z_i) * t_i - m_i(z_i)`. -/
noncomputable def interimQuasiLinearUtility
    (A : BayesianSingleItemAuction I) (i : I) (t_i z_i : ℝ) : ℝ :=
  A.interimAllocProb i z_i * t_i - A.interimExpectedPayment i z_i

/-- Truthful interim payoff `U_i(t_i)`. -/
noncomputable def equilibriumPayoff
    (A : BayesianSingleItemAuction I) (i : I) (t_i : ℝ) : ℝ :=
  A.interimQuasiLinearUtility i t_i t_i

/-- Interim incentive compatibility. -/
def IsIncentiveCompatible
    (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (t_i z_i : ℝ),
    A.interimQuasiLinearUtility i t_i z_i ≤ A.equilibriumPayoff i t_i

/-- Misreport utility in terms of truthful payoff at the report. -/
theorem interimQuasiLinearUtility_eq_equilibriumPayoff_add
    (A : BayesianSingleItemAuction I) (i : I) (t_i z_i : ℝ) :
    A.interimQuasiLinearUtility i t_i z_i =
      A.equilibriumPayoff i z_i + A.interimAllocProb i z_i * (t_i - z_i) := by
  rw [equilibriumPayoff, interimQuasiLinearUtility, interimQuasiLinearUtility]
  ring

/-- Utility integrability from allocation and payment integrability. -/
theorem integrable_interimQuasiLinearUtilityIntegrand
    (A : BayesianSingleItemAuction I)
    (hQ : A.HasIntegrableInterimAllocation) (hM : A.HasIntegrableInterimPayment)
    (i : I) (t_i z_i : ℝ) :
    Integrable (fun t => A.interimQuasiLinearUtilityIntegrand i t_i z_i t)
      (A.opponentPrior i) := by
  exact ((hQ i z_i).const_mul t_i).sub (hM i z_i)

/-- The utility integrand integrates to interim utility. -/
theorem integral_interimQuasiLinearUtilityIntegrand_eq
    (A : BayesianSingleItemAuction I)
    (hQ : A.HasIntegrableInterimAllocation) (hM : A.HasIntegrableInterimPayment)
    (i : I) (t_i z_i : ℝ) :
    (∫ t, A.interimQuasiLinearUtilityIntegrand i t_i z_i t ∂A.opponentPrior i) =
      A.interimQuasiLinearUtility i t_i z_i := by
  calc
    (∫ t, A.interimQuasiLinearUtilityIntegrand i t_i z_i t ∂A.opponentPrior i)
        = (∫ t, t_i * A.interimAllocationIntegrand i z_i t -
            A.interimPaymentIntegrand i z_i t ∂A.opponentPrior i) := by
          rfl
    _ = (∫ t, t_i * A.interimAllocationIntegrand i z_i t ∂A.opponentPrior i) -
          ∫ t, A.interimPaymentIntegrand i z_i t ∂A.opponentPrior i := by
          exact integral_sub ((hQ i z_i).const_mul t_i) (hM i z_i)
    _ = t_i * A.interimAllocProb i z_i - A.interimExpectedPayment i z_i := by
          rw [integral_const_mul]
          rfl
    _ = A.interimQuasiLinearUtility i t_i z_i := by
          rw [interimQuasiLinearUtility]
          ring

/-- Pointwise DSIC inequality for the interim utility integrand. -/
theorem interimQuasiLinearUtilityIntegrand_le_of_isDSIC
    [DecidableEq I] (A : BayesianSingleItemAuction I) (hdsic : A.IsDSIC)
    (i : I) (t_i z_i : ℝ) (t : OpponentTypeProfile I i) :
    A.interimQuasiLinearUtilityIntegrand i t_i z_i t ≤
      A.interimQuasiLinearUtilityIntegrand i t_i t_i t := by
  have h :=
    hdsic (reportProfile i t_i t) i z_i (reportProfile i t_i t)
  simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
    MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
    StrategicGame.deviate, interimQuasiLinearUtilityIntegrand,
    interimAllocationIntegrand, interimPaymentIntegrand] using h

/-- DSIC implies interim IC under interim integrability. -/
theorem isIncentiveCompatible_of_isDSIC
    [DecidableEq I] (A : BayesianSingleItemAuction I)
    (hint : A.HasIntegrableInterimObjects) (hdsic : A.IsDSIC) :
    A.IsIncentiveCompatible := by
  intro i t_i z_i
  rcases hint with ⟨hQ, hM⟩
  have hz := A.integral_interimQuasiLinearUtilityIntegrand_eq hQ hM i t_i z_i
  have ht := A.integral_interimQuasiLinearUtilityIntegrand_eq hQ hM i t_i t_i
  rw [equilibriumPayoff, ← hz, ← ht]
  exact integral_mono
    (A.integrable_interimQuasiLinearUtilityIntegrand hQ hM i t_i z_i)
    (A.integrable_interimQuasiLinearUtilityIntegrand hQ hM i t_i t_i)
    (fun t => A.interimQuasiLinearUtilityIntegrand_le_of_isDSIC hdsic i t_i z_i t)

/-- [MSZ 12.48] IC iff the one-dimensional payoff inequality. -/
theorem isIncentiveCompatible_iff_equilibriumPayoff_ge
    (A : BayesianSingleItemAuction I) :
    A.IsIncentiveCompatible ↔
      ∀ (i : I) (v_i x_i : ℝ),
        A.equilibriumPayoff i v_i ≥
          A.equilibriumPayoff i x_i + A.interimAllocProb i x_i * (v_i - x_i) := by
  constructor
  · intro hIC i v_i x_i
    simpa [interimQuasiLinearUtility_eq_equilibriumPayoff_add] using hIC i v_i x_i
  · intro hineq i t_i z_i
    simpa [interimQuasiLinearUtility_eq_equilibriumPayoff_add] using hineq i t_i z_i

/-- IC implies monotonicity of `q_i`. -/
theorem interimAllocProb_mono_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible) (i : I) :
    Monotone (A.interimAllocProb i) := by
  rw [Monotone]
  intro x y hxy
  by_cases hlt : x < y
  · have hineq := (A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC)
    have h1 :
        A.equilibriumPayoff i x + A.interimAllocProb i x * (y - x) ≤
          A.equilibriumPayoff i y := by
      exact hineq i y x
    have h2 :
        A.equilibriumPayoff i y + A.interimAllocProb i y * (x - y) ≤
          A.equilibriumPayoff i x := by
      exact hineq i x y
    have hprod :
        (A.interimAllocProb i x - A.interimAllocProb i y) * (y - x) ≤ 0 := by
      nlinarith
    have hpos : 0 < y - x := sub_pos.mpr hlt
    nlinarith
  · have hEq : x = y := le_antisymm hxy (le_of_not_gt hlt)
    simp [hEq]

/-- IC gives global interval integrability of `q_i`. -/
theorem hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible) :
    A.HasIntervalIntegrableInterimAllocation := by
  intro i a b
  exact (A.interimAllocProb_mono_of_isIncentiveCompatible hIC i).intervalIntegrable

/-- IC makes truthful payoff convex. -/
theorem equilibriumPayoff_convexOn_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible) (i : I) :
    ConvexOn ℝ Set.univ (A.equilibriumPayoff i) := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simp only [smul_eq_mul]
    let m := a * x + b * y
    let Wm := A.equilibriumPayoff i m
    let Qm := A.interimAllocProb i m
    change Wm ≤ a * A.equilibriumPayoff i x + b * A.equilibriumPayoff i y
    have hineq := A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC
    have hxineq :
        Wm + Qm * (x - m) ≤
          A.equilibriumPayoff i x := by
      simpa [Wm, Qm, m] using hineq i x m
    have hyineq :
        Wm + Qm * (y - m) ≤
          A.equilibriumPayoff i y := by
      simpa [Wm, Qm, m] using hineq i y m
    have hxscaled := mul_le_mul_of_nonneg_left hxineq ha
    have hyscaled := mul_le_mul_of_nonneg_left hyineq hb
    have hsum := add_le_add hxscaled hyscaled
    have hcombo : a * (x - m) + b * (y - m) = 0 := by
      have hm : a * x + b * y = m := rfl
      calc
        a * (x - m) + b * (y - m) = (a * x + b * y) - (a + b) * m := by
          ring
        _ = m - 1 * m := by rw [hm, hab]
        _ = 0 := by ring
    have hleft : a * (Wm + Qm * (x - m)) + b * (Wm + Qm * (y - m)) = Wm := by
      calc
        a * (Wm + Qm * (x - m)) + b * (Wm + Qm * (y - m))
            = (a + b) * Wm + Qm * (a * (x - m) + b * (y - m)) := by
              ring
        _ = Wm := by
              rw [hab, hcombo]
              ring
    nlinarith

/-- At differentiable types, `U_i' = q_i`. -/
theorem deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible)
    {i : I} {v_i : ℝ}
    (hdiff : DifferentiableAt ℝ (A.equilibriumPayoff i) v_i) :
    deriv (A.equilibriumPayoff i) v_i = A.interimAllocProb i v_i := by
  let q := A.interimAllocProb i v_i
  have hineq := A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC
  have hmin :
      IsMinOn (fun x : ℝ => A.equilibriumPayoff i x - q * x) Set.univ v_i := by
    rw [isMinOn_univ_iff]
    intro x
    have hxineq : A.equilibriumPayoff i x ≥ A.equilibriumPayoff i v_i + q * (x - v_i) := by
      simpa [q] using hineq i x v_i
    nlinarith
  have hlocal : IsLocalMin (fun x : ℝ => A.equilibriumPayoff i x - q * x) v_i :=
    hmin.isLocalMin (by simp)
  have hderiv :
      HasDerivAt (fun x : ℝ => A.equilibriumPayoff i x - q * x)
        (deriv (A.equilibriumPayoff i) v_i - q) v_i := by
    exact hdiff.hasDerivAt.sub (hasDerivAt_const_mul (x := v_i) q)
  have hzero : deriv (A.equilibriumPayoff i) v_i - q = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  simpa [q] using sub_eq_zero.mp hzero

/-- Interim individual rationality. -/
def IsIndividuallyRational (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (t_i : ℝ), 0 ≤ A.equilibriumPayoff i t_i

/-- Interim individual rationality on `[0, ωᵢ]`. -/
def IsIndividuallyRationalOnSupport (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (t_i : ℝ),
    0 ≤ t_i → t_i ≤ A.typeData.omega i → 0 ≤ A.equilibriumPayoff i t_i

/-- [MSZ 12.49] Payoff envelope. -/
def HasInterimEnvelopeFormula (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (v_i : ℝ),
    A.equilibriumPayoff i v_i =
      A.equilibriumPayoff i 0 + ∫ z in 0..v_i, A.interimAllocProb i z

/-- [MSZ 12.49] Payment identity. -/
def HasInterimPaymentFormula (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (v_i : ℝ),
    A.interimExpectedPayment i v_i =
      A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
        ∫ z in 0..v_i, A.interimAllocProb i z

/-- Envelope derivative condition. -/
def HasInterimEnvelopeDerivative (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (v_i : ℝ),
    HasDerivAt (A.equilibriumPayoff i) (A.interimAllocProb i v_i) v_i

/-- IC and differentiability give the envelope derivative. -/
theorem hasInterimEnvelopeDerivative_of_isIncentiveCompatible_of_equilibriumPayoff_differentiable
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible)
    (hdiff : ∀ (i : I) (v_i : ℝ), DifferentiableAt ℝ (A.equilibriumPayoff i) v_i) :
    A.HasInterimEnvelopeDerivative := by
  intro i v_i
  have hderiv := (hdiff i v_i).hasDerivAt
  have hderiv_eq :
      deriv (A.equilibriumPayoff i) v_i = A.interimAllocProb i v_i :=
    A.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible
      hIC (hdiff i v_i)
  simpa [hderiv_eq] using hderiv

/-- The envelope derivative gives the payoff envelope. -/
theorem hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative
    (A : BayesianSingleItemAuction I)
    (hderiv : A.HasInterimEnvelopeDerivative)
    (hint : A.HasIntervalIntegrableInterimAllocation) :
    A.HasInterimEnvelopeFormula := by
  intro i v_i
  have hFTC :
      ∫ z in 0..v_i, A.interimAllocProb i z =
        A.equilibriumPayoff i v_i - A.equilibriumPayoff i 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := A.equilibriumPayoff i)
      (f' := A.interimAllocProb i)
      (a := 0) (b := v_i)
      (fun x _hx => hderiv i x)
      (hint i 0 v_i)
  rw [hFTC]
  ring

/-- IC plus the envelope derivative gives the payoff envelope. -/
theorem hasInterimEnvelopeFormula_of_isIncentiveCompatible_of_hasInterimEnvelopeDerivative
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible)
    (hderiv : A.HasInterimEnvelopeDerivative) :
    A.HasInterimEnvelopeFormula :=
  A.hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative hderiv
    (A.hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible hIC)

/-- [MSZ 12.49] Payoff envelope from IC. -/
theorem hasInterimEnvelopeFormula_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible) :
    A.HasInterimEnvelopeFormula := by
  intro i v_i
  let W : ℝ → ℝ := A.equilibriumPayoff i
  let Q : ℝ → ℝ := A.interimAllocProb i
  change W v_i = W 0 + ∫ z in 0..v_i, Q z
  have hconv : ConvexOn ℝ Set.univ W := by
    simpa [W] using A.equilibriumPayoff_convexOn_of_isIncentiveCompatible hIC i
  have hll : LocallyLipschitz W :=
    hconv.locallyLipschitz
  have hll_on : LocallyLipschitzOn (Set.uIcc 0 v_i) W :=
    hll.locallyLipschitzOn
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_uIcc hll_on
  have hAC : AbsolutelyContinuousOnInterval W 0 v_i :=
    hK.absolutelyContinuousOnInterval
  have hFTC :
      ∫ z in 0..v_i, deriv W z = W v_i - W 0 :=
    hAC.integral_deriv_eq_sub
  have hae_deriv_eq :
      ∀ᵐ z ∂volume, z ∈ Set.uIoc 0 v_i → deriv W z = Q z := by
    filter_upwards [hAC.ae_differentiableAt] with z hdiff hz
    have hdiff_z : DifferentiableAt ℝ W z := hdiff (Set.uIoc_subset_uIcc hz)
    simpa [W, Q] using
      A.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible hIC
        (i := i) (v_i := z) hdiff_z
  have hcongr :
      ∫ z in 0..v_i, deriv W z = ∫ z in 0..v_i, Q z :=
    intervalIntegral.integral_congr_ae hae_deriv_eq
  calc
    W v_i = W 0 + ∫ z in 0..v_i, deriv W z := by
      linarith
    _ = W 0 + ∫ z in 0..v_i, Q z := by
      rw [hcongr]

/-- [MSZ 12.146] Payoff identity. -/
theorem equilibriumPayoff_eq_neg_interimExpectedPayment_zero_add_integral
    (A : BayesianSingleItemAuction I)
    (henv : A.HasInterimEnvelopeFormula) (i : I) (v_i : ℝ) :
    A.equilibriumPayoff i v_i =
      -A.interimExpectedPayment i 0 + ∫ z in 0..v_i, A.interimAllocProb i z := by
  have hW0 : A.equilibriumPayoff i 0 = -A.interimExpectedPayment i 0 := by
    rw [equilibriumPayoff, interimQuasiLinearUtility]
    ring
  rw [henv i v_i, hW0]

/-- The payoff envelope implies the payment identity. -/
theorem hasInterimPaymentFormula_of_hasInterimEnvelopeFormula
    (A : BayesianSingleItemAuction I) (henv : A.HasInterimEnvelopeFormula) :
    A.HasInterimPaymentFormula := by
  intro i v_i
  calc
    A.interimExpectedPayment i v_i
        = A.interimAllocProb i v_i * v_i - A.equilibriumPayoff i v_i := by
          rw [equilibriumPayoff, interimQuasiLinearUtility]
          ring
    _ = A.interimAllocProb i v_i * v_i -
          (A.equilibriumPayoff i 0 + ∫ z in 0..v_i, A.interimAllocProb i z) := by
          rw [henv i v_i]
    _ = A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := by
          rw [equilibriumPayoff, interimQuasiLinearUtility]
          ring

/-- The envelope derivative implies the payment identity. -/
theorem hasInterimPaymentFormula_of_hasInterimEnvelopeDerivative
    (A : BayesianSingleItemAuction I)
    (hderiv : A.HasInterimEnvelopeDerivative)
    (hint : A.HasIntervalIntegrableInterimAllocation) :
    A.HasInterimPaymentFormula :=
  A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula
    (A.hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative hderiv hint)

/-- [MSZ 12.147] Payment identity from IC. -/
theorem hasInterimPaymentFormula_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible) :
    A.HasInterimPaymentFormula :=
  A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula
    (A.hasInterimEnvelopeFormula_of_isIncentiveCompatible hIC)

/-- Envelope and payment identities from IC and the derivative condition. -/
theorem interimEnvelopeFormula_and_paymentFormula_of_isIncentiveCompatible_of_hasInterimEnvelopeDerivative
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible)
    (hderiv : A.HasInterimEnvelopeDerivative) :
    A.HasInterimEnvelopeFormula ∧ A.HasInterimPaymentFormula := by
  have henv :
      A.HasInterimEnvelopeFormula :=
      A.hasInterimEnvelopeFormula_of_isIncentiveCompatible_of_hasInterimEnvelopeDerivative
      hIC hderiv
  exact ⟨henv, A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henv⟩

/-- [MSZ 12.49] Envelope and payment identities from IC. -/
theorem interimEnvelopeFormula_and_paymentFormula_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible) :
    A.HasInterimEnvelopeFormula ∧ A.HasInterimPaymentFormula := by
  have henv : A.HasInterimEnvelopeFormula :=
    A.hasInterimEnvelopeFormula_of_isIncentiveCompatible hIC
  exact ⟨henv, A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henv⟩

/-- Same `q_i` and zero-type payment give the same truthful payoff. -/
theorem equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq
    (A B : BayesianSingleItemAuction I)
    (henvA : A.HasInterimEnvelopeFormula) (henvB : B.HasInterimEnvelopeFormula)
    (i : I)
    (hQ : ∀ z : ℝ, A.interimAllocProb i z = B.interimAllocProb i z)
    (hM0 : A.interimExpectedPayment i 0 = B.interimExpectedPayment i 0)
    (v_i : ℝ) :
    A.equilibriumPayoff i v_i = B.equilibriumPayoff i v_i := by
  have hW0 : A.equilibriumPayoff i 0 = B.equilibriumPayoff i 0 := by
    rw [equilibriumPayoff, interimQuasiLinearUtility,
      equilibriumPayoff, interimQuasiLinearUtility, hM0]
    ring
  have hQfun : (fun z => A.interimAllocProb i z) = fun z => B.interimAllocProb i z :=
    funext hQ
  calc
    A.equilibriumPayoff i v_i
        = A.equilibriumPayoff i 0 + ∫ z in 0..v_i, A.interimAllocProb i z :=
          henvA i v_i
    _ = B.equilibriumPayoff i 0 + ∫ z in 0..v_i, B.interimAllocProb i z := by
          rw [hW0, hQfun]
    _ = B.equilibriumPayoff i v_i := (henvB i v_i).symm

/-- Same `q_i` and zero-type payment give the same interim payment. -/
theorem interimExpectedPayment_eq_of_hasInterimPaymentFormula_of_interimAllocProb_eq
    (A B : BayesianSingleItemAuction I)
    (hpayA : A.HasInterimPaymentFormula) (hpayB : B.HasInterimPaymentFormula)
    (i : I)
    (hQ : ∀ z : ℝ, A.interimAllocProb i z = B.interimAllocProb i z)
    (hM0 : A.interimExpectedPayment i 0 = B.interimExpectedPayment i 0)
    (v_i : ℝ) :
    A.interimExpectedPayment i v_i = B.interimExpectedPayment i v_i := by
  have hQv : A.interimAllocProb i v_i = B.interimAllocProb i v_i := hQ v_i
  have hQfun : (fun z => A.interimAllocProb i z) = fun z => B.interimAllocProb i z :=
    funext hQ
  calc
    A.interimExpectedPayment i v_i
        = A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := hpayA i v_i
    _ = B.interimExpectedPayment i 0 + B.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, B.interimAllocProb i z := by
          rw [hM0, hQv, hQfun]
    _ = B.interimExpectedPayment i v_i := (hpayB i v_i).symm

/-- [MSZ 12.50] Same `q_i` and zero-type payment give the same interim objects. -/
theorem interimExpectedPayment_eq_and_equilibriumPayoff_eq_of_hasInterimEnvelopeFormula
    (A B : BayesianSingleItemAuction I)
    (henvA : A.HasInterimEnvelopeFormula) (henvB : B.HasInterimEnvelopeFormula)
    (i : I)
    (hQ : ∀ z : ℝ, A.interimAllocProb i z = B.interimAllocProb i z)
    (hM0 : A.interimExpectedPayment i 0 = B.interimExpectedPayment i 0)
    (v_i : ℝ) :
    A.interimExpectedPayment i v_i = B.interimExpectedPayment i v_i ∧
      A.equilibriumPayoff i v_i = B.equilibriumPayoff i v_i := by
  constructor
  · exact
      A.interimExpectedPayment_eq_of_hasInterimPaymentFormula_of_interimAllocProb_eq B
        (A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henvA)
        (B.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henvB)
        i hQ hM0 v_i
  · exact
      A.equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq B
        henvA henvB i hQ hM0 v_i

/-- Nonnegative envelope increments on `[0, ωᵢ]`. -/
def HasNonnegativeInterimAllocationIntegralOnSupport
    (A : BayesianSingleItemAuction I) : Prop :=
  ∀ (i : I) (v_i : ℝ),
    0 ≤ v_i → v_i ≤ A.typeData.omega i →
      0 ≤ ∫ z in 0..v_i, A.interimAllocProb i z

/-- Feasibility gives nonnegative envelope increments on the support. -/
theorem hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hfeas : A.IsFeasible) :
    A.HasNonnegativeInterimAllocationIntegralOnSupport := by
  intro i v_i hv_nonneg _hv_le
  exact intervalIntegral.integral_nonneg hv_nonneg fun z _hz =>
    A.interimAllocProb_nonneg_of_isFeasible hfeas i z

/-- [MSZ 12.52] Supportwise IR iff zero-type payment is nonpositive. -/
theorem isIndividuallyRationalOnSupport_iff_interimExpectedPayment_zero_nonpos
    (A : BayesianSingleItemAuction I)
    (henv : A.HasInterimEnvelopeFormula)
    (hint_nonneg : A.HasNonnegativeInterimAllocationIntegralOnSupport) :
    A.IsIndividuallyRationalOnSupport ↔
      ∀ i : I, A.interimExpectedPayment i 0 ≤ 0 := by
  constructor
  · intro hIR i
    have hW0 : 0 ≤ A.equilibriumPayoff i 0 :=
      hIR i 0 le_rfl (A.typeData.cdf i).omega_nonneg
    rw [equilibriumPayoff, interimQuasiLinearUtility] at hW0
    linarith
  · intro hM0 i v_i hv_nonneg hv_le
    have hW0 : 0 ≤ A.equilibriumPayoff i 0 := by
      rw [equilibriumPayoff, interimQuasiLinearUtility]
      have hM := hM0 i
      linarith
    have hint : 0 ≤ ∫ z in 0..v_i, A.interimAllocProb i z :=
      hint_nonneg i v_i hv_nonneg hv_le
    have hsum : 0 ≤ A.equilibriumPayoff i 0 +
        ∫ z in 0..v_i, A.interimAllocProb i z :=
      add_nonneg hW0 hint
    simpa [henv i v_i] using hsum

/-- Supportwise IR makes zero-type expected payment nonpositive. -/
theorem interimExpectedPayment_zero_nonpos_of_isIndividuallyRationalOnSupport
    (A : BayesianSingleItemAuction I)
    (hIR : A.IsIndividuallyRationalOnSupport) (i : I) :
    A.interimExpectedPayment i 0 ≤ 0 := by
  have hW0 : 0 ≤ A.equilibriumPayoff i 0 :=
    hIR i 0 le_rfl (A.typeData.cdf i).omega_nonneg
  rw [equilibriumPayoff, interimQuasiLinearUtility] at hW0
  linarith

/-- IC and IR bound interim expected payment by the envelope term. -/
theorem interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible)
    (hIR : A.IsIndividuallyRationalOnSupport)
    (i : I) (v_i : ℝ) :
    A.interimExpectedPayment i v_i ≤
      A.interimAllocProb i v_i * v_i -
        ∫ z in 0..v_i, A.interimAllocProb i z := by
  have hpay := A.hasInterimPaymentFormula_of_isIncentiveCompatible hIC
  have hM0 := A.interimExpectedPayment_zero_nonpos_of_isIndividuallyRationalOnSupport hIR i
  calc
    A.interimExpectedPayment i v_i
        = A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := hpay i v_i
    _ ≤ A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := by
          linarith

end incentive_compatible

end BayesianSingleItemAuction
