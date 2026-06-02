import EconCSLib.MechanismDesign.Auction.OptimalSingleItem
import EconCSLib.MechanismDesign.Auction.ReserveVickrey

/-!
# EconCSLib.MechanismDesign.Auction.RegularMyersonReserveSecondPrice

Regular Myerson auctions and reserve second-price auctions.

This file connects the virtual-surplus-maximizing auction from
`OptimalSingleItem` with the reserve Vickrey auction from `ReserveVickrey`.

## Main definitions

* `reserveSecondPriceAuction`, the reserve second-price mechanism lifted into
  the Bayesian single-item interface while preserving `prior`, `opponentPrior`,
  and `typeData`;
* `StrictReserveBidProfile`, the pointwise no-tie/no-reserve-boundary condition
  under which Myerson and reserve second-price agree as mechanisms;
* `TieAlignedReserveBidProfile`, a weaker bridge condition separating highest
  bidder tie alignment from the reserve boundary condition.

## Main results

* Feasibility, DSIC, zero-normalization, interim-integrability, IC, and IR facts
  for `reserveSecondPriceAuction`, mostly obtained from the reusable
  `ReserveSecondPrice` API;
* pointwise allocation and payment bridges away from reserve ties;
* almost-everywhere strict-profile bridges under atomless independent priors;
* expected-revenue equality between the virtual-surplus-maximizing auction and
  reserve second-price;
* the MSZ 12.61 endpoint: reserve second-price is regular-Myerson optimal among
  feasible IC/IR candidates under the analytic assumptions.

At `rho = max b`, reserve second-price sells while the current Myerson
allocation withholds.  The final optimality theorem avoids false object equality:
the boundary has zero virtual surplus and is null under the analytic assumptions.

References:
* Maschler, Solan, Zamir, *Game Theory*, Corollary 12.61.
-/

open MeasureTheory

namespace BayesianSingleItemAuction

variable {I : Type*}

section ReserveSecondPriceAuction

/-! ## Basic objects -/

/-- Profiles where the reserve second-price auction and the Myerson auction agree pointwise.

The assumptions rule out three sources of ambiguity: negative bids/reserve
values, ties for the highest bid, and equality of the highest bid with the
reserve. -/
structure StrictReserveBidProfile
    [Fintype I] [Nontrivial I] (rho : ℝ) (b : I → ℝ) : Prop where
  /-- Nonnegative reserve. -/
  reserve_nonneg : 0 ≤ rho
  /-- Nonnegative bids. -/
  bid_nonneg : ∀ i, 0 ≤ b i
  /-- Unique highest bid. -/
  unique_argmax : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)
  /-- No exact reserve tie. -/
  no_reserve_tie : rho ≠ b (Auction.argmaxBid b)

/-- Profiles where Myerson and reserve second-price choose the same highest bidder.

This is weaker than `StrictReserveBidProfile`: it records the conclusion needed
by allocation bridge lemmas after tie alignment has already been proved. -/
structure TieAlignedReserveBidProfile
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (b : I → ℝ) : Prop where
  /-- Common selected winner. -/
  winner_eq_argmax : A.virtualSurplusMaximizingWinner b = Auction.argmaxBid b
  /-- No exact reserve tie. -/
  no_reserve_tie : rho ≠ b (Auction.argmaxBid b)

/-- Strict profiles are tie-aligned under a common regular reserve. -/
theorem StrictReserveBidProfile.toTieAlignedReserveBidProfile_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ} {b : I → ℝ}
    (hb : StrictReserveBidProfile rho b)
    (hreserve : A.CommonRegularReserve rho) :
    A.TieAlignedReserveBidProfile rho b where
  winner_eq_argmax :=
    A.virtualSurplusMaximizingWinner_eq_argmaxBid_of_strictVirtualValueOrder
      hreserve.hasStrictVirtualValueOrder hb.unique_argmax
  no_reserve_tie := hb.no_reserve_tie

/-- Common-CDF version of strict-profile tie alignment. -/
theorem StrictReserveBidProfile.toTieAlignedReserveBidProfile_of_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ} {b : I → ℝ}
    (hb : StrictReserveBidProfile rho b)
    (hreserve : A.CommonCDFRegularReserve rho) :
    A.TieAlignedReserveBidProfile rho b :=
  hb.toTieAlignedReserveBidProfile_of_commonRegularReserve hreserve.commonRegularReserve

/-- At `rho = max b`, the current Myerson allocation withholds. -/
theorem reserveTie_virtualSurplusMaximizingAllocationRule_eq_zero
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (htie : b (Auction.argmaxBid b) = rho) :
    A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) := by
  have hbelow : ∀ i, b i ≤ rho := by
    intro i
    exact le_trans (Auction.bid_le_maxBid b i) (le_of_eq htie)
  have hnonpos : ∀ i, A.virtualValue i (b i) ≤ 0 := by
    intro i
    rcases lt_or_eq_of_le (hbelow i) with hlt | heq
    · exact A.virtualValue_nonpos_of_lt_isReserveThreshold
        (hreserve.isReserveThreshold i) hlt
    · rw [heq, hreserve.common_virtualValue i rho, hreserve.reserve_zero]
  exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos hnonpos

/-- Reserve second-price auction in the Bayesian single-item interface.

The mechanism part is `ReserveSecondPrice.mechanism rho`; the Bayesian
environment is copied from `A`, so this construction can be compared with
`A.virtualSurplusMaximizingAuction` in the same prior/type-data environment. -/
noncomputable def reserveSecondPriceAuction [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) : BayesianSingleItemAuction I where
  allocationRule b i :=
    if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0
  paymentRule b := (Auction.ReserveSecondPrice.mechanism rho).paymentRule b
  prior := A.prior
  prob_prior := A.prob_prior
  opponentPrior := A.opponentPrior
  prob_opponentPrior := A.prob_opponentPrior
  typeData := A.typeData

@[simp] theorem reserveSecondPriceAuction_allocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (b : I → ℝ) :
    (A.reserveSecondPriceAuction rho).allocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 :=
  rfl

@[simp] theorem reserveSecondPriceAuction_paymentRule
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (b : I → ℝ) :
    (A.reserveSecondPriceAuction rho).paymentRule b =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b :=
  rfl

@[simp] theorem reserveSecondPriceAuction_prior
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).prior = A.prior :=
  rfl

@[simp] theorem reserveSecondPriceAuction_opponentPrior
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).opponentPrior = A.opponentPrior :=
  rfl

@[simp] theorem reserveSecondPriceAuction_typeData
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).typeData = A.typeData :=
  rfl

/-- When the highest bid meets the reserve, reserve second-price allocates to `argmaxBid`. -/
theorem reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_le_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : rho ≤ b (Auction.argmaxBid b)) :
    Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) := by
  have hle : rho ≤ b (Auction.SecondPrice.winner b) := by
    simpa [Auction.SecondPrice.winner] using hb
  have halloc :
      Auction.ReserveSecondPrice.allocation rho b =
        some (Auction.SecondPrice.winner b) :=
    (Auction.ReserveSecondPrice.allocation_eq_some_winner_iff
      (reserve := rho) (b := b)).2 hle
  simpa [Auction.SecondPrice.winner] using halloc

/-- Above the reserve, reserve second-price allocates to `argmaxBid`. -/
theorem reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : rho < b (Auction.argmaxBid b)) :
    Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) := by
  exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_le_argmaxBid
    (le_of_lt hb)

/-- Below the reserve, reserve second-price withholds. -/
theorem reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : b (Auction.argmaxBid b) < rho) :
    Auction.ReserveSecondPrice.allocation rho b = none := by
  have hb' : b (Auction.SecondPrice.winner b) < rho := by
    simpa [Auction.SecondPrice.winner] using hb
  exact (Auction.ReserveSecondPrice.allocation_eq_none_iff
    (reserve := rho) (b := b)).2 hb'

/-- At `rho = max b`, reserve second-price sells to `argmaxBid`. -/
theorem reserveTie_reserveSecondPriceAuction_allocationRule_eq_one
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (htie : b (Auction.argmaxBid b) = rho) :
    (A.reserveSecondPriceAuction rho).allocationRule b (Auction.argmaxBid b) = 1 := by
  have halloc :
      Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) := by
    exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_le_argmaxBid
      (by simp [htie])
  simp [halloc]

/-- At `rho = max b`, the two allocation conventions differ. -/
theorem reserveTie_virtualSurplusMaximizingAuction_allocationRule_ne_reserveSecondPriceAuction
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (htie : b (Auction.argmaxBid b) = rho) :
    (A.virtualSurplusMaximizingAuction).allocationRule b ≠
      (A.reserveSecondPriceAuction rho).allocationRule b := by
  intro halloc
  have hmyerson_fun :
      A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) :=
    A.reserveTie_virtualSurplusMaximizingAllocationRule_eq_zero hreserve htie
  have hmyerson :
      (A.virtualSurplusMaximizingAuction).allocationRule b (Auction.argmaxBid b) = 0 := by
    simpa [virtualSurplusMaximizingAuction] using
      congr_fun hmyerson_fun (Auction.argmaxBid b)
  have hreserve_alloc :
      (A.reserveSecondPriceAuction rho).allocationRule b (Auction.argmaxBid b) = 1 :=
    A.reserveTie_reserveSecondPriceAuction_allocationRule_eq_one htie
  have hpoint := congr_fun halloc (Auction.argmaxBid b)
  rw [hreserve_alloc, hmyerson] at hpoint
  norm_num at hpoint

/-- The reserve second-price lift keeps `A`'s prior, opponent priors, and type data. -/
theorem reserveSecondPriceAuction_hasSameSellingEnvironment
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    A.HasSameSellingEnvironment (A.reserveSecondPriceAuction rho) := by
  exact ⟨rfl, rfl, rfl⟩

/-- The lifted reserve second-price allocation is a feasible single-item allocation.

This is just the generic optional-winner feasibility lemma applied to
`ReserveSecondPrice.allocation`. -/
theorem reserveSecondPriceAuction_isFeasible
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).IsFeasible := by
  exact (A.reserveSecondPriceAuction rho).isFeasible_of_optionalWinnerAllocation
    (Auction.ReserveSecondPrice.allocation rho) rfl

/-- Reserve second-price allocation integrands are pointwise bounded by one. -/
theorem reserveSecondPriceAuction_interimAllocationIntegrand_norm_le_one
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (i : I) (z_i : ℝ)
    (t : OpponentTypeProfile I i) :
    ‖(A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t‖ ≤ 1 := by
  have hx := (A.reserveSecondPriceAuction_isFeasible rho).1 (reportProfile i z_i t) i
  rw [interimAllocationIntegrand, Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/-- Reserve second-price payment integrands are bounded by the reserve/report scale. -/
theorem reserveSecondPriceAuction_interimPaymentIntegrand_norm_le_max_reserve_report
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (i : I) (z_i : ℝ)
    (t : OpponentTypeProfile I i) :
    ‖(A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t‖ ≤
      max |rho| |z_i| := by
  let b : I → ℝ := reportProfile i z_i t
  simpa [interimPaymentIntegrand, reserveSecondPriceAuction, b, Real.norm_eq_abs] using
    Auction.ReserveSecondPrice.mechanism_payment_abs_le_max_reserve_bid
      (reserve := rho) (b := b) (i := i)

/-- A measurability-only route to interim integrability for reserve second-price.

The required bounds are pointwise: allocation is in `{0,1}`, and the winner's
payment lies between the reserve and her fixed report. -/
theorem reserveSecondPriceAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (halloc_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => (A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t)
          ((A.reserveSecondPriceAuction rho).opponentPrior i))
    (hpay_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t => (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t)
          ((A.reserveSecondPriceAuction rho).opponentPrior i)) :
    (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects := by
  refine (A.reserveSecondPriceAuction rho)
    |>.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound
      halloc_meas hpay_meas ?_ ?_
  · intro i z_i
    exact ⟨1, Filter.Eventually.of_forall fun t =>
      A.reserveSecondPriceAuction_interimAllocationIntegrand_norm_le_one rho i z_i t⟩
  · intro i z_i
    exact ⟨max |rho| |z_i|, Filter.Eventually.of_forall fun t =>
      A.reserveSecondPriceAuction_interimPaymentIntegrand_norm_le_max_reserve_report
        rho i z_i t⟩

/-- Utility in the Bayesian wrapper equals the underlying reserve second-price utility. -/
theorem reserveSecondPriceAuction_quasiLinearUtility_eq
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (b v : I → ℝ) (i : I) :
    (A.reserveSecondPriceAuction rho).quasiLinearUtility b v i =
      Auction.ReserveSecondPrice.utility rho v b i := by
  by_cases halloc : Auction.ReserveSecondPrice.allocation rho b = some i
  · rw [Auction.ReserveSecondPrice.utility_winner halloc]
    simp [SingleParameterMechanism.quasiLinearUtility, SingleParameterMechanism.payment,
      SingleParameterMechanism.quasiLinearValue, reserveSecondPriceAuction,
      halloc]
  · rw [Auction.ReserveSecondPrice.utility_loser halloc]
    simp [SingleParameterMechanism.quasiLinearUtility, SingleParameterMechanism.payment,
      SingleParameterMechanism.quasiLinearValue, reserveSecondPriceAuction,
      halloc]

/-- Reserve second-price is DSIC after lifting to the Bayesian single-item interface. -/
theorem reserveSecondPriceAuction_isDSIC
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).IsDSIC := by
  unfold SingleParameterMechanism.IsDSIC MechanismWithTransfers.isDSIC
  intro v i s' σ
  change
    (A.reserveSecondPriceAuction rho).quasiLinearUtility (StrategicGame.deviate σ i s') v i ≤
      (A.reserveSecondPriceAuction rho).quasiLinearUtility
        (StrategicGame.deviate σ i (v i)) v i
  rw [reserveSecondPriceAuction_quasiLinearUtility_eq,
    reserveSecondPriceAuction_quasiLinearUtility_eq]
  have hdom :=
    Auction.ReserveSecondPrice.truthful_weakly_dominant (I := I) (U := ℝ) rho v i s' σ
  simpa [Auction.ReserveSecondPrice.game] using hdom

/-- A nonnegative reserve gives zero normalization. -/
theorem reserveSecondPriceAuction_isZeroNormalized
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hrho : 0 ≤ rho) :
    (A.reserveSecondPriceAuction rho).IsZeroNormalized := by
  intro i b
  exact Auction.ReserveSecondPrice.mechanism_payment_update_self_zero_of_nonneg_reserve
    hrho i b

/-- DSIC gives Bayesian interim IC once interim objects are integrable. -/
theorem reserveSecondPriceAuction_isIncentiveCompatible
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    (A.reserveSecondPriceAuction rho).IsIncentiveCompatible := by
  exact (A.reserveSecondPriceAuction rho).isIncentiveCompatible_of_isDSIC
    hint (A.reserveSecondPriceAuction_isDSIC rho)

/-- Nonnegative reserve second-price is supportwise interim IR. -/
theorem reserveSecondPriceAuction_isIndividuallyRationalOnSupport
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    (A.reserveSecondPriceAuction rho).IsIndividuallyRationalOnSupport := by
  have hIC : (A.reserveSecondPriceAuction rho).IsIncentiveCompatible :=
    A.reserveSecondPriceAuction_isIncentiveCompatible rho hint
  have henv : (A.reserveSecondPriceAuction rho).HasInterimEnvelopeFormula :=
    (A.reserveSecondPriceAuction rho).hasInterimEnvelopeFormula_of_isIncentiveCompatible hIC
  have hnonneg :
      (A.reserveSecondPriceAuction rho).HasNonnegativeInterimAllocationIntegralOnSupport :=
    (A.reserveSecondPriceAuction rho).hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible
      (A.reserveSecondPriceAuction_isFeasible rho)
  exact
    (A.reserveSecondPriceAuction rho)
      |>.isIndividuallyRationalOnSupport_of_isZeroNormalized_of_hasInterimEnvelopeFormula
        (A.reserveSecondPriceAuction_isZeroNormalized hrho) henv hnonneg

/-- Package reserve second-price as a feasible IC/IR candidate.

This version takes virtual-surplus integrability as an explicit hypothesis, so
it can be used without the global analytic assumptions from `OptimalSingleItem`. -/
theorem reserveSecondPriceAuction_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects)
    (hvirt : A.IntegrableVirtualSurplus (A.reserveSecondPriceAuction rho).allocationRule) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) := by
  exact ⟨
    A.reserveSecondPriceAuction_hasSameSellingEnvironment rho,
    A.reserveSecondPriceAuction_isFeasible rho,
    A.reserveSecondPriceAuction_isIncentiveCompatible rho hint,
    A.reserveSecondPriceAuction_isIndividuallyRationalOnSupport hrho hint,
    hvirt⟩

/-- Package reserve second-price as a feasible IC/IR candidate under analytic assumptions.

Compared with `reserveSecondPriceAuction_isFeasibleICIRIntegrable`, this version
derives virtual-surplus integrability from
`RegularMyersonICIRAnalyticAssumptions`. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) := by
  have henv : A.HasSameSellingEnvironment (A.reserveSecondPriceAuction rho) :=
    A.reserveSecondPriceAuction_hasSameSellingEnvironment rho
  have hfeas : (A.reserveSecondPriceAuction rho).IsFeasible :=
    A.reserveSecondPriceAuction_isFeasible rho
  have hIC : (A.reserveSecondPriceAuction rho).IsIncentiveCompatible :=
    A.reserveSecondPriceAuction_isIncentiveCompatible rho hint
  have hIR : (A.reserveSecondPriceAuction rho).IsIndividuallyRationalOnSupport :=
    A.reserveSecondPriceAuction_isIndividuallyRationalOnSupport hrho hint
  exact ⟨henv, hfeas, hIC, hIR,
    h.candidate_integrableVirtualSurplus
      (A.reserveSecondPriceAuction rho) henv hfeas hIC hIR⟩

end ReserveSecondPriceAuction

section ThresholdOrderFacts

/-! ## Local threshold order facts -/

private lemma max_commonReserve_maxBidExcluding_le_bid_of_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ} {i : I}
    (hi : i = Auction.argmaxBid b) (hrho : rho ≤ b i) :
    max rho (Auction.maxBidExcluding b i) ≤ b i := by
  have hexcl : Auction.maxBidExcluding b i ≤ b i := by
    simpa [hi] using Auction.maxBidExcluding_le_argmaxBid_bid (b := b)
  exact max_le hrho hexcl

private lemma bid_le_max_commonReserve_maxBidExcluding_of_ne_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ} {i : I}
    (hi : i ≠ Auction.argmaxBid b) :
    b i ≤ max rho (Auction.maxBidExcluding b i) := by
  have hle_max : b i ≤ Auction.maxBid b := by
    simpa [Auction.argmaxBid_eq_maxBid b] using Auction.bid_le_maxBid b i
  have hle_excl : b i ≤ Auction.maxBidExcluding b i := by
    simpa [Auction.maxBidExcluding_eq_maxBid_of_not_argmax (b := b) (i := i) hi] using
      hle_max
  exact le_trans hle_excl (le_max_right rho (Auction.maxBidExcluding b i))

private lemma bid_le_max_commonReserve_maxBidExcluding_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : b (Auction.argmaxBid b) < rho) (i : I) :
    b i ≤ max rho (Auction.maxBidExcluding b i) := by
  exact le_trans (le_trans (Auction.bid_le_maxBid b i) (le_of_lt hb))
    (le_max_left rho (Auction.maxBidExcluding b i))

end ThresholdOrderFacts

section PaymentBridge

/-! ## Payment bridge -/

/-- Along one bidder's report, the Myerson allocation is the critical-value step. -/
theorem virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho) :
    ∀ᵐ z ∂MeasureTheory.volume, z ∈ Set.uIoc 0 (b i) →
      A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i =
        if max rho (Auction.maxBidExcluding b i) < z then (1 : ℝ) else 0 := by
  let c := max rho (Auction.maxBidExcluding b i)
  have hzero_below :
      ∀ {z : ℝ}, z < c →
        A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i = 0 := by
    intro z hz_lt_c
    by_cases hpos : 0 < A.winningVirtualValue (Function.update b i z)
    · have hne : i ≠ A.virtualSurplusMaximizingWinner (Function.update b i z) := by
        intro hi_win
        have hwin : A.virtualSurplusMaximizingWinner (Function.update b i z) = i := hi_win.symm
        have hvirt_i_pos : 0 < A.virtualValue i z := by
          rw [winningVirtualValue, hwin, Function.update_self] at hpos
          exact hpos
        by_cases hz_rho : z < rho
        · exact (not_le_of_gt hvirt_i_pos)
            (A.virtualValue_nonpos_of_lt_isReserveThreshold (hrho i) hz_rho)
        · have hrho_le_z : rho ≤ z := le_of_not_gt hz_rho
          have hz_lt_excl : z < Auction.maxBidExcluding b i := by
            by_contra hnot
            have hexcl_le_z : Auction.maxBidExcluding b i ≤ z := le_of_not_gt hnot
            have hc_le_z : c ≤ z := max_le hrho_le_z hexcl_le_z
            exact not_lt_of_ge hc_le_z hz_lt_c
          obtain ⟨j, hji, hjmax⟩ := Auction.exists_maxBidExcluding b i
          have hz_lt_j : z < b j := by
            simpa [hjmax] using hz_lt_excl
          have hvirt_lt : A.virtualValue i z < A.virtualValue j (b j) :=
            hA (i := i) (j := j) hz_lt_j
          have hvirt_j_le_i : A.virtualValue j (b j) ≤ A.virtualValue i z := by
            have hle :=
              A.virtualSurplusMaximizingWinner_virtualValue_ge (Function.update b i z) j
            rw [winningVirtualValue, hwin, Function.update_self] at hle
            simpa [Function.update_of_ne hji] using hle
          exact not_lt_of_ge hvirt_j_le_i hvirt_lt
      · simp [virtualSurplusMaximizingAllocationRule, hpos, hne]
    · simp [virtualSurplusMaximizingAllocationRule, hpos]
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume c] with z hz_ne _hz_mem
  by_cases hz_threshold : c < z
  · have hcz : max rho (Auction.maxBidExcluding b i) < z := by
      simpa [c] using hz_threshold
    have hz_reserve : rho < z :=
      lt_of_le_of_lt (le_max_left rho (Auction.maxBidExcluding b i)) hcz
    have harg :
        Auction.argmaxBid (Function.update b i z) = i :=
      Auction.argmaxBid_update_self_eq_of_maxBidExcluding_lt
        (b := b) (i := i)
        (lt_of_le_of_lt (le_max_right rho (Auction.maxBidExcluding b i)) hcz)
    have hstrict_update :
        ∀ j,
          j ≠ Auction.argmaxBid (Function.update b i z) →
            (Function.update b i z) j <
              (Function.update b i z) (Auction.argmaxBid (Function.update b i z)) := by
      intro j hj
      have hji : j ≠ i := by
        simpa [harg] using hj
      have hlt :=
        Auction.update_self_strict_max_of_maxBidExcluding_lt
          (b := b) (i := i)
          (lt_of_le_of_lt (le_max_right rho (Auction.maxBidExcluding b i)) hcz) j hji
      have hlt' : (Function.update b i z) j < z := by
        simpa [Function.update_self] using hlt
      rw [harg, Function.update_self]
      exact hlt'
    have hb_update :
        rho < (Function.update b i z) (Auction.argmaxBid (Function.update b i z)) := by
      rw [harg, Function.update_self]
      exact hz_reserve
    have halloc :
        A.virtualSurplusMaximizingAllocationRule (Function.update b i z) =
          fun k =>
            if k = Auction.argmaxBid (Function.update b i z) then (1 : ℝ) else 0 :=
      A.virtualSurplusMaximizingAllocationRule_eq_argmaxBidIndicator_of_commonReserve_lt_argmaxBid
      hA hrho hstrict_update hb_update
    rw [congr_fun halloc i]
    have hif : max rho (Auction.maxBidExcluding b i) < z := hcz
    simp [harg, hif]
  · have hz_le_threshold : z ≤ max rho (Auction.maxBidExcluding b i) :=
      le_of_not_gt hz_threshold
    have hz_lt_c : z < c := lt_of_le_of_ne hz_le_threshold hz_ne
    simpa [c, hz_threshold] using hzero_below hz_lt_c

/-- The Myerson payment is the reserve/excluding-bid critical value. -/
theorem virtualSurplusMaximizingPaymentRule_eq_max_commonReserve_maxBidExcluding
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b))
    (hi : i = Auction.argmaxBid b) :
    A.virtualSurplusMaximizingPaymentRule b i =
      max rho (Auction.maxBidExcluding b i) := by
  have halloc_fun :
      A.virtualSurplusMaximizingAllocationRule b =
        fun k => if k = Auction.argmaxBid b then (1 : ℝ) else 0 :=
    A.virtualSurplusMaximizingAllocationRule_eq_argmaxBidIndicator_of_commonReserve_lt_argmaxBid
      hA hrho hstrict hb
  have halloc : A.virtualSurplusMaximizingAllocationRule b i = 1 := by
    rw [congr_fun halloc_fun i]
    simp [hi]
  have hc0 : 0 ≤ max rho (Auction.maxBidExcluding b i) :=
    le_trans hrho0 (le_max_left rho (Auction.maxBidExcluding b i))
  have hbi : rho ≤ b i := by
    simpa [hi] using le_of_lt hb
  have hcy : max rho (Auction.maxBidExcluding b i) ≤ b i :=
    max_commonReserve_maxBidExcluding_le_bid_of_argmax hi hbi
  exact A.virtualSurplusMaximizingPaymentRule_eq_criticalValue_of_ae_stepAllocation
    hc0 hcy halloc
    (A.virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_commonReserve
      hA hrho)

/-- In the strict sale case, the Myerson payment equals the clearing price. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_clearingPrice_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b))
    (hi : i = Auction.argmaxBid b) :
    A.virtualSurplusMaximizingPaymentRule b i =
      Auction.ReserveSecondPrice.clearingPrice rho b := by
  have hpay :
      A.virtualSurplusMaximizingPaymentRule b i =
        max rho (Auction.maxBidExcluding b i) :=
    A.virtualSurplusMaximizingPaymentRule_eq_max_commonReserve_maxBidExcluding
      hA hrho hrho0 hstrict hb hi
  have halloc :
      Auction.ReserveSecondPrice.allocation rho b = some i := by
    simpa [hi] using
      reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_lt_argmaxBid
        (rho := rho) (b := b) hb
  have hprice :
      Auction.ReserveSecondPrice.clearingPrice rho b =
        max rho (Auction.maxBidExcluding b i) :=
    Auction.ReserveSecondPrice.clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some
      halloc
  rw [hpay, hprice]

/-- Payment equality for the winner in the strict sale case. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b))
    (hi : i = Auction.argmaxBid b) :
    A.virtualSurplusMaximizingPaymentRule b i =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b i := by
  have halloc :
      Auction.ReserveSecondPrice.allocation rho b = some i := by
    simpa [hi] using
      reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_lt_argmaxBid
        (rho := rho) (b := b) hb
  rw [Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some halloc]
  exact
    A.virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_clearingPrice_of_commonReserve_lt_argmaxBid
      hA hrho hrho0 hstrict hb hi

/-- Non-winners pay zero in the strict sale case. -/
theorem virtualSurplusMaximizingPaymentRule_eq_zero_of_ne_argmaxBid_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b))
    (hi : i ≠ Auction.argmaxBid b) :
    A.virtualSurplusMaximizingPaymentRule b i = 0 := by
  have halloc_fun :
      A.virtualSurplusMaximizingAllocationRule b =
        fun k => if k = Auction.argmaxBid b then (1 : ℝ) else 0 :=
    A.virtualSurplusMaximizingAllocationRule_eq_argmaxBidIndicator_of_commonReserve_lt_argmaxBid
      hA hrho hstrict hb
  have halloc : A.virtualSurplusMaximizingAllocationRule b i = 0 := by
    rw [congr_fun halloc_fun i]
    simp [hi]
  exact A.virtualSurplusMaximizingPaymentRule_eq_zero_of_ae_stepAllocation
    (hb_nonneg i)
    (bid_le_max_commonReserve_maxBidExcluding_of_ne_argmax hi)
    halloc
    (A.virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_commonReserve
      hA hrho)

/-- Payment-vector equality in the strict sale case. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_commonReserve_lt_argmaxBid_pointwise
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingPaymentRule b =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  funext i
  by_cases hi : i = Auction.argmaxBid b
  · exact
      A.virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_commonReserve_lt_argmaxBid
        hA hrho hrho0 hstrict hb hi
  · have hmyerson :
        A.virtualSurplusMaximizingPaymentRule b i = 0 :=
      A.virtualSurplusMaximizingPaymentRule_eq_zero_of_ne_argmaxBid_commonReserve_lt_argmaxBid
        hA hrho hb_nonneg hstrict hb hi
    rw [hmyerson,
      Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_ne_winner
        (by simpa [Auction.SecondPrice.winner] using hi)]

/-- Below the reserve, Myerson payments are zero. -/
theorem virtualSurplusMaximizingPaymentRule_eq_zero_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    {rho : ℝ} {b : I → ℝ} {i : I}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hb : b (Auction.argmaxBid b) < rho) :
    A.virtualSurplusMaximizingPaymentRule b i = 0 := by
  have halloc_fun :
      A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) :=
    A.virtualSurplusMaximizingAllocationRule_eq_zero_of_argmaxBid_lt_commonReserve hrho hb
  have halloc : A.virtualSurplusMaximizingAllocationRule b i = 0 := by
    simpa using congr_fun halloc_fun i
  have hstep :
      ∀ᵐ z ∂MeasureTheory.volume, z ∈ Set.uIoc 0 (b i) →
        A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i =
          if max rho (Auction.maxBidExcluding b i) < z then (1 : ℝ) else 0 := by
    refine Filter.Eventually.of_forall ?_
    intro z hz_mem
    have hz_le_bi : z ≤ b i := by
      have hbi0 : 0 ≤ b i := hb_nonneg i
      have hzIoc : z ∈ Set.Ioc 0 (b i) := by
        simpa [Set.uIoc_of_le hbi0] using hz_mem
      exact hzIoc.2
    have hz_lt_rho : z < rho := by
      exact lt_of_le_of_lt (le_trans hz_le_bi (Auction.bid_le_maxBid b i)) hb
    have hmax_update :
        (Function.update b i z) (Auction.argmaxBid (Function.update b i z)) < rho := by
      by_cases harg_i : Auction.argmaxBid (Function.update b i z) = i
      · rw [harg_i, Function.update_self]
        exact hz_lt_rho
      · have hle :
          (Function.update b i z) (Auction.argmaxBid (Function.update b i z)) ≤
            b (Auction.argmaxBid (Function.update b i z)) := by
          rw [Function.update_of_ne harg_i]
        exact lt_of_le_of_lt
          (le_trans hle (Auction.bid_le_maxBid b (Auction.argmaxBid (Function.update b i z))))
          hb
    have hzero_update :
        A.virtualSurplusMaximizingAllocationRule (Function.update b i z) = fun _ => (0 : ℝ) :=
      A.virtualSurplusMaximizingAllocationRule_eq_zero_of_argmaxBid_lt_commonReserve
        hrho hmax_update
    have hnlt : ¬ max rho (Auction.maxBidExcluding b i) < z := by
      intro hlt
      exact not_lt_of_ge hz_lt_rho.le
        (lt_of_le_of_lt (le_max_left rho (Auction.maxBidExcluding b i)) hlt)
    rw [congr_fun hzero_update i]
    simp [hnlt]
  exact A.virtualSurplusMaximizingPaymentRule_eq_zero_of_ae_stepAllocation
    (hb_nonneg i)
    (bid_le_max_commonReserve_maxBidExcluding_of_argmaxBid_lt_commonReserve hb i)
    halloc hstep

/-- Payment-vector equality in the strict no-sale case. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hb : b (Auction.argmaxBid b) < rho) :
    A.virtualSurplusMaximizingPaymentRule b =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  funext i
  have hmyerson :
      A.virtualSurplusMaximizingPaymentRule b i = 0 :=
    A.virtualSurplusMaximizingPaymentRule_eq_zero_of_argmaxBid_lt_commonReserve
      hrho hb_nonneg hb
  have hreserve :
      Auction.ReserveSecondPrice.allocation rho b = none := by
    exact reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_commonReserve
      (rho := rho) (b := b) hb
  rw [hmyerson,
    Auction.ReserveSecondPrice.mechanism_payment_eq_zero_of_allocation_eq_none hreserve]

end PaymentBridge

section AllocationBridge

/-! ## Allocation bridge -/

/-- Allocation equality in the strict sale case. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  have hmyerson :
      A.virtualSurplusMaximizingAllocationRule b =
        fun i => if i = Auction.argmaxBid b then (1 : ℝ) else 0 :=
    A.virtualSurplusMaximizingAllocationRule_eq_argmaxBidIndicator_of_commonReserve_lt_argmaxBid
      hA hrho hstrict hb
  have hreserve :
      Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) :=
    reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_lt_argmaxBid hb
  rw [hmyerson, hreserve]
  funext i
  by_cases hi : i = Auction.argmaxBid b
  · simp [hi]
  · have hne : Auction.argmaxBid b ≠ i := by
      intro h
      exact hi h.symm
    simp [hi, hne]

/-- Pointwise allocation equality in the strict sale case. -/
theorem virtualSurplusMaximizingAllocationRule_eq_one_iff_reserveSecondPrice_allocation_eq_some_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b)) (i : I) :
    A.virtualSurplusMaximizingAllocationRule b i = 1 ↔
      Auction.ReserveSecondPrice.allocation rho b = some i := by
  have hbridge :=
    congr_fun
      (A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonReserve_lt_argmaxBid
        hA hrho hstrict hb) i
  rw [hbridge]
  by_cases halloc : Auction.ReserveSecondPrice.allocation rho b = some i <;> simp [halloc]

/-- Tie-aligned allocation equality in the strict sale case. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonRegularReserve_lt_argmaxBid_tieAligned
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hwinner : A.virtualSurplusMaximizingWinner b = Auction.argmaxBid b)
    (hb : rho < b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  have hargmax_pos : 0 < A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
    have hzero : A.virtualValue (Auction.argmaxBid b) rho = 0 := by
      rw [hreserve.common_virtualValue (Auction.argmaxBid b) rho, hreserve.reserve_zero]
    have hlt :
        A.virtualValue (Auction.argmaxBid b) rho <
          A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
      rw [hreserve.common_virtualValue (Auction.argmaxBid b) rho,
        hreserve.common_virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b))]
      exact hreserve.strictMono_phi hb
    rwa [hzero] at hlt
  have hpos : 0 < A.winningVirtualValue b := by
    simpa [winningVirtualValue, hwinner] using hargmax_pos
  have hmyerson :
      A.virtualSurplusMaximizingAllocationRule b =
        fun i => if i = Auction.argmaxBid b then (1 : ℝ) else 0 := by
    simpa [hwinner] using
      A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_winningVirtualValue_pos
        b hpos
  have hreserve_alloc :
      Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) :=
    reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_lt_argmaxBid hb
  rw [hmyerson, hreserve_alloc]
  funext i
  by_cases hi : i = Auction.argmaxBid b
  · simp [hi]
  · have hne : Auction.argmaxBid b ≠ i := by
      intro h
      exact hi h.symm
    simp [hi, hne]

/-- Allocation equality in the strict no-sale case. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb : b (Auction.argmaxBid b) < rho) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  have hmyerson :
      A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) :=
    A.virtualSurplusMaximizingAllocationRule_eq_zero_of_argmaxBid_lt_commonReserve hrho hb
  have hreserve :
      Auction.ReserveSecondPrice.allocation rho b = none :=
    reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_commonReserve hb
  rw [hmyerson, hreserve]
  funext i
  simp

/-- Tie-aligned allocation equality under a common regular reserve. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonRegularReserve_tieAligned
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hb : A.TieAlignedReserveBidProfile rho b) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  rcases lt_or_gt_of_ne hb.no_reserve_tie with habove | hbelow
  · exact
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonRegularReserve_lt_argmaxBid_tieAligned
        hreserve hb.winner_eq_argmax habove
  · exact
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_argmaxBid_lt_commonReserve
        hreserve.isReserveThreshold hbelow

/-- Common-CDF version of the tie-aligned allocation bridge. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonCDFRegularReserve_tieAligned
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonCDFRegularReserve rho)
    (hb : A.TieAlignedReserveBidProfile rho b) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  exact
    A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonRegularReserve_tieAligned
      hreserve.commonRegularReserve hb

end AllocationBridge

section MechanismBridge

/-! ## Mechanism bridge -/

/-- Mechanism equality in the strict sale case. -/
theorem virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b)) :
    (A.virtualSurplusMaximizingMechanism).allocationRule b =
        (fun i =>
          if (Auction.ReserveSecondPrice.mechanism rho).allocationRule b = some i then
            (1 : ℝ)
          else
            0) ∧
      (A.virtualSurplusMaximizingMechanism).paymentRule b =
        (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  constructor
  · simpa using
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonReserve_lt_argmaxBid
        hA hrho hstrict hb
  · simpa using
      A.virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_commonReserve_lt_argmaxBid_pointwise
        hA hrho hrho0 hb_nonneg hstrict hb

/-- Mechanism equality in the strict no-sale case. -/
theorem virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hb : b (Auction.argmaxBid b) < rho) :
    (A.virtualSurplusMaximizingMechanism).allocationRule b =
        (fun i =>
          if (Auction.ReserveSecondPrice.mechanism rho).allocationRule b = some i then
            (1 : ℝ)
          else
            0) ∧
      (A.virtualSurplusMaximizingMechanism).paymentRule b =
        (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  constructor
  · simpa using
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_argmaxBid_lt_commonReserve
        hrho hb
  · simpa using
      A.virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_argmaxBid_lt_commonReserve
        hrho hb_nonneg hb

/-- Mechanism equality away from the reserve tie. -/
theorem virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    (A.virtualSurplusMaximizingMechanism).allocationRule b =
        (fun i =>
          if (Auction.ReserveSecondPrice.mechanism rho).allocationRule b = some i then
            (1 : ℝ)
          else
            0) ∧
      (A.virtualSurplusMaximizingMechanism).paymentRule b =
        (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  rcases lt_or_gt_of_ne hreserve_ne with habove | hbelow
  · exact
      A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_commonReserve_lt_argmaxBid
        hA hrho hrho0 hb_nonneg hstrict habove
  · exact
      A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_argmaxBid_lt_commonReserve
        hrho hb_nonneg hbelow

/-- Allocation component of the unified no-reserve-tie bridge. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  rcases lt_or_gt_of_ne hreserve_ne with habove | hbelow
  · exact
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonReserve_lt_argmaxBid
        hA hrho hstrict habove
  · exact
      A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_argmaxBid_lt_commonReserve
        hrho hbelow

/-- Payment component of the unified no-reserve-tie bridge. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingPaymentRule b =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  have h :=
    A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_noReserveTie
      hA hrho hrho0 hb_nonneg hstrict hreserve_ne
  simpa using h.2

/-- Auction-interface bridge from the reusable strict-profile package. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_strictReserveBidProfile
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb : StrictReserveBidProfile rho b) :
    (A.virtualSurplusMaximizingAuction).allocationRule b =
        (A.reserveSecondPriceAuction rho).allocationRule b ∧
      (A.virtualSurplusMaximizingAuction).paymentRule b =
        (A.reserveSecondPriceAuction rho).paymentRule b := by
  have hbridge :=
    A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_noReserveTie
      hA hrho hb.reserve_nonneg hb.bid_nonneg hb.unique_argmax hb.no_reserve_tie
  exact ⟨by simpa [virtualSurplusMaximizingAuction] using hbridge.1,
    by simpa [virtualSurplusMaximizingAuction] using hbridge.2⟩

/-- Common-regular-reserve version of the mechanism bridge. -/
theorem virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_commonRegularReserve_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    (A.virtualSurplusMaximizingMechanism).allocationRule b =
        (fun i =>
          if (Auction.ReserveSecondPrice.mechanism rho).allocationRule b = some i then
            (1 : ℝ)
          else
            0) ∧
      (A.virtualSurplusMaximizingMechanism).paymentRule b =
        (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  exact
    A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_noReserveTie
      hreserve.hasStrictVirtualValueOrder hreserve.isReserveThreshold
      hrho0 hb_nonneg hstrict hreserve_ne

/-- Allocation component of the common-regular-reserve bridge. -/
theorem virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_commonRegularReserve_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if Auction.ReserveSecondPrice.allocation rho b = some i then (1 : ℝ) else 0 := by
  exact
    A.virtualSurplusMaximizingAllocationRule_eq_reserveSecondPriceIndicator_of_noReserveTie
      hreserve.hasStrictVirtualValueOrder hreserve.isReserveThreshold hstrict hreserve_ne

/-- Payment component of the common-regular-reserve bridge. -/
theorem virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_commonRegularReserve_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingPaymentRule b =
      (Auction.ReserveSecondPrice.mechanism rho).paymentRule b := by
  exact
    A.virtualSurplusMaximizingPaymentRule_eq_reserveSecondPrice_paymentRule_of_noReserveTie
      hreserve.hasStrictVirtualValueOrder hreserve.isReserveThreshold
      hrho0 hb_nonneg hstrict hreserve_ne

/-- Auction-interface form under packaged common regular-reserve assumptions. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    (A.virtualSurplusMaximizingAuction).allocationRule b =
        (A.reserveSecondPriceAuction rho).allocationRule b ∧
      (A.virtualSurplusMaximizingAuction).paymentRule b =
        (A.reserveSecondPriceAuction rho).paymentRule b := by
  have hbridge :=
    A.virtualSurplusMaximizingMechanism_eq_reserveSecondPriceMechanism_of_commonRegularReserve_noReserveTie
      hreserve hrho0 hb_nonneg hstrict hreserve_ne
  exact ⟨by simpa [virtualSurplusMaximizingAuction] using hbridge.1,
    by simpa [virtualSurplusMaximizingAuction] using hbridge.2⟩

/-- Strict-profile version under a common regular reserve. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hb : StrictReserveBidProfile rho b) :
    (A.virtualSurplusMaximizingAuction).allocationRule b =
        (A.reserveSecondPriceAuction rho).allocationRule b ∧
      (A.virtualSurplusMaximizingAuction).paymentRule b =
        (A.reserveSecondPriceAuction rho).paymentRule b := by
  exact
    A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_strictReserveBidProfile
      hreserve.hasStrictVirtualValueOrder hreserve.isReserveThreshold hb

/-- Strict-profile family under a common regular reserve. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_on_strictReserveBidProfiles_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonRegularReserve rho) :
    ∀ b : I → ℝ, StrictReserveBidProfile rho b →
      (A.virtualSurplusMaximizingAuction).allocationRule b =
          (A.reserveSecondPriceAuction rho).allocationRule b ∧
        (A.virtualSurplusMaximizingAuction).paymentRule b =
          (A.reserveSecondPriceAuction rho).paymentRule b := by
  intro b hb
  exact
    A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve
      hreserve hb

/-- Common-CDF version of auction-interface equality at a strict profile. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonCDFRegularReserve_noReserveTie
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hb_nonneg : ∀ i, 0 ≤ b i)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hreserve_ne : rho ≠ b (Auction.argmaxBid b)) :
    (A.virtualSurplusMaximizingAuction).allocationRule b =
        (A.reserveSecondPriceAuction rho).allocationRule b ∧
      (A.virtualSurplusMaximizingAuction).paymentRule b =
        (A.reserveSecondPriceAuction rho).paymentRule b := by
  exact
    A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve_noReserveTie
      hreserve.commonRegularReserve hrho0 hb_nonneg hstrict hreserve_ne

/-- Strict-profile version under a common-CDF regular reserve. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hreserve : A.CommonCDFRegularReserve rho)
    (hb : StrictReserveBidProfile rho b) :
    (A.virtualSurplusMaximizingAuction).allocationRule b =
        (A.reserveSecondPriceAuction rho).allocationRule b ∧
      (A.virtualSurplusMaximizingAuction).paymentRule b =
        (A.reserveSecondPriceAuction rho).paymentRule b := by
  exact
    A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_strictReserveBidProfile
      hreserve.hasStrictVirtualValueOrder hreserve.isReserveThreshold hb

/-- Strict-profile family under a common-CDF regular reserve. -/
theorem virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_on_strictReserveBidProfiles_of_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonCDFRegularReserve rho) :
    ∀ b : I → ℝ, StrictReserveBidProfile rho b →
      (A.virtualSurplusMaximizingAuction).allocationRule b =
          (A.reserveSecondPriceAuction rho).allocationRule b ∧
        (A.virtualSurplusMaximizingAuction).paymentRule b =
          (A.reserveSecondPriceAuction rho).paymentRule b := by
  intro b hb
  exact
    A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonCDFRegularReserve
      hreserve hb

/-! ## Expected revenue and optimality -/

/-- Analytic assumptions package the almost-everywhere strict reserve profile
condition once an almost-everywhere unique highest bid is supplied. -/
theorem RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hrho0 : 0 ≤ rho)
    (hae_unique :
      ∀ᵐ b ∂A.prior,
        ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)) :
    ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  filter_upwards
    [A.ae_forall_eval_nonneg_prior_of_hasIndependentTypePriors h.independent_type_priors,
      A.ae_argmaxBid_ne_const_prior_of_hasIndependentTypePriors h.independent_type_priors rho,
      hae_unique] with b hb_nonneg hb_reserve_ne hb_unique
  exact ⟨hrho0, hb_nonneg, hb_unique, hb_reserve_ne⟩

/-- Analytic assumptions make reserve profiles strict almost everywhere for a
nonnegative reserve. -/
theorem RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hrho0 : 0 ≤ rho) :
    ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact
    RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax h hrho0
      (A.ae_unique_argmaxBid_prior_of_hasIndependentTypePriors h.independent_type_priors)

/-- Expected-revenue equality from strict-profile equality almost everywhere.

This is the measure-theoretic bridge used by 12.61: pointwise mechanism equality
is only required off a null reserve-tie set, and seller revenue depends only on
the payment rule. -/
theorem expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hae : ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  refine
    A.expectedSellerRevenueInEnvironment_congr_paymentRule_ae
      A.virtualSurplusMaximizingAuction
      (A.reserveSecondPriceAuction rho) ?_
  filter_upwards [hae] with b hb
  exact
    (A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve
      hreserve hb).2

/-- Common-CDF version of the a.e. expected-revenue bridge. -/
theorem expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonCDFRegularReserve rho)
    (hae : ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    A.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
      hreserve.commonRegularReserve hae

/-- Analytic-assumption expected-revenue bridge with explicit a.e. unique argmax. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique :
      ∀ᵐ b ∂A.prior,
        ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    A.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
      hreserve
        (RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax
          h hrho0 hae_unique)

/-- Common-CDF version of the analytic-assumption expected-revenue bridge. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique :
      ∀ᵐ b ∂A.prior,
        ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
      hreserve.commonRegularReserve hrho0 hae_unique

/-- Analytic-assumption expected-revenue bridge under a common regular reserve.

Atomless independent priors make the highest-bid tie and reserve-boundary sets
null, so the pointwise strict-profile bridge integrates to equality of expected
seller revenue. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    A.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
      hreserve
        (RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile h hrho0)

/-- Common-CDF version of the analytic-assumption expected-revenue bridge. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
      hreserve.commonRegularReserve hrho0

/-- Virtual-value reserve version of expected-revenue equality. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) :=
  h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
    hreserve.commonRegularReserve hrho0

/-- Common-CDF virtual-value reserve version of expected-revenue equality. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) :=
  h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
    hreserve.commonRegularReserve hrho0

/-! ### Optimality without object equality -/

/-- Under a common regular reserve, the winning virtual value is the highest bid's value. -/
theorem CommonRegularReserve.winningVirtualValue_eq_argmaxBid
    [Fintype I] [Nontrivial I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ} (hreserve : A.CommonRegularReserve rho)
    (b : I → ℝ) :
    A.winningVirtualValue b =
      A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
  apply le_antisymm
  · have hbid :
        b (A.virtualSurplusMaximizingWinner b) ≤ b (Auction.argmaxBid b) :=
      Auction.bid_le_maxBid b (A.virtualSurplusMaximizingWinner b)
    calc
      A.winningVirtualValue b
          = hreserve.phi (b (A.virtualSurplusMaximizingWinner b)) := by
              simp [winningVirtualValue, hreserve.common_virtualValue]
      _ ≤ hreserve.phi (b (Auction.argmaxBid b)) :=
              hreserve.strictMono_phi.monotone hbid
      _ = A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
              rw [hreserve.common_virtualValue]
  · exact A.virtualSurplusMaximizingWinner_virtualValue_ge b (Auction.argmaxBid b)

/-- Reserve second-price virtual surplus is the positive part of the highest virtual value. -/
theorem virtualSurplus_reserveSecondPriceAuction_allocationRule_eq_max_argmaxBid_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hreserve : A.CommonRegularReserve rho)
    (b : I → ℝ) :
    A.virtualSurplus (A.reserveSecondPriceAuction rho).allocationRule b =
      max (A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b))) 0 := by
  by_cases hsell : rho ≤ b (Auction.argmaxBid b)
  · have halloc :
        Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) := by
      exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_commonReserve_le_argmaxBid
        (rho := rho) (b := b) hsell
    have hnonneg : 0 ≤ A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
      have hphi_nonneg :
          0 ≤ hreserve.phi (b (Auction.argmaxBid b)) := by
        rw [← hreserve.reserve_zero]
        exact hreserve.strictMono_phi.monotone hsell
      rwa [hreserve.common_virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b))]
    rw [virtualSurplus, reserveSecondPriceAuction_allocationRule, halloc,
      max_eq_left hnonneg]
    simp [Finset.mem_univ]
  · have hlt : b (Auction.argmaxBid b) < rho := lt_of_not_ge hsell
    have halloc :
        Auction.ReserveSecondPrice.allocation rho b = none :=
      reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_commonReserve hlt
    have hnonpos : A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) ≤ 0 := by
      have hphi_nonpos :
          hreserve.phi (b (Auction.argmaxBid b)) ≤ 0 := by
        rw [← hreserve.reserve_zero]
        exact hreserve.strictMono_phi.monotone hlt.le
      rwa [hreserve.common_virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b))]
    rw [virtualSurplus, reserveSecondPriceAuction_allocationRule, halloc,
      max_eq_right hnonpos]
    simp

/-- Reserve second-price and Myerson have the same virtual surplus pointwise.

This avoids claiming that the two allocation rules are equal at the reserve
boundary.  Both rules achieve the same positive part of the highest virtual
value, which is the quantity needed for virtual-surplus optimality. -/
theorem virtualSurplus_reserveSecondPriceAuction_allocationRule_eq_virtualSurplusMaximizingAllocationRule_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hreserve : A.CommonRegularReserve rho)
    (b : I → ℝ) :
    A.virtualSurplus (A.reserveSecondPriceAuction rho).allocationRule b =
      A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b := by
  rw [
    A.virtualSurplus_reserveSecondPriceAuction_allocationRule_eq_max_argmaxBid_of_commonRegularReserve
      hreserve b,
    A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_max_winningVirtualValue_zero
      b,
    hreserve.winningVirtualValue_eq_argmaxBid b]

/-- Reserve second-price allocation is virtual-surplus optimal.

The proof compares virtual surplus directly, so it remains valid even though
reserve second-price and the current Myerson allocation convention differ at
`rho = max b`. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hreserve : A.CommonRegularReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule := by
  constructor
  · exact (A.reserveSecondPriceAuction_isFeasible rho).isSingleItemAllocationRule
  · intro y hy b
    calc
      A.virtualSurplus y b
          ≤ A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b :=
              A.virtualSurplus_le_virtualSurplusMaximizingAllocationRule
                (x := y) (b := b) (hy.1 b) (hy.2 b)
      _ = A.virtualSurplus (A.reserveSecondPriceAuction rho).allocationRule b :=
              (A.virtualSurplus_reserveSecondPriceAuction_allocationRule_eq_virtualSurplusMaximizingAllocationRule_of_commonRegularReserve
                hreserve b).symm

/-- Common-CDF wrapper for reserve second-price virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hreserve : A.CommonCDFRegularReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-- Virtual-value reserve wrapper for reserve second-price virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonVirtualValueReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-- Common-CDF virtual-value reserve wrapper for reserve second-price virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonCDFVirtualValueReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-- Reserve second-price is expected-revenue optimal among feasible IC/IR candidates.

The theorem transfers the abstract Myerson optimality result from
`OptimalSingleItem` through the a.e. expected-revenue equality bridge above. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) := by
  constructor
  · exact h.reserveSecondPriceAuction_isFeasibleICIRIntegrable hrho0 hint
  · intro C hC
    have hopt :
        A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
          A.virtualSurplusMaximizingAuction
          (fun C => A.IsFeasibleICIRIntegrable C) :=
      A.virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_of_isRegular
        hreserve.isRegular h
    have hle :
        A.expectedSellerRevenueInEnvironment C ≤
          A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction :=
      hopt.2 C hC
    have heq :
        A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
          A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) :=
      h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
        hreserve hrho0
    simpa [heq] using hle

/-- Common-CDF version of reserve second-price expected-revenue optimality. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

/-- Virtual-value reserve version of reserve second-price expected-revenue optimality. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

/-- Common-CDF virtual-value reserve version of expected-revenue optimality. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

/-- MSZ 12.61: reserve second-price is regular-Myerson optimal.

This is the main endpoint for a common regular reserve: reserve second-price is
feasible, IC, IR, virtual-surplus optimal, and expected-seller-revenue optimal
among feasible IC/IR integrable candidates. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) := by
  have hcand : A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) :=
    h.reserveSecondPriceAuction_isFeasibleICIRIntegrable hrho0 hint
  exact ⟨
    A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
      hreserve,
    hcand.isFeasible,
    hcand.isIncentiveCompatible,
    hcand.isIndividuallyRationalOnSupport,
    h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
      hreserve hrho0 hint⟩

/-- Common-CDF wrapper for the MSZ 12.61 reserve second-price optimality endpoint. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

/-- MSZ 12.61 wrapper using `rho = inf {t | 0 < phi t}` and `phi rho = 0`. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

/-- Common-CDF positive-virtual-value MSZ 12.61 wrapper. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve.commonRegularReserve hrho0 hint

end MechanismBridge

end BayesianSingleItemAuction
