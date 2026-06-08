/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.OptimalSingleItem
import EconCSLib.MechanismDesign.Auction.ReserveVickrey

/-!
# EconCSLib.MechanismDesign.Auction.RegularMyersonReserveSecondPrice

Regular Myerson auctions and reserve second-price auctions.

A bridge from the MSZ 12.59 Myerson optimality theorem in `OptimalSingleItem`
to the MSZ 12.61 reserve second-price corollary.

Design: the reserve mechanism is defined as an ordinary Bayesian single-item
auction, while no-tie, measurability, and candidate obligations are kept as
separate predicates and assumption packages. This mirrors the assumption-explicit
style used elsewhere in the library.

Main objects:
* `reserveSecondPriceAuction`: reserve second-price in a Bayesian environment.
* `StrictReserveBidProfile`: pointwise no-tie/no-boundary profiles.
* `TieAlignedReserveBidProfile`: pointwise winner-alignment profiles.
* `ReserveSecondPriceAEUniqueArgmax`: interim-slice a.e. uniqueness of the
  highest bid.
* `ReserveSecondPriceInterimMeasurabilityAssumptions`: interim measurability
  obligations for reserve second-price.
* `ReserveSecondPriceCandidateAssumptions`: nonnegative-reserve and interim
  measurability obligations for using reserve second-price as an IC/IR
  candidate.

Main result: common-regular-reserve MSZ 12.61 optimality.

At `rho = max b`, reserve second-price sells while the present Myerson allocation
withholds. The proof compares virtual surplus and expected revenue.

This file was generated with AI assistance and reviewed by Ma Yuxuan.

References:
* Maschler, Solan, Zamir, *Game Theory*, Corollary 12.61.
-/

open MeasureTheory

namespace BayesianSingleItemAuction

variable {I : Type*}

section ReserveSecondPriceAuction

/-! ## Basic objects -/

/-- Strict reserve profiles: nonnegative bids, unique argmax, and no reserve tie. -/
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

/-- Profiles where Myerson's winner is `argmaxBid` and no reserve tie occurs. -/
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

/-- Common-CDF presentation of strict-profile tie alignment. -/
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
    · exact hreserve.virtualValue_nonpos_of_lt_reserve hlt
    · rw [heq, hreserve.virtualValue_eq_zero i]
  exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos hnonpos

/-- Reserve second-price auction with `A`'s prior, opponent priors, and type data. -/
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
theorem reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_le_argmaxBid
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
theorem reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : rho < b (Auction.argmaxBid b)) :
    Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) := by
  exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_le_argmaxBid
    (le_of_lt hb)

/-- Below the reserve, reserve second-price withholds. -/
theorem reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_reserve
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
    exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_le_argmaxBid
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

/-- Reserve second-price is feasible as an optional-winner rule. -/
theorem reserveSecondPriceAuction_isFeasible
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) :
    (A.reserveSecondPriceAuction rho).IsFeasible := by
  exact (A.reserveSecondPriceAuction rho).isFeasible_of_optionalWinnerAllocation
    (Auction.ReserveSecondPrice.allocation rho) rfl

private lemma measurable_maxBid_comp
    [Fintype I] [Nontrivial I] {X : Type*} [MeasurableSpace X]
    (b : X → I → ℝ)
    (hb : ∀ j, Measurable fun x => b x j) :
    Measurable fun x => Auction.maxBid (b x) := by
  change Measurable fun x => Finset.univ.sup' Finset.univ_nonempty (b x)
  convert
    (Finset.measurable_sup'
      (s := Finset.univ)
      (hs := Finset.univ_nonempty)
      (f := fun j x => b x j)
      (fun j _ => hb j)) using 1
  ext x
  simp only [Finset.sup'_apply]

private lemma measurable_maxBidExcluding_comp
    [Fintype I] [Nontrivial I] [DecidableEq I] {X : Type*} [MeasurableSpace X]
    (b : X → I → ℝ)
    (hb : ∀ j, Measurable fun x => b x j) (i : I) :
    Measurable fun x => Auction.maxBidExcluding (b x) i := by
  change Measurable fun x => (Finset.univ.erase i).sup'
    Finset.univ_nontrivial.erase_nonempty (b x)
  convert
    (Finset.measurable_sup'
      (s := Finset.univ.erase i)
      (hs := Finset.univ_nontrivial.erase_nonempty)
      (f := fun j x => b x j)
      (fun j _ => hb j)) using 1
  ext x
  simp only [Finset.sup'_apply]

private lemma measurable_reportProfile_profileSplit
    [DecidableEq I] (i : I) :
    Measurable fun p : ℝ × OpponentTypeProfile I i => reportProfile i p.1 p.2 := by
  classical
  rw [measurable_pi_iff]
  intro j
  by_cases hji : j = i
  · simpa [reportProfile, hji] using
      (measurable_fst : Measurable fun p : ℝ × OpponentTypeProfile I i => p.1)
  · simpa [reportProfile, hji] using
      ((measurable_pi_apply (⟨j, hji⟩ : {j // j ≠ i})).comp
        (measurable_snd : Measurable fun p : ℝ × OpponentTypeProfile I i => p.2))

/-- The highest bid is measurable after a profile split. -/
theorem reserveSecondPrice_profileSplitMaxBid_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I] (i : I) :
    Measurable fun p : ℝ × OpponentTypeProfile I i =>
      Auction.maxBid (reportProfile i p.1 p.2) := by
  have hprofile : Measurable fun p : ℝ × OpponentTypeProfile I i =>
      reportProfile i p.1 p.2 :=
    measurable_reportProfile_profileSplit i
  have hcoords :
      ∀ j, Measurable fun p : ℝ × OpponentTypeProfile I i =>
        reportProfile i p.1 p.2 j := by
    intro j
    exact (measurable_pi_apply j).comp hprofile
  exact measurable_maxBid_comp
    (fun p : ℝ × OpponentTypeProfile I i => reportProfile i p.1 p.2) hcoords

/-- The highest bid is measurable for a fixed reported type. -/
theorem reserveSecondPrice_interimMaxBid_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I] (i : I) (z_i : ℝ) :
    Measurable fun t : OpponentTypeProfile I i =>
      Auction.maxBid (reportProfile i z_i t) := by
  have hpair : Measurable fun t : OpponentTypeProfile I i => (z_i, t) :=
    measurable_const.prodMk measurable_id
  simpa using
    (reserveSecondPrice_profileSplitMaxBid_measurable (I := I) i).comp hpair

/-- The reserve second-price winning-payment threshold is measurable after a
profile split. -/
theorem reserveSecondPrice_profileSplitWinningPayment_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (rho : ℝ) (i : I) :
    Measurable fun p : ℝ × OpponentTypeProfile I i =>
      max rho (Auction.maxBidExcluding (reportProfile i p.1 p.2) i) := by
  have hprofile : Measurable fun p : ℝ × OpponentTypeProfile I i =>
      reportProfile i p.1 p.2 :=
    measurable_reportProfile_profileSplit i
  have hcoords :
      ∀ j, Measurable fun p : ℝ × OpponentTypeProfile I i =>
        reportProfile i p.1 p.2 j := by
    intro j
    exact (measurable_pi_apply j).comp hprofile
  exact measurable_const.max
    (measurable_maxBidExcluding_comp
      (fun p : ℝ × OpponentTypeProfile I i => reportProfile i p.1 p.2) hcoords i)

/-- The reserve second-price winning-payment threshold is measurable for a
fixed reported type. -/
theorem reserveSecondPrice_interimWinningPayment_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (rho : ℝ) (i : I) (z_i : ℝ) :
    Measurable fun t : OpponentTypeProfile I i =>
      max rho (Auction.maxBidExcluding (reportProfile i z_i t) i) := by
  have hpair : Measurable fun t : OpponentTypeProfile I i => (z_i, t) :=
    measurable_const.prodMk measurable_id
  simpa using
    (reserveSecondPrice_profileSplitWinningPayment_measurable (I := I) rho i).comp hpair

/-- Interim event where bidder `i` strictly beats all opponents and meets the reserve. -/
def reserveSecondPriceInterimWinningSet [DecidableEq I]
    (rho : ℝ) (i : I) (z_i : ℝ) : Set (OpponentTypeProfile I i) :=
  {t | rho ≤ reportProfile i z_i t i ∧
    ∀ j, j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i}

/-- The strict interim winning event is measurable. -/
theorem reserveSecondPriceInterimWinningSet_measurable
    [Fintype I] [DecidableEq I] (rho : ℝ) (i : I) (z_i : ℝ) :
    MeasurableSet (reserveSecondPriceInterimWinningSet (I := I) rho i z_i) := by
  have hprofile : Measurable fun t : OpponentTypeProfile I i => reportProfile i z_i t := by
    have hpair : Measurable fun t : OpponentTypeProfile I i => (z_i, t) :=
      measurable_const.prodMk measurable_id
    exact (measurable_reportProfile_profileSplit i).comp hpair
  have hcoords :
      ∀ j, Measurable fun t : OpponentTypeProfile I i => reportProfile i z_i t j := by
    intro j
    exact (measurable_pi_apply j).comp hprofile
  have hreserve : MeasurableSet
      {t : OpponentTypeProfile I i | rho ≤ reportProfile i z_i t i} :=
    measurableSet_le measurable_const (hcoords i)
  have hstrict : MeasurableSet
      {t : OpponentTypeProfile I i |
        ∀ j, j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} := by
    classical
    haveI : Countable I := inferInstance
    have hsets :
        ∀ j : I, MeasurableSet
          {t : OpponentTypeProfile I i |
            j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} := by
      intro j
      by_cases hji : j = i
      · have hset :
            {t : OpponentTypeProfile I i |
              j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} = Set.univ := by
          ext t
          simp [hji]
        rw [hset]
        exact MeasurableSet.univ
      · have hset :
            {t : OpponentTypeProfile I i |
              j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} =
              {t : OpponentTypeProfile I i |
                reportProfile i z_i t j < reportProfile i z_i t i} := by
          ext t
          simp [hji]
        rw [hset]
        exact measurableSet_lt (hcoords j) (hcoords i)
    have hInter :
        MeasurableSet
          (⋂ j : I,
            {t : OpponentTypeProfile I i |
              j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i}) :=
      MeasurableSet.iInter hsets
    have hset :
        {t : OpponentTypeProfile I i |
          ∀ j, j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} =
          ⋂ j : I,
            {t : OpponentTypeProfile I i |
              j ≠ i → reportProfile i z_i t j < reportProfile i z_i t i} := by
      ext t
      simp
    rwa [hset]
  exact hreserve.inter hstrict

/-- Highest bids are a.e. unique on every reserve second-price interim slice. -/
def ReserveSecondPriceAEUniqueArgmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) : Prop :=
  ∀ i z_i,
    ∀ᵐ t ∂(A.reserveSecondPriceAuction rho).opponentPrior i,
      ∀ j, j ≠ Auction.argmaxBid (reportProfile i z_i t) →
        reportProfile i z_i t j <
          reportProfile i z_i t (Auction.argmaxBid (reportProfile i z_i t))

/-- Projection: a.e. uniqueness on one reserve second-price interim slice. -/
theorem ReserveSecondPriceAEUniqueArgmax.on_interimSlice
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceAEUniqueArgmax rho) (i : I) (z_i : ℝ) :
    ∀ᵐ t ∂(A.reserveSecondPriceAuction rho).opponentPrior i,
      ∀ j, j ≠ Auction.argmaxBid (reportProfile i z_i t) →
        reportProfile i z_i t j <
          reportProfile i z_i t (Auction.argmaxBid (reportProfile i z_i t)) :=
  h i z_i

/-- On profiles with a unique highest bid, reserve allocation to `i` is exactly
the strict interim winning event. -/
theorem reserveSecondPrice_allocation_eq_some_iff_mem_interimWinningSet_of_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {rho : ℝ} {i : I} {z_i : ℝ} {t : OpponentTypeProfile I i}
    (huniq :
      ∀ j, j ≠ Auction.argmaxBid (reportProfile i z_i t) →
        reportProfile i z_i t j <
          reportProfile i z_i t (Auction.argmaxBid (reportProfile i z_i t))) :
    Auction.ReserveSecondPrice.allocation rho (reportProfile i z_i t) = some i ↔
      t ∈ reserveSecondPriceInterimWinningSet (I := I) rho i z_i := by
  let b : I → ℝ := reportProfile i z_i t
  constructor
  · intro halloc
    have hwinner : Auction.SecondPrice.winner b = i :=
      Auction.ReserveSecondPrice.winner_eq_of_allocation_eq_some halloc
    have harg : Auction.argmaxBid b = i := by
      simpa [Auction.SecondPrice.winner] using hwinner
    have hreserve : rho ≤ b i := by
      have hreserve_winner :
          rho ≤ b (Auction.SecondPrice.winner b) :=
        Auction.ReserveSecondPrice.reserve_le_bid_winner_of_allocation_eq_some halloc
      simpa [hwinner] using hreserve_winner
    have hstrict : ∀ j, j ≠ i → b j < b i := by
      intro j hji
      have hjarg : j ≠ Auction.argmaxBid b := by
        rw [harg]
        exact hji
      simpa [b, harg] using huniq j hjarg
    exact ⟨hreserve, hstrict⟩
  · intro hwin
    have hreserve : rho ≤ b i := hwin.1
    have hstrict : ∀ j, j ≠ i → b j < b i := hwin.2
    have hi_arg : i = Auction.argmaxBid b :=
      Auction.eq_argmaxBid_of_strict_max b i hstrict
    have hreserve_arg : rho ≤ b (Auction.argmaxBid b) := by
      simpa [hi_arg] using hreserve
    have halloc_arg :
        Auction.ReserveSecondPrice.allocation rho b = some (Auction.argmaxBid b) :=
      reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_le_argmaxBid hreserve_arg
    simpa [b, hi_arg] using halloc_arg

/-- If the highest bid is a.e. unique, the reserve second-price allocation
integrand is a.e. strongly measurable. -/
theorem reserveSecondPriceAuction_interimAllocationIntegrand_aestronglyMeasurable_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (i : I) (z_i : ℝ)
    (hae_unique :
      ∀ᵐ t ∂(A.reserveSecondPriceAuction rho).opponentPrior i,
        ∀ j, j ≠ Auction.argmaxBid (reportProfile i z_i t) →
          reportProfile i z_i t j <
            reportProfile i z_i t (Auction.argmaxBid (reportProfile i z_i t))) :
    AEStronglyMeasurable
      (fun t => (A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t)
      ((A.reserveSecondPriceAuction rho).opponentPrior i) := by
  classical
  let winSet := reserveSecondPriceInterimWinningSet (I := I) rho i z_i
  let g : OpponentTypeProfile I i → ℝ := fun t => if t ∈ winSet then 1 else 0
  have hwin_meas : MeasurableSet winSet := by
    simpa [winSet] using
      reserveSecondPriceInterimWinningSet_measurable (I := I) rho i z_i
  have hg_meas : Measurable g :=
    Measurable.ite hwin_meas measurable_const measurable_const
  refine hg_meas.aestronglyMeasurable.congr ?_
  filter_upwards [hae_unique] with t huniq
  let b : I → ℝ := reportProfile i z_i t
  have hiff :=
    reserveSecondPrice_allocation_eq_some_iff_mem_interimWinningSet_of_unique_argmax
      (rho := rho) (i := i) (z_i := z_i) (t := t) huniq
  by_cases hwin : t ∈ winSet
  · have halloc : Auction.ReserveSecondPrice.allocation rho b = some i :=
      hiff.2 (by simpa [winSet, b] using hwin)
    simp [g, hwin, interimAllocationIntegrand, reserveSecondPriceAuction, b, halloc]
  · have hnotalloc : Auction.ReserveSecondPrice.allocation rho b ≠ some i := by
      intro halloc
      exact hwin (by simpa [winSet, b] using hiff.1 halloc)
    simp [g, hwin, interimAllocationIntegrand, reserveSecondPriceAuction, b, hnotalloc]

/-- If the highest bid is a.e. unique, the reserve second-price payment
integrand is a.e. strongly measurable. -/
theorem reserveSecondPriceAuction_interimPaymentIntegrand_aestronglyMeasurable_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (i : I) (z_i : ℝ)
    (hae_unique :
      ∀ᵐ t ∂(A.reserveSecondPriceAuction rho).opponentPrior i,
        ∀ j, j ≠ Auction.argmaxBid (reportProfile i z_i t) →
          reportProfile i z_i t j <
            reportProfile i z_i t (Auction.argmaxBid (reportProfile i z_i t))) :
    AEStronglyMeasurable
      (fun t => (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t)
      ((A.reserveSecondPriceAuction rho).opponentPrior i) := by
  classical
  let winSet := reserveSecondPriceInterimWinningSet (I := I) rho i z_i
  let g : OpponentTypeProfile I i → ℝ := fun t =>
    if t ∈ winSet then max rho (Auction.maxBidExcluding (reportProfile i z_i t) i) else 0
  have hwin_meas : MeasurableSet winSet := by
    simpa [winSet] using
      reserveSecondPriceInterimWinningSet_measurable (I := I) rho i z_i
  have hthreshold_meas :
      Measurable fun t : OpponentTypeProfile I i =>
        max rho (Auction.maxBidExcluding (reportProfile i z_i t) i) :=
    reserveSecondPrice_interimWinningPayment_measurable rho i z_i
  have hg_meas : Measurable g :=
    Measurable.ite hwin_meas hthreshold_meas measurable_const
  refine hg_meas.aestronglyMeasurable.congr ?_
  filter_upwards [hae_unique] with t huniq
  let b : I → ℝ := reportProfile i z_i t
  have hiff :=
    reserveSecondPrice_allocation_eq_some_iff_mem_interimWinningSet_of_unique_argmax
      (rho := rho) (i := i) (z_i := z_i) (t := t) huniq
  by_cases hwin : t ∈ winSet
  · have halloc : Auction.ReserveSecondPrice.allocation rho b = some i :=
      hiff.2 (by simpa [winSet, b] using hwin)
    have hpayment :
        (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t =
          max rho (Auction.maxBidExcluding b i) := by
      rw [interimPaymentIntegrand]
      change (A.reserveSecondPriceAuction rho).paymentRule b i =
        max rho (Auction.maxBidExcluding b i)
      rw [reserveSecondPriceAuction_paymentRule]
      rw [Auction.ReserveSecondPrice.mechanism_payment_of_allocation_eq_some halloc]
      exact Auction.ReserveSecondPrice.clearingPrice_eq_max_reserve_excluding_of_allocation_eq_some
        halloc
    simp [g, hwin, b, hpayment]
  · have hnotalloc : Auction.ReserveSecondPrice.allocation rho b ≠ some i := by
      intro halloc
      exact hwin (by simpa [winSet, b] using hiff.1 halloc)
    have hpayment :
        (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t = 0 := by
      rw [interimPaymentIntegrand]
      change (A.reserveSecondPriceAuction rho).paymentRule b i = 0
      rw [reserveSecondPriceAuction_paymentRule]
      exact Auction.ReserveSecondPrice.mechanism_payment_of_allocation_ne_some hnotalloc
    simp [g, hwin, hpayment]

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

/-- Reserve second-price split payments are bounded on the type support. -/
theorem reserveSecondPriceAuction_profileSplitPayment_norm_le_max_reserve_omega
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) (i : I)
    (p : ℝ × OpponentTypeProfile I i)
    (hp : p.1 ∈ Set.Ioc 0 (A.typeData.omega i)) :
    ‖(A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i‖ ≤
      max |rho| |A.typeData.omega i| := by
  have hpay :=
    A.reserveSecondPriceAuction_interimPaymentIntegrand_norm_le_max_reserve_report
      rho i p.1 p.2
  have hp_nonneg : 0 ≤ p.1 := le_of_lt hp.1
  have homega_nonneg : 0 ≤ A.typeData.omega i :=
    (A.typeData.cdf i).omega_nonneg
  have habs : |p.1| ≤ |A.typeData.omega i| := by
    rw [abs_of_nonneg hp_nonneg, abs_of_nonneg homega_nonneg]
    exact hp.2
  exact hpay.trans (max_le_max le_rfl habs)

/-- Reserve second-price split payments are a.e. bounded on the type support. -/
theorem reserveSecondPriceAuction_profileSplitPayment_bound
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] :
    ∀ i : I,
      ∃ C : ℝ,
        ∀ᵐ p : ℝ × OpponentTypeProfile I i
            ∂((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)),
          ‖(A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i‖ ≤ C := by
  intro i
  refine ⟨max |rho| |A.typeData.omega i|, ?_⟩
  have hsupport :
      ∀ᵐ p : ℝ × OpponentTypeProfile I i
          ∂((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)),
        p.1 ∈ Set.Ioc 0 (A.typeData.omega i) := by
    exact measurePreserving_fst.quasiMeasurePreserving.ae (A.ae_typeMeasure_mem_Ioc i)
  filter_upwards [hsupport] with p hp
  exact A.reserveSecondPriceAuction_profileSplitPayment_norm_le_max_reserve_omega rho i p hp

/-- Profile-split payment integrability for reserve second-price follows from
profile-split payment measurability. -/
theorem reserveSecondPriceAuction_profileSplit_payment_integrable_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i))) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)) :=
  profileSplit_payment_integrable_of_aestronglyMeasurable_of_bound
    hpay_meas
    (A.reserveSecondPriceAuction_profileSplitPayment_bound rho)

/-- Package reserve second-price profile-split measurability obligations. -/
theorem reserveSecondPriceAuction_profileSplitMeasurabilityAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)))
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i p.1)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i))) :
    A.ProfileSplitMeasurabilityAssumptions (A.reserveSecondPriceAuction rho) where
  payment_aestronglyMeasurable := hpay_meas
  virtual_surplus_aestronglyMeasurable := hvs_meas

/-- Package measurable reserve second-price profile-split integrands. -/
theorem reserveSecondPriceAuction_profileSplitMeasurabilityAssumptions_of_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (hpay_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i))
    (hvs_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i p.1)) :
    A.ProfileSplitMeasurabilityAssumptions (A.reserveSecondPriceAuction rho) :=
  ProfileSplitMeasurabilityAssumptions.of_measurable hpay_meas hvs_meas

/-- Reserve second-price profile-split integrability from profile-split
measurability and one-dimensional virtual-value integrability. -/
theorem reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hmeas : A.ProfileSplitMeasurabilityAssumptions (A.reserveSecondPriceAuction rho))
    (hvirtualValue_integrable :
      ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)) :
    A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho) :=
  hmeas.toProfileSplitIntegrabilityAssumptions_of_paymentBound_of_virtualValue_integrable
    (A.reserveSecondPriceAuction_isFeasible rho)
    (A.reserveSecondPriceAuction_profileSplitPayment_bound rho)
    hvirtualValue_integrable

/-- Raw a.e.-strong-measurability wrapper for reserve second-price profile-split integrability. -/
theorem reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)))
    (hvirtualValue_integrable :
      ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i))
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i p.1)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i))) :
    A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho) :=
  A.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    rho
    (A.reserveSecondPriceAuction_profileSplitMeasurabilityAssumptions rho hpay_meas hvs_meas)
    hvirtualValue_integrable

/-- Analytic-assumption entry point for reserve second-price profile-split
integrability, with profile-split measurability packaged. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (rho : ℝ)
    (hmeas : A.ProfileSplitMeasurabilityAssumptions (A.reserveSecondPriceAuction rho)) :
    A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho) := by
  haveI : ∀ i : I, IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact A.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    rho hmeas h.virtualValue_integrable_all

/-- Analytic-assumption entry point for reserve second-price profile-split
integrability, with raw a.e. strong measurability explicit. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (rho : ℝ)
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i)))
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i p.1)
          ((A.typeMeasure i).prod ((A.reserveSecondPriceAuction rho).opponentPrior i))) :
    A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho) := by
  exact h.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    rho
    (A.reserveSecondPriceAuction_profileSplitMeasurabilityAssumptions rho hpay_meas hvs_meas)

/-- Analytic-assumption entry point for reserve second-price profile-split
integrability, with raw measurable functions explicit. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (rho : ℝ)
    (hpay_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).paymentRule (reportProfile i p.1 p.2) i))
    (hvs_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            (A.reserveSecondPriceAuction rho).allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i p.1)) :
    A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho) := by
  exact h.reserveSecondPriceAuction_profileSplitIntegrabilityAssumptions_of_profileSplitMeasurable
    rho
    (A.reserveSecondPriceAuction_profileSplitMeasurabilityAssumptions_of_measurable
      rho hpay_meas hvs_meas)

/-- Interim measurability obligations for reserve second-price. -/
structure ReserveSecondPriceInterimMeasurabilityAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) : Prop where
  /-- Allocation interim integrands are a.e. strongly measurable. -/
  allocation_aestronglyMeasurable :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t => (A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t)
        ((A.reserveSecondPriceAuction rho).opponentPrior i)
  /-- Payment interim integrands are a.e. strongly measurable. -/
  payment_aestronglyMeasurable :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t => (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t)
        ((A.reserveSecondPriceAuction rho).opponentPrior i)

/-- Measurable reserve second-price interim integrands give the interim
measurability package. -/
theorem ReserveSecondPriceInterimMeasurabilityAssumptions.of_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (halloc_meas :
      ∀ i z_i,
        Measurable
          (fun t => (A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t))
    (hpay_meas :
      ∀ i z_i,
        Measurable
          (fun t => (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t)) :
    A.ReserveSecondPriceInterimMeasurabilityAssumptions rho where
  allocation_aestronglyMeasurable := fun i z_i =>
    (halloc_meas i z_i).aestronglyMeasurable
  payment_aestronglyMeasurable := fun i z_i =>
    (hpay_meas i z_i).aestronglyMeasurable

/-- A.e. unique highest bids give the reserve second-price interim measurability package. -/
theorem ReserveSecondPriceInterimMeasurabilityAssumptions.of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.ReserveSecondPriceInterimMeasurabilityAssumptions rho where
  allocation_aestronglyMeasurable := fun i z_i =>
    A.reserveSecondPriceAuction_interimAllocationIntegrand_aestronglyMeasurable_of_ae_unique_argmax
      rho i z_i (hae_unique.on_interimSlice i z_i)
  payment_aestronglyMeasurable := fun i z_i =>
    A.reserveSecondPriceAuction_interimPaymentIntegrand_aestronglyMeasurable_of_ae_unique_argmax
      rho i z_i (hae_unique.on_interimSlice i z_i)

/-- Convert a.e. uniqueness into the reserve second-price interim measurability package. -/
theorem ReserveSecondPriceAEUniqueArgmax.toInterimMeasurabilityAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.ReserveSecondPriceInterimMeasurabilityAssumptions rho :=
  ReserveSecondPriceInterimMeasurabilityAssumptions.of_ae_unique_argmax A rho h

/-- Candidate assumptions for reserve second-price.

This package records the reserve-side data needed to use reserve second-price
as a feasible IC/IR integrable candidate: a nonnegative reserve and measurable
interim allocation/payment integrands. Integrability follows from the built-in
reserve second-price bounds.
-/
structure ReserveSecondPriceCandidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ) : Prop where
  /-- The reserve is nonnegative, so zero-normalization gives interim IR. -/
  reserve_nonnegative :
    0 ≤ rho
  /-- Reserve second-price interim allocation/payment integrands are measurable. -/
  interim_measurability :
    A.ReserveSecondPriceInterimMeasurabilityAssumptions rho

/-- Projection: the reserve is nonnegative. -/
theorem ReserveSecondPriceCandidateAssumptions.reserveNonnegative
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceCandidateAssumptions rho) :
    0 ≤ rho :=
  h.reserve_nonnegative

/-- Projection: reserve second-price interim measurability. -/
theorem ReserveSecondPriceCandidateAssumptions.interimMeasurability
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.ReserveSecondPriceInterimMeasurabilityAssumptions rho :=
  h.interim_measurability

/-- Package nonnegative reserve and interim measurability as reserve second-price
candidate assumptions. -/
theorem ReserveSecondPriceCandidateAssumptions.of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.ReserveSecondPriceCandidateAssumptions rho where
  reserve_nonnegative := hrho0
  interim_measurability := hmeas

/-- Package raw a.e.-strong measurability as reserve second-price candidate assumptions. -/
theorem ReserveSecondPriceCandidateAssumptions.of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (hrho0 : 0 ≤ rho)
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
    A.ReserveSecondPriceCandidateAssumptions rho :=
  ReserveSecondPriceCandidateAssumptions.of_interimMeasurable hrho0
    ⟨halloc_meas, hpay_meas⟩

/-- Package measurable reserve second-price interim integrands as candidate assumptions. -/
theorem ReserveSecondPriceCandidateAssumptions.of_measurable
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (halloc_meas :
      ∀ i z_i,
        Measurable
          (fun t => (A.reserveSecondPriceAuction rho).interimAllocationIntegrand i z_i t))
    (hpay_meas :
      ∀ i z_i,
        Measurable
          (fun t => (A.reserveSecondPriceAuction rho).interimPaymentIntegrand i z_i t)) :
    A.ReserveSecondPriceCandidateAssumptions rho :=
  ReserveSecondPriceCandidateAssumptions.of_interimMeasurable hrho0
    (ReserveSecondPriceInterimMeasurabilityAssumptions.of_measurable A rho
      halloc_meas hpay_meas)

/-- Package nonnegative reserve and a.e. unique highest bids as reserve
second-price candidate assumptions. -/
theorem ReserveSecondPriceCandidateAssumptions.of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.ReserveSecondPriceCandidateAssumptions rho :=
  ReserveSecondPriceCandidateAssumptions.of_interimMeasurable
    hrho0 hae_unique.toInterimMeasurabilityAssumptions

/-- Measurable reserve second-price integrands are interim-integrable by bounds. -/
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

/-- Packaged interim measurability gives reserve second-price interim integrability. -/
theorem ReserveSecondPriceInterimMeasurabilityAssumptions.hasIntegrableInterimObjects
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects :=
  A.reserveSecondPriceAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable
    rho h.allocation_aestronglyMeasurable h.payment_aestronglyMeasurable

/-- Candidate-side assumptions imply reserve second-price interim integrability. -/
theorem ReserveSecondPriceCandidateAssumptions.hasIntegrableInterimObjects
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceCandidateAssumptions rho) :
    (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects :=
  h.interimMeasurability.hasIntegrableInterimObjects

/-- A.e. uniqueness gives reserve second-price interim integrability. -/
theorem ReserveSecondPriceAEUniqueArgmax.hasIntegrableInterimObjects
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceAEUniqueArgmax rho) :
    (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects :=
  h.toInterimMeasurabilityAssumptions.hasIntegrableInterimObjects

/-- A.e. unique highest bids give reserve second-price interim integrability. -/
theorem reserveSecondPriceAuction_hasIntegrableInterimObjects_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (rho : ℝ)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects :=
  hae_unique.hasIntegrableInterimObjects

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

/-- Candidate-side assumptions imply Bayesian interim IC for reserve second-price. -/
theorem ReserveSecondPriceCandidateAssumptions.isIncentiveCompatible
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceCandidateAssumptions rho) :
    (A.reserveSecondPriceAuction rho).IsIncentiveCompatible :=
  A.reserveSecondPriceAuction_isIncentiveCompatible rho h.hasIntegrableInterimObjects

/-- Candidate-side assumptions imply supportwise interim IR for reserve second-price. -/
theorem ReserveSecondPriceCandidateAssumptions.isIndividuallyRationalOnSupport
    [Fintype I] [Nontrivial I] [DecidableEq I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.ReserveSecondPriceCandidateAssumptions rho) :
    (A.reserveSecondPriceAuction rho).IsIndividuallyRationalOnSupport :=
  A.reserveSecondPriceAuction_isIndividuallyRationalOnSupport
    h.reserveNonnegative h.hasIntegrableInterimObjects

/-- Reserve second-price as a feasible IC/IR integrable candidate. -/
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

/-- Profile-split integrability entry point for reserve second-price as an
IC/IR candidate. -/
theorem reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_profileSplitIntegrability
    [Fintype I] [Nontrivial I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hind : A.HasIndependentTypePriors)
    (hrho : 0 ≤ rho)
    (hint : (A.reserveSecondPriceAuction rho).HasIntegrableInterimObjects)
    (hprofile :
      A.ProfileSplitIntegrabilityAssumptions (A.reserveSecondPriceAuction rho)) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) := by
  exact hprofile.toIsFeasibleICIRIntegrable hind
    (A.reserveSecondPriceAuction_hasSameSellingEnvironment rho)
    (A.reserveSecondPriceAuction_isFeasible rho)
    (A.reserveSecondPriceAuction_isIncentiveCompatible rho hint)
    (A.reserveSecondPriceAuction_isIndividuallyRationalOnSupport hrho hint)

/-- Analytic-assumption entry point for reserve second-price as a feasible IC/IR candidate. -/
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
  exact h.toIsFeasibleICIRIntegrable
    (A.reserveSecondPriceAuction rho) henv hfeas hIC hIR

/-- Analytic-assumption entry point for reserve second-price as a feasible IC/IR
candidate from interim measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isFeasibleICIRIntegrable
    hrho hmeas.hasIntegrableInterimObjects

/-- Analytic-assumption entry point for reserve second-price as a feasible IC/IR
candidate from the reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    {rho : ℝ}
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isFeasibleICIRIntegrable
    hcand.reserveNonnegative hcand.hasIntegrableInterimObjects

/-- Analytic-assumption entry point for reserve second-price as a feasible IC/IR
candidate from a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isFeasibleICIRIntegrable_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    {rho : ℝ}
    (hrho : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsFeasibleICIRIntegrable (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isFeasibleICIRIntegrable
    hrho hae_unique.hasIntegrableInterimObjects

end ReserveSecondPriceAuction

section ThresholdOrderFacts

/-! ## Local threshold order facts -/

private lemma max_reserve_maxBidExcluding_le_bid_of_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ} {i : I}
    (hi : i = Auction.argmaxBid b) (hrho : rho ≤ b i) :
    max rho (Auction.maxBidExcluding b i) ≤ b i := by
  have hexcl : Auction.maxBidExcluding b i ≤ b i := by
    simpa [hi] using Auction.maxBidExcluding_le_argmaxBid_bid (b := b)
  exact max_le hrho hexcl

private lemma bid_le_max_reserve_maxBidExcluding_of_ne_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ} {i : I}
    (hi : i ≠ Auction.argmaxBid b) :
    b i ≤ max rho (Auction.maxBidExcluding b i) := by
  have hle_max : b i ≤ Auction.maxBid b := by
    simpa [Auction.argmaxBid_eq_maxBid b] using Auction.bid_le_maxBid b i
  have hle_excl : b i ≤ Auction.maxBidExcluding b i := by
    simpa [Auction.maxBidExcluding_eq_maxBid_of_not_argmax (b := b) (i := i) hi] using
      hle_max
  exact le_trans hle_excl (le_max_right rho (Auction.maxBidExcluding b i))

private lemma bid_le_max_reserve_maxBidExcluding_of_argmaxBid_lt_reserve
    [Fintype I] [Nontrivial I] [DecidableEq I] {rho : ℝ} {b : I → ℝ}
    (hb : b (Auction.argmaxBid b) < rho) (i : I) :
    b i ≤ max rho (Auction.maxBidExcluding b i) := by
  exact le_trans (le_trans (Auction.bid_le_maxBid b i) (le_of_lt hb))
    (le_max_left rho (Auction.maxBidExcluding b i))

end ThresholdOrderFacts

section PaymentBridge

/-! ## Payment bridge -/

/-- Along one report coordinate, the Myerson allocation is a reserve-threshold step. -/
theorem virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_reserveThreshold
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

/-- The Myerson payment is the maximum of reserve and excluding-bid price. -/
theorem virtualSurplusMaximizingPaymentRule_eq_max_reserve_maxBidExcluding
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
    max_reserve_maxBidExcluding_le_bid_of_argmax hi hbi
  exact A.virtualSurplusMaximizingPaymentRule_eq_criticalValue_of_ae_stepAllocation
    hc0 hcy halloc
    (A.virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_reserveThreshold
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
    A.virtualSurplusMaximizingPaymentRule_eq_max_reserve_maxBidExcluding
      hA hrho hrho0 hstrict hb hi
  have halloc :
      Auction.ReserveSecondPrice.allocation rho b = some i := by
    simpa [hi] using
      reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_lt_argmaxBid
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
      reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_lt_argmaxBid
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
    (bid_le_max_reserve_maxBidExcluding_of_ne_argmax hi)
    halloc
    (A.virtualSurplusMaximizingAllocationRule_update_self_eq_step_of_reserveThreshold
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
    (bid_le_max_reserve_maxBidExcluding_of_argmaxBid_lt_reserve hb i)
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
    exact reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_reserve
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
    reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_lt_argmaxBid hb
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
  have hargmax_pos : 0 < A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) :=
    hreserve.virtualValue_pos_of_reserve_lt hb
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
    reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_lt_argmaxBid hb
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
    reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_reserve hb
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

/-- Common-CDF presentation of the tie-aligned allocation bridge. -/
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

/-!
Public bridge lemmas are layered by assumptions: generic threshold hypotheses,
packaged common regular reserves, then common-CDF presentations.
-/

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

/-! ### Common regular-reserve wrappers -/

/-- Packaged common regular-reserve presentation of the mechanism bridge. -/
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

/-! ### Common-CDF wrappers -/

/-- Common-CDF presentation of auction-interface equality away from reserve ties. -/
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

/-- Highest bids are a.e. unique under the full prior. -/
def AEUniqueArgmaxPrior [Fintype I] [Nontrivial I] (A : BayesianSingleItemAuction I) : Prop :=
  ∀ᵐ b ∂A.prior,
    ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)

/-- Projection: a.e. uniqueness of the highest bid under the full prior. -/
theorem AEUniqueArgmaxPrior.ae_unique_argmax
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I}
    (h : A.AEUniqueArgmaxPrior) :
    ∀ᵐ b ∂A.prior,
      ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b) :=
  h

/-- Package a.e. uniqueness of the highest bid under the full prior. -/
theorem AEUniqueArgmaxPrior.of_ae
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I}
    (h :
      ∀ᵐ b ∂A.prior,
        ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)) :
    A.AEUniqueArgmaxPrior :=
  h

/-- Projection: analytic assumptions give full-prior a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.aeUniqueArgmaxPrior
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.AEUniqueArgmaxPrior := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact AEUniqueArgmaxPrior.of_ae
    (A.ae_unique_argmaxBid_prior_of_hasIndependentTypePriors h.hasIndependentTypePriors)

/-- All bids are a.e. nonnegative under the full prior. -/
def AENonnegativeBidsPrior [Fintype I] (A : BayesianSingleItemAuction I) : Prop :=
  ∀ᵐ b ∂A.prior, ∀ i, 0 ≤ b i

/-- Projection: all bids are a.e. nonnegative under the full prior. -/
theorem AENonnegativeBidsPrior.ae_bid_nonnegative
    [Fintype I] {A : BayesianSingleItemAuction I}
    (h : A.AENonnegativeBidsPrior) :
    ∀ᵐ b ∂A.prior, ∀ i, 0 ≤ b i :=
  h

/-- Package a.e. nonnegative bids under the full prior. -/
theorem AENonnegativeBidsPrior.of_ae
    [Fintype I] {A : BayesianSingleItemAuction I}
    (h : ∀ᵐ b ∂A.prior, ∀ i, 0 ≤ b i) :
    A.AENonnegativeBidsPrior :=
  h

/-- Projection: analytic assumptions give full-prior a.e. nonnegative bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.aeNonnegativeBidsPrior
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.AENonnegativeBidsPrior := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact AENonnegativeBidsPrior.of_ae
    (A.ae_forall_eval_nonneg_prior_of_hasIndependentTypePriors h.hasIndependentTypePriors)

/-- The winning bid is a.e. not exactly the reserve under the full prior. -/
def AENoReserveTiePrior
    [Fintype I] [Nontrivial I] (A : BayesianSingleItemAuction I) (rho : ℝ) : Prop :=
  ∀ᵐ b ∂A.prior, rho ≠ b (Auction.argmaxBid b)

/-- Projection: the winning bid is a.e. not exactly the reserve. -/
theorem AENoReserveTiePrior.ae_noReserveTie
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.AENoReserveTiePrior rho) :
    ∀ᵐ b ∂A.prior, rho ≠ b (Auction.argmaxBid b) :=
  h

/-- Package a.e. no-reserve-tie profiles under the full prior. -/
theorem AENoReserveTiePrior.of_ae
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : ∀ᵐ b ∂A.prior, rho ≠ b (Auction.argmaxBid b)) :
    A.AENoReserveTiePrior rho :=
  h

/-- Projection: analytic assumptions give full-prior a.e. no reserve tie. -/
theorem RegularMyersonICIRAnalyticAssumptions.aeNoReserveTiePrior
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) (rho : ℝ) :
    A.AENoReserveTiePrior rho := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact AENoReserveTiePrior.of_ae
    (A.ae_argmaxBid_ne_const_prior_of_hasIndependentTypePriors
      h.hasIndependentTypePriors rho)

/-- Strict reserve profiles hold a.e. under the full prior. -/
def AEStrictReserveBidProfile
    [Fintype I] [Nontrivial I] (A : BayesianSingleItemAuction I) (rho : ℝ) : Prop :=
  ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b

/-- Projection: strict reserve profiles hold a.e. under the full prior. -/
theorem AEStrictReserveBidProfile.ae_strictReserveBidProfile
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.AEStrictReserveBidProfile rho) :
    ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b :=
  h

/-- Package a.e. strict reserve profiles under the full prior. -/
theorem AEStrictReserveBidProfile.of_ae
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : ∀ᵐ b ∂A.prior, StrictReserveBidProfile rho b) :
    A.AEStrictReserveBidProfile rho :=
  h

/-- Build a.e. strict reserve profiles from the prior-level components. -/
theorem AEStrictReserveBidProfile.of_components
    [Fintype I] [Nontrivial I] {A : BayesianSingleItemAuction I} {rho : ℝ}
    (hrho0 : 0 ≤ rho)
    (hnonneg : A.AENonnegativeBidsPrior)
    (hunique : A.AEUniqueArgmaxPrior)
    (hnotie : A.AENoReserveTiePrior rho) :
    A.AEStrictReserveBidProfile rho := by
  refine AEStrictReserveBidProfile.of_ae ?_
  filter_upwards
    [hnonneg.ae_bid_nonnegative, hnotie.ae_noReserveTie, hunique.ae_unique_argmax]
      with b hb_nonneg hb_reserve_ne hb_unique
  exact ⟨hrho0, hb_nonneg, hb_unique, hb_reserve_ne⟩

/-- A.e. unique highest bids give a.e. strict reserve profiles. -/
theorem RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.AEUniqueArgmaxPrior) :
    A.AEStrictReserveBidProfile rho := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact
    AEStrictReserveBidProfile.of_components hrho0
      h.aeNonnegativeBidsPrior hae_unique (h.aeNoReserveTiePrior rho)

/-- Nonnegative reserves give a.e. strict reserve profiles. -/
theorem RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hrho0 : 0 ≤ rho) :
    A.AEStrictReserveBidProfile rho := by
  haveI : ∀ i : I, MeasureTheory.IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact
    RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax h hrho0
      h.aeUniqueArgmaxPrior

/-- A.e. strict-profile equality gives expected seller-revenue equality. -/
theorem expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonRegularReserve rho)
    (hae : A.AEStrictReserveBidProfile rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  refine
    A.expectedSellerRevenueInEnvironment_congr_paymentRule_ae
      A.virtualSurplusMaximizingAuction
      (A.reserveSecondPriceAuction rho) ?_
  filter_upwards [hae.ae_strictReserveBidProfile] with b hb
  exact
    (A.virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_commonRegularReserve
      hreserve hb).2

/-- Common-CDF presentation of the a.e. expected-revenue bridge. -/
theorem expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonCDFRegularReserve rho)
    (hae : A.AEStrictReserveBidProfile rho) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    A.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
      hreserve.commonRegularReserve hae

/-! ### Analytic expected-revenue wrappers -/

/-- Analytic expected-revenue bridge with explicit a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.AEUniqueArgmaxPrior) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    A.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_strictReserveBidProfile_commonRegularReserve
      hreserve
        (RegularMyersonICIRAnalyticAssumptions.ae_strictReserveBidProfile_of_ae_unique_argmax
          h hrho0 hae_unique)

/-- Common-CDF presentation with explicit a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.AEUniqueArgmaxPrior) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
      hreserve.commonRegularReserve hrho0 hae_unique

/-- Positive-virtual-value reserve presentation with explicit a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.AEUniqueArgmaxPrior) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
      hreserve.commonRegularReserve hrho0 hae_unique

/-- Common-CDF positive-virtual-value presentation with explicit a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.AEUniqueArgmaxPrior) :
    A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction =
      A.expectedSellerRevenueInEnvironment (A.reserveSecondPriceAuction rho) := by
  exact
    h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_of_ae_unique_argmax_commonRegularReserve
      hreserve.commonRegularReserve hrho0 hae_unique

/-- Common regular-reserve expected-revenue equality under analytic assumptions. -/
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

/-- Common-CDF presentation using analytic assumptions' a.e. strict profiles. -/
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

/-! ### Reserve-presentation wrappers for expected revenue -/

/-- Positive-virtual-value reserve presentation of expected-revenue equality. -/
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

/-- Common-CDF positive-virtual-value reserve presentation of expected-revenue equality. -/
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
      exact reserveSecondPrice_allocation_eq_some_argmaxBid_of_reserve_le_argmaxBid
        (rho := rho) (b := b) hsell
    have hnonneg : 0 ≤ A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) :=
      hreserve.virtualValue_nonneg_of_reserve_le hsell
    rw [virtualSurplus, reserveSecondPriceAuction_allocationRule, halloc,
      max_eq_left hnonneg]
    simp [Finset.mem_univ]
  · have hlt : b (Auction.argmaxBid b) < rho := lt_of_not_ge hsell
    have halloc :
        Auction.ReserveSecondPrice.allocation rho b = none :=
      reserveSecondPrice_allocation_eq_none_of_argmaxBid_lt_reserve hlt
    have hnonpos : A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) ≤ 0 :=
      hreserve.virtualValue_nonpos_of_lt_reserve hlt
    rw [virtualSurplus, reserveSecondPriceAuction_allocationRule, halloc,
      max_eq_right hnonpos]
    simp

/-- Reserve second-price and Myerson have equal virtual surplus pointwise. -/
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

/-- Reserve second-price allocation is virtual-surplus optimal. -/
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

/-! ### Reserve-presentation wrappers for virtual-surplus optimality -/

/-- Common-CDF presentation of reserve second-price virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFRegularReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} (hreserve : A.CommonCDFRegularReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-- Positive-virtual-value reserve presentation of virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonVirtualValueReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-- Common-CDF positive-virtual-value reserve presentation of virtual-surplus optimality. -/
theorem reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonCDFVirtualValueReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ}
    (hreserve : A.CommonCDFVirtualValueReserve rho) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.reserveSecondPriceAuction rho).allocationRule :=
  A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
    hreserve.commonRegularReserve

/-! ### Expected-revenue optimality wrappers -/

/-- Reserve second-price is expected-revenue optimal among feasible IC/IR candidates. -/
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
  exact
    (A.virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_of_isRegular
      hreserve.isRegular h).of_revenue_eq
        (h.reserveSecondPriceAuction_isFeasibleICIRIntegrable hrho0 hint)
        (h.expectedSellerRevenueInEnvironment_virtualSurplusMaximizingAuction_eq_reserveSecondPriceAuction_commonRegularReserve
          hreserve hrho0)

/-- Common-CDF presentation of reserve second-price expected-revenue optimality. -/
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

/-- Positive-virtual-value reserve presentation of expected-revenue optimality. -/
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

/-- Common-CDF positive-virtual-value reserve presentation of expected-revenue optimality. -/
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

/-! ### Expected-revenue optimality from interim measurability -/

/-- Reserve second-price is expected-revenue optimal from interim measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve hrho0 hmeas.hasIntegrableInterimObjects

/-- Common-CDF presentation of expected-revenue optimality from interim
measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-- Positive-virtual-value presentation of expected-revenue optimality from
interim measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-- Common-CDF positive-virtual-value presentation of expected-revenue
optimality from interim measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-! ### Expected-revenue optimality from reserve-side candidate assumptions -/

/-- Reserve second-price is expected-revenue optimal from the reserve-side
candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve hcand.reserveNonnegative hcand.hasIntegrableInterimObjects

/-- Common-CDF presentation of expected-revenue optimality from the reserve-side
candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-- Positive-virtual-value presentation of expected-revenue optimality from the
reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-- Common-CDF positive-virtual-value presentation of expected-revenue
optimality from the reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-! ### Expected-revenue optimality from a.e. unique highest bids -/

/-- Reserve second-price is expected-revenue optimal from a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
    hreserve hrho0 hae_unique.hasIntegrableInterimObjects

/-- Common-CDF presentation of expected-revenue optimality from a.e. unique
highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFRegularReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

/-- Positive-virtual-value presentation of expected-revenue optimality from
a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonVirtualValueReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

/-- Common-CDF positive-virtual-value presentation of expected-revenue
optimality from a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonCDFVirtualValueReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      (A.reserveSecondPriceAuction rho)
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

/-! ### MSZ 12.61 endpoint wrappers -/

/-- MSZ 12.61: reserve second-price is regular-Myerson optimal. -/
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
  exact hcand.toIsRegularMyersonOptimalICIRAuction
    (A.reserveSecondPriceAuction_allocationRule_isVirtualSurplusOptimal_of_commonRegularReserve
      hreserve)
    (h.reserveSecondPriceAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_commonRegularReserve
      hreserve hrho0 hint)

/-- Common-CDF presentation of the MSZ 12.61 endpoint. -/
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

/-- Positive-virtual-value reserve presentation of the MSZ 12.61 endpoint. -/
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

/-- Common-CDF positive-virtual-value reserve presentation of the MSZ 12.61 endpoint. -/
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

/-! ### MSZ 12.61 endpoint wrappers from interim measurability -/

/-- MSZ 12.61 from reserve second-price interim measurability. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve hrho0 hmeas.hasIntegrableInterimObjects

/-- Common-CDF presentation of the interim-measurable MSZ 12.61 endpoint. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-- Positive-virtual-value presentation of the interim-measurable MSZ 12.61 endpoint. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-- Common-CDF positive-virtual-value presentation of the interim-measurable MSZ 12.61 endpoint. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_interimMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hmeas : A.ReserveSecondPriceInterimMeasurabilityAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_interimMeasurable
    hreserve.commonRegularReserve hrho0 hmeas

/-! ### MSZ 12.61 endpoint wrappers from reserve-side candidate assumptions -/

/-- MSZ 12.61 from the reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve hcand.reserveNonnegative hcand.hasIntegrableInterimObjects

/-- Common-CDF presentation of MSZ 12.61 from the reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-- Positive-virtual-value presentation of MSZ 12.61 from the reserve-side
candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-- Common-CDF positive-virtual-value presentation of MSZ 12.61 from the
reserve-side candidate package. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_candidateAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hcand : A.ReserveSecondPriceCandidateAssumptions rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_candidateAssumptions
    hreserve.commonRegularReserve hcand

/-! ### MSZ 12.61 endpoint from a.e. unique highest bids -/

/-- MSZ 12.61 from a common regular reserve and a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve
    hreserve hrho0 hae_unique.hasIntegrableInterimObjects

/-- Common-CDF presentation of MSZ 12.61 from a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFRegularReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFRegularReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

/-- Positive-virtual-value presentation of MSZ 12.61 from a.e. unique highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonVirtualValueReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

/-- Common-CDF positive-virtual-value presentation of MSZ 12.61 from a.e. unique
highest bids. -/
theorem RegularMyersonICIRAnalyticAssumptions.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonCDFVirtualValueReserve_of_ae_unique_argmax
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hreserve : A.CommonCDFVirtualValueReserve rho)
    (hrho0 : 0 ≤ rho)
    (hae_unique : A.ReserveSecondPriceAEUniqueArgmax rho) :
    A.IsRegularMyersonOptimalICIRAuction (A.reserveSecondPriceAuction rho) :=
  h.reserveSecondPriceAuction_isRegularMyersonOptimalICIR_commonRegularReserve_of_ae_unique_argmax
    hreserve.commonRegularReserve hrho0 hae_unique

end MechanismBridge

end BayesianSingleItemAuction
