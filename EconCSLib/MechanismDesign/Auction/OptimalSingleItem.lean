/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.BayesianSingleItem
import EconCSLib.MechanismDesign.Auction.Myerson
import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.Monotone

/-!
# EconCSLib.MechanismDesign.Auction.OptimalSingleItem

Regular Myerson optimal single-item auctions.

This file defines virtual values, the virtual-surplus-maximizing allocation
rule, its Myerson payment rule, and the IC/IR revenue-optimality interface for
MSZ 12.59. The main public result is
`virtualSurplusMaximizingAuction_regularMyersonOptimalICIR_of_isRegular`.

## Design

The base auction record is kept separate from analytic side conditions.  As in
the fair-division `Allocation` / `IsAllocation` split and the extensive-game
`FiniteExtractable` package, regularity, density, Fubini, integrability, and
candidate-mechanism obligations are exposed through `Is...` predicates and
`*Assumptions` structures at theorem entry points.

## Main definitions

* `virtualValue`, `IsRegular`, `IsReserveThreshold`
* `IsVirtualValueCutoff`, `virtualValueCutoff`, `VirtualValueReserve`,
  `VirtualValueCutoffReserve`
* `CommonRegularReserve` and reserve-presentation wrappers
* `virtualSurplus`, `expectedVirtualSurplus`
* `IsSingleItemAllocationRule`, `IsVirtualSurplusOptimalAllocationRule`
* `IsRevenueComparable`, `IsRevenueUpperBounded`
* `IsFeasibleICIRIntegrable`
* `InterimFubiniAnalyticAssumptions`
* `VirtualValueMeanZeroAnalyticAssumptions`
* `ProfileSplitMeasurabilityAssumptions`
* `ProfileSplitIntegrabilityAssumptions`
* `RegularMyersonICIREnvironmentAssumptions`
* `RegularMyersonICIRCandidateProfileSplitAssumptions`
* `RegularMyersonICIRAnalyticAssumptions`
* `IsRegularMyersonOptimalICIRAuction`
* `virtualSurplusMaximizingAllocationRule`
* `virtualSurplusMaximizingPaymentRule`, `virtualSurplusMaximizingMechanism`,
  `virtualSurplusMaximizingAuction`

## Main proofs

* reserve-threshold and sale/no-sale behavior
* feasibility and pointwise virtual-surplus optimality
* expected virtual-surplus monotonicity
* monotonicity and DSIC via `MechanismDesign.Auction.Myerson`
* bridge from ex-post DSIC to interim IC, plus conditional interim IR
* expected-revenue comparison through virtual-surplus identities and upper bounds
* `virtualSurplusMaximizingAuction_regularMyersonOptimalICIR_of_isRegular`

References:
* Maschler, Solan, Zamir, *Game Theory*, Section 12.10.
* Nisan, Roughgarden, Tardos, Vazirani, *Algorithmic Game Theory*, Chapter 13.
-/

open scoped BigOperators
open MeasureTheory

namespace BayesianSingleItemAuction

variable {I : Type*}

section VirtualValues

/-! ## Virtual values and regularity -/

/-- Myerson virtual value `v - (1 - F_i(v)) / f_i(v)` for bidder `i`. -/
noncomputable def virtualValue (A : BayesianSingleItemAuction I) (i : I) (v : ℝ) : ℝ :=
  v - (1 - (A.typeData.cdf i).cdf v) / A.typeDensity i v

/-- Virtual value induced by a one-dimensional CDF expression. -/
noncomputable def cdfVirtualValue (cdf : ℝ → ℝ) (v : ℝ) : ℝ :=
  v - (1 - cdf v) / deriv cdf v

/-- Regularity: every bidder's virtual value is monotone. -/
def IsRegular (A : BayesianSingleItemAuction I) : Prop :=
  ∀ i : I, Monotone (A.virtualValue i)

/-- Cross-agent strict order preservation of virtual values.

This is the allocation-level hypothesis used by the common regular-reserve
bridge: whenever one reported value is strictly larger than another, its
virtual value is strictly larger, even across bidders. A common strictly
monotone virtual-value function satisfies this condition. -/
def HasStrictVirtualValueOrder (A : BayesianSingleItemAuction I) : Prop :=
  ∀ ⦃i j : I⦄ ⦃v w : ℝ⦄, v < w → A.virtualValue i v < A.virtualValue j w

/-- Strict virtual-value order implies regularity. -/
theorem HasStrictVirtualValueOrder.isRegular
    {A : BayesianSingleItemAuction I} (hA : A.HasStrictVirtualValueOrder) :
    A.IsRegular := by
  intro i v w hvw
  rcases lt_or_eq_of_le hvw with hlt | rfl
  · exact le_of_lt (hA (i := i) (j := i) hlt)
  · exact le_rfl

/-- A common strictly monotone virtual-value function gives strict virtual-value
order across bidders. -/
theorem hasStrictVirtualValueOrder_of_common_strictMono
    (A : BayesianSingleItemAuction I) {φ : ℝ → ℝ}
    (hcommon : ∀ i v, A.virtualValue i v = φ v)
    (hφ : StrictMono φ) :
    A.HasStrictVirtualValueOrder := by
  intro i j v w hvw
  rw [hcommon i v, hcommon j w]
  exact hφ hvw

/-- Regular virtual values are measurable by Mathlib's measurability theorem for
monotone real functions. -/
theorem measurable_virtualValue_of_isRegular
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) (i : I) :
    Measurable (A.virtualValue i) :=
  (hA i).measurable

/-- A reserve threshold separating nonpositive and nonnegative virtual values. -/
def IsReserveThreshold (A : BayesianSingleItemAuction I) (i : I) (ρ : ℝ) : Prop :=
  (∀ v, v < ρ → A.virtualValue i v ≤ 0) ∧
    ∀ v, ρ ≤ v → 0 ≤ A.virtualValue i v

/-- A cutoff where virtual values cross a comparison value `κ`.

For `κ = 0` this is the usual reserve-threshold predicate. The parameter `κ`
is deliberately abstract: it records a virtual-value comparison level without
fixing a particular economic interpretation. -/
def IsVirtualValueCutoff
    (A : BayesianSingleItemAuction I) (i : I) (κ ρ : ℝ) : Prop :=
  (∀ v, v < ρ → A.virtualValue i v ≤ κ) ∧
    ∀ v, ρ ≤ v → κ ≤ A.virtualValue i v

/-- The virtual-value cutoff `inf {t | κ < φ t}`. -/
noncomputable def virtualValueCutoff (φ : ℝ → ℝ) (κ : ℝ) : ℝ :=
  sInf {t : ℝ | κ < φ t}

/-- The zero virtual-value reserve candidate `inf {t | 0 < φ t}`. -/
noncomputable def positiveVirtualValueCutoff (φ : ℝ → ℝ) : ℝ :=
  virtualValueCutoff φ 0

/-- A continuous virtual value reaches the comparison value at the infimum of a
nonempty bounded-below strict superlevel set. -/
theorem virtualValueCutoff_boundary_eq
    {φ : ℝ → ℝ} {κ : ℝ}
    (hcont : ContinuousAt φ (virtualValueCutoff φ κ))
    (hne : ({t : ℝ | κ < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | κ < φ t}) :
    φ (virtualValueCutoff φ κ) = κ := by
  let S : Set ℝ := {t : ℝ | κ < φ t}
  have hclosure : virtualValueCutoff φ κ ∈ closure S := by
    simpa [virtualValueCutoff, S] using csInf_mem_closure hne hbdd
  refine le_antisymm ?_ ?_
  · by_contra hle
    have hgt : κ < φ (virtualValueCutoff φ κ) := lt_of_not_ge hle
    have hS_nhds : S ∈ nhds (virtualValueCutoff φ κ) := by
      simpa [S] using hcont.preimage_mem_nhds (Ioi_mem_nhds hgt)
    rcases nonempty_nhds_inter_Iio hS_nhds (not_isMin (virtualValueCutoff φ κ)) with
      ⟨y, hyS, hylt⟩
    have hcut_le_y : virtualValueCutoff φ κ ≤ y := by
      simpa [virtualValueCutoff, S] using csInf_le hbdd hyS
    exact (not_lt_of_ge hcut_le_y) hylt
  · by_contra hge
    have hlt : φ (virtualValueCutoff φ κ) < κ := lt_of_not_ge hge
    have hbelow_nhds : {t : ℝ | φ t < κ} ∈ nhds (virtualValueCutoff φ κ) := by
      simpa using hcont.preimage_mem_nhds (Iio_mem_nhds hlt)
    rcases (mem_closure_iff_nhds.mp hclosure _ hbelow_nhds) with ⟨y, hybelow, hyS⟩
    have hygt : κ < φ y := by
      simpa [S] using hyS
    exact (not_lt_of_ge hybelow.le) hygt

/-- Boundary equation for a named cutoff point. -/
theorem virtualValueCutoff_boundary_eq_of_eq
    {φ : ℝ → ℝ} {κ rho : ℝ}
    (hcont : ContinuousAt φ rho)
    (hrho : rho = virtualValueCutoff φ κ)
    (hne : ({t : ℝ | κ < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | κ < φ t}) :
    φ rho = κ := by
  subst rho
  exact virtualValueCutoff_boundary_eq hcont hne hbdd

/-- A reserve specified as the lower cutoff where a virtual value becomes positive.

The boundary equation `φ rho = 0` is stored explicitly. Use
`VirtualValueReserve.of_continuousAt` when it should be derived from continuity
at a nonempty bounded-below cutoff. -/
structure VirtualValueReserve (φ : ℝ → ℝ) (rho : ℝ) : Prop where
  /-- Reserve as the infimum of values with positive virtual value. -/
  reserve_eq_positiveVirtualValueCutoff : rho = positiveVirtualValueCutoff φ
  /-- Boundary zero at the reserve. -/
  reserve_zero : φ rho = 0

/-- A reserve specified as a virtual-value cutoff `φ rho = κ`.

The parameter `κ` is a general comparison level for virtual values. Keeping it
abstract lets reserve-price specializations reuse the same interface without
baking in one application. Use `VirtualValueCutoffReserve.of_continuousAt` when
the boundary equation should be derived from continuity at the cutoff. -/
structure VirtualValueCutoffReserve (φ : ℝ → ℝ) (κ rho : ℝ) : Prop where
  /-- Reserve as the infimum of values whose virtual value beats `κ`. -/
  reserve_eq_virtualValueCutoff : rho = virtualValueCutoff φ κ
  /-- Boundary equation for the virtual-value cutoff. -/
  reserve_eq_cutoff : φ rho = κ

/-- Zero cutoff recovers the positive-virtual-value reserve equation. -/
theorem VirtualValueCutoffReserve.virtualValueReserve_of_zero
    {φ : ℝ → ℝ} {rho : ℝ}
    (h : VirtualValueCutoffReserve φ 0 rho) :
    VirtualValueReserve φ rho := by
  exact
    ⟨by simpa [positiveVirtualValueCutoff] using h.reserve_eq_virtualValueCutoff,
      h.reserve_eq_cutoff⟩

/-- A positive-virtual-value reserve is the zero virtual-value cutoff. -/
theorem VirtualValueReserve.virtualValueCutoffReserve_zero
    {φ : ℝ → ℝ} {rho : ℝ}
    (h : VirtualValueReserve φ rho) :
    VirtualValueCutoffReserve φ 0 rho := by
  exact
    ⟨by simpa [positiveVirtualValueCutoff] using h.reserve_eq_positiveVirtualValueCutoff,
      h.reserve_zero⟩

/-- Build a virtual-value cutoff reserve from continuity at the cutoff. -/
theorem VirtualValueCutoffReserve.of_continuousAt
    {φ : ℝ → ℝ} {κ rho : ℝ}
    (hcont : ContinuousAt φ rho)
    (hrho : rho = virtualValueCutoff φ κ)
    (hne : ({t : ℝ | κ < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | κ < φ t}) :
    VirtualValueCutoffReserve φ κ rho := by
  exact ⟨hrho, virtualValueCutoff_boundary_eq_of_eq hcont hrho hne hbdd⟩

/-- Build a positive-virtual-value reserve from continuity at the zero cutoff. -/
theorem VirtualValueReserve.of_continuousAt
    {φ : ℝ → ℝ} {rho : ℝ}
    (hcont : ContinuousAt φ rho)
    (hrho : rho = positiveVirtualValueCutoff φ)
    (hne : ({t : ℝ | 0 < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | 0 < φ t}) :
    VirtualValueReserve φ rho := by
  refine ⟨hrho, ?_⟩
  exact virtualValueCutoff_boundary_eq_of_eq
    hcont (by simpa [positiveVirtualValueCutoff] using hrho) hne hbdd

/-- The zero cutoff is exactly the reserve-threshold predicate. -/
theorem isReserveThreshold_iff_isVirtualValueCutoff_zero
    (A : BayesianSingleItemAuction I) (i : I) (ρ : ℝ) :
    A.IsReserveThreshold i ρ ↔ A.IsVirtualValueCutoff i 0 ρ :=
  Iff.rfl

/-- Below a virtual-value cutoff, the virtual value is at most the comparison value. -/
theorem virtualValue_le_of_lt_isVirtualValueCutoff
    (A : BayesianSingleItemAuction I) {i : I} {κ ρ v : ℝ}
    (hρ : A.IsVirtualValueCutoff i κ ρ) (hv : v < ρ) :
    A.virtualValue i v ≤ κ :=
  hρ.1 v hv

/-- Above a virtual-value cutoff, the virtual value is at least the comparison value. -/
theorem le_virtualValue_of_isVirtualValueCutoff
    (A : BayesianSingleItemAuction I) {i : I} {κ ρ v : ℝ}
    (hρ : A.IsVirtualValueCutoff i κ ρ) (hv : ρ ≤ v) :
    κ ≤ A.virtualValue i v :=
  hρ.2 v hv

/-- At a reserve threshold, the virtual value is nonnegative. -/
theorem virtualValue_nonneg_of_isReserveThreshold
    (A : BayesianSingleItemAuction I) {i : I} {ρ v : ℝ}
    (hρ : A.IsReserveThreshold i ρ) (hv : ρ ≤ v) :
    0 ≤ A.virtualValue i v :=
  hρ.2 v hv

/-- Below a reserve threshold, the virtual value is nonpositive. -/
theorem virtualValue_nonpos_of_lt_isReserveThreshold
    (A : BayesianSingleItemAuction I) {i : I} {ρ v : ℝ}
    (hρ : A.IsReserveThreshold i ρ) (hv : v < ρ) :
    A.virtualValue i v ≤ 0 :=
  hρ.1 v hv

/-- A zero of a regular virtual value is a reserve threshold. -/
theorem isReserveThreshold_of_isRegular_of_virtualValue_eq_zero
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) {i : I} {ρ : ℝ}
    (hzero : A.virtualValue i ρ = 0) :
    A.IsReserveThreshold i ρ := by
  constructor
  · intro v hv
    simpa [hzero] using hA i hv.le
  · intro v hv
    simpa [hzero] using hA i hv

/-- A crossing of a regular virtual value is a virtual-value cutoff. -/
theorem isVirtualValueCutoff_of_isRegular_of_virtualValue_eq
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) {i : I} {κ ρ : ℝ}
    (hcross : A.virtualValue i ρ = κ) :
    A.IsVirtualValueCutoff i κ ρ := by
  constructor
  · intro v hv
    simpa [hcross] using hA i hv.le
  · intro v hv
    simpa [hcross] using hA i hv

/-- If all bidders share a strictly monotone virtual-value function and `ρ` is
a zero of that common function, then `ρ` is a reserve threshold for every
bidder. -/
theorem isReserveThreshold_common_strictMono_of_common_zero
    (A : BayesianSingleItemAuction I) {φ : ℝ → ℝ} {ρ : ℝ}
    (hcommon : ∀ i v, A.virtualValue i v = φ v)
    (hφ : StrictMono φ)
    (hzero : φ ρ = 0) :
    ∀ i, A.IsReserveThreshold i ρ := by
  intro i
  exact A.isReserveThreshold_of_isRegular_of_virtualValue_eq_zero
    (A.hasStrictVirtualValueOrder_of_common_strictMono hcommon hφ).isRegular
    (by simpa [hcommon i ρ] using hzero)

/-- If all bidders share a strictly monotone virtual-value function and `ρ`
crosses the comparison value `κ`, then `ρ` is the same virtual-value cutoff for
every bidder. -/
theorem isVirtualValueCutoff_common_strictMono_of_common_eq
    (A : BayesianSingleItemAuction I) {φ : ℝ → ℝ} {κ ρ : ℝ}
    (hcommon : ∀ i v, A.virtualValue i v = φ v)
    (hφ : StrictMono φ)
    (hcross : φ ρ = κ) :
    ∀ i, A.IsVirtualValueCutoff i κ ρ := by
  intro i
  exact A.isVirtualValueCutoff_of_isRegular_of_virtualValue_eq
    (A.hasStrictVirtualValueOrder_of_common_strictMono hcommon hφ).isRegular
    (by simpa [hcommon i ρ] using hcross)

/-! ## Common reserve presentations -/

/-!
`CommonRegularReserve` is the minimal reserve interface used by the bridge
theorems. The virtual-value and common-CDF structures below are presentation
wrappers that can be coerced back to this interface.
-/

/-- Minimal common-reserve interface: one strictly increasing virtual value, zero at `rho`. -/
structure CommonRegularReserve (A : BayesianSingleItemAuction I) (rho : ℝ) where
  /-- Common virtual-value function. -/
  phi : ℝ → ℝ
  /-- All bidders share `phi`. -/
  common_virtualValue : ∀ i v, A.virtualValue i v = phi v
  /-- Strict regularity. -/
  strictMono_phi : StrictMono phi
  /-- Reserve zero. -/
  reserve_zero : phi rho = 0

/-- Positive-virtual-value cutoff presentation of a common regular reserve. -/
structure CommonVirtualValueReserve (A : BayesianSingleItemAuction I) (rho : ℝ) where
  /-- Common virtual-value function. -/
  phi : ℝ → ℝ
  /-- All bidders share `phi`. -/
  common_virtualValue : ∀ i v, A.virtualValue i v = phi v
  /-- Strict regularity. -/
  strictMono_phi : StrictMono phi
  /-- Virtual-value reserve equation. -/
  virtualValue_reserve : VirtualValueReserve phi rho

/-- Common comparison-cutoff presentation of a virtual-value reserve. -/
structure CommonVirtualValueCutoffReserve
    (A : BayesianSingleItemAuction I) (κ rho : ℝ) where
  /-- Common virtual-value function. -/
  phi : ℝ → ℝ
  /-- All bidders share `phi`. -/
  common_virtualValue : ∀ i v, A.virtualValue i v = phi v
  /-- Strict regularity. -/
  strictMono_phi : StrictMono phi
  /-- Virtual-value cutoff reserve equation. -/
  cutoff_reserve : VirtualValueCutoffReserve phi κ rho

/-- Forget the cutoff presentation of a common virtual-value reserve, retaining
only the common regular reserve data used by reserve-threshold lemmas. -/
noncomputable def CommonVirtualValueReserve.commonRegularReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonVirtualValueReserve rho) :
    A.CommonRegularReserve rho where
  phi := h.phi
  common_virtualValue := h.common_virtualValue
  strictMono_phi := h.strictMono_phi
  reserve_zero := h.virtualValue_reserve.reserve_zero

/-- View a common virtual-value reserve as the corresponding zero-level
virtual-value cutoff reserve. -/
noncomputable def CommonVirtualValueReserve.commonVirtualValueCutoffReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonVirtualValueReserve rho) :
    A.CommonVirtualValueCutoffReserve 0 rho where
  phi := h.phi
  common_virtualValue := h.common_virtualValue
  strictMono_phi := h.strictMono_phi
  cutoff_reserve := h.virtualValue_reserve.virtualValueCutoffReserve_zero

/-- Build a common virtual-value reserve from continuity at the zero cutoff. -/
noncomputable def CommonVirtualValueReserve.of_continuousAt
    {A : BayesianSingleItemAuction I} {φ : ℝ → ℝ} {rho : ℝ}
    (hcommon : ∀ i v, A.virtualValue i v = φ v)
    (hφ : StrictMono φ)
    (hcont : ContinuousAt φ rho)
    (hrho : rho = positiveVirtualValueCutoff φ)
    (hne : ({t : ℝ | 0 < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | 0 < φ t}) :
    A.CommonVirtualValueReserve rho where
  phi := φ
  common_virtualValue := hcommon
  strictMono_phi := hφ
  virtualValue_reserve := VirtualValueReserve.of_continuousAt hcont hrho hne hbdd

/-- Build a common virtual-value cutoff reserve from continuity at the cutoff. -/
noncomputable def CommonVirtualValueCutoffReserve.of_continuousAt
    {A : BayesianSingleItemAuction I} {φ : ℝ → ℝ} {κ rho : ℝ}
    (hcommon : ∀ i v, A.virtualValue i v = φ v)
    (hφ : StrictMono φ)
    (hcont : ContinuousAt φ rho)
    (hrho : rho = virtualValueCutoff φ κ)
    (hne : ({t : ℝ | κ < φ t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | κ < φ t}) :
    A.CommonVirtualValueCutoffReserve κ rho where
  phi := φ
  common_virtualValue := hcommon
  strictMono_phi := hφ
  cutoff_reserve := VirtualValueCutoffReserve.of_continuousAt hcont hrho hne hbdd

/-- A common strictly monotone virtual value gives strict cross-bidder order preservation. -/
theorem CommonRegularReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) :
    A.HasStrictVirtualValueOrder :=
  A.hasStrictVirtualValueOrder_of_common_strictMono h.common_virtualValue h.strictMono_phi

/-- A common regular reserve implies regularity of every bidder's virtual value. -/
theorem CommonRegularReserve.isRegular
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) :
    A.IsRegular :=
  h.hasStrictVirtualValueOrder.isRegular

/-- A common regular reserve is a reserve threshold for every bidder. -/
theorem CommonRegularReserve.isReserveThreshold
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) :
    ∀ i, A.IsReserveThreshold i rho :=
  A.isReserveThreshold_common_strictMono_of_common_zero
    h.common_virtualValue h.strictMono_phi h.reserve_zero

/-- Above a common regular reserve, each bidder's virtual value is nonnegative. -/
theorem CommonRegularReserve.virtualValue_nonneg_of_reserve_le
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) {i : I} {v : ℝ}
    (hv : rho ≤ v) :
    0 ≤ A.virtualValue i v :=
  A.virtualValue_nonneg_of_isReserveThreshold (h.isReserveThreshold i) hv

/-- At a common regular reserve, each bidder's virtual value is zero. -/
theorem CommonRegularReserve.virtualValue_eq_zero
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) (i : I) :
    A.virtualValue i rho = 0 := by
  rw [h.common_virtualValue i rho, h.reserve_zero]

/-- Strictly above a common regular reserve, each bidder's virtual value is positive. -/
theorem CommonRegularReserve.virtualValue_pos_of_reserve_lt
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) {i : I} {v : ℝ}
    (hv : rho < v) :
    0 < A.virtualValue i v := by
  calc
    0 = h.phi rho := h.reserve_zero.symm
    _ < h.phi v := h.strictMono_phi hv
    _ = A.virtualValue i v := (h.common_virtualValue i v).symm

/-- Below a common regular reserve, each bidder's virtual value is nonpositive. -/
theorem CommonRegularReserve.virtualValue_nonpos_of_lt_reserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonRegularReserve rho) {i : I} {v : ℝ}
    (hv : v < rho) :
    A.virtualValue i v ≤ 0 :=
  A.virtualValue_nonpos_of_lt_isReserveThreshold (h.isReserveThreshold i) hv

/-- Virtual-value reserves give strict cross-bidder virtual-value order. -/
theorem CommonVirtualValueReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonVirtualValueReserve rho) :
    A.HasStrictVirtualValueOrder :=
  h.commonRegularReserve.hasStrictVirtualValueOrder

/-- Virtual-value reserves are regular. -/
theorem CommonVirtualValueReserve.isRegular
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonVirtualValueReserve rho) :
    A.IsRegular :=
  h.hasStrictVirtualValueOrder.isRegular

/-- Virtual-value reserves are reserve thresholds for every bidder. -/
theorem CommonVirtualValueReserve.isReserveThreshold
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonVirtualValueReserve rho) :
    ∀ i, A.IsReserveThreshold i rho :=
  h.commonRegularReserve.isReserveThreshold

/-- Common virtual-value cutoff reserves give strict cross-bidder virtual-value order. -/
theorem CommonVirtualValueCutoffReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonVirtualValueCutoffReserve κ rho) :
    A.HasStrictVirtualValueOrder :=
  A.hasStrictVirtualValueOrder_of_common_strictMono h.common_virtualValue h.strictMono_phi

/-- Common virtual-value cutoff reserves are regular. -/
theorem CommonVirtualValueCutoffReserve.isRegular
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonVirtualValueCutoffReserve κ rho) :
    A.IsRegular :=
  h.hasStrictVirtualValueOrder.isRegular

/-- Common virtual-value cutoff reserves are virtual-value cutoffs for every bidder. -/
theorem CommonVirtualValueCutoffReserve.isVirtualValueCutoff
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonVirtualValueCutoffReserve κ rho) :
    ∀ i, A.IsVirtualValueCutoff i κ rho :=
  A.isVirtualValueCutoff_common_strictMono_of_common_eq
    h.common_virtualValue h.strictMono_phi h.cutoff_reserve.reserve_eq_cutoff

/-- CDF presentation of `CommonRegularReserve`. -/
structure CommonCDFRegularReserve (A : BayesianSingleItemAuction I) (rho : ℝ) where
  /-- Common CDF. -/
  cdf : ℝ → ℝ
  /-- All bidders share `cdf`. -/
  common_cdf : ∀ i, (A.typeData.cdf i).cdf = cdf
  /-- Strictly increasing induced virtual value. -/
  strictMono_virtualValue : StrictMono (cdfVirtualValue cdf)
  /-- Reserve zero. -/
  reserve_zero : cdfVirtualValue cdf rho = 0

/-- CDF presentation using the positive-virtual-value reserve. -/
structure CommonCDFVirtualValueReserve (A : BayesianSingleItemAuction I) (rho : ℝ) where
  /-- Common CDF. -/
  cdf : ℝ → ℝ
  /-- All bidders share `cdf`. -/
  common_cdf : ∀ i, (A.typeData.cdf i).cdf = cdf
  /-- Strictly increasing induced virtual value. -/
  strictMono_virtualValue : StrictMono (cdfVirtualValue cdf)
  /-- Virtual-value reserve equation for the induced virtual value. -/
  virtualValue_reserve : VirtualValueReserve (cdfVirtualValue cdf) rho

/-- CDF presentation using a comparison-value cutoff reserve. -/
structure CommonCDFVirtualValueCutoffReserve
    (A : BayesianSingleItemAuction I) (κ rho : ℝ) where
  /-- Common CDF. -/
  cdf : ℝ → ℝ
  /-- All bidders share `cdf`. -/
  common_cdf : ∀ i, (A.typeData.cdf i).cdf = cdf
  /-- Strictly increasing induced virtual value. -/
  strictMono_virtualValue : StrictMono (cdfVirtualValue cdf)
  /-- Virtual-value cutoff reserve equation for the induced virtual value. -/
  cutoff_reserve : VirtualValueCutoffReserve (cdfVirtualValue cdf) κ rho

/-- Convert a common-CDF regular reserve into the common virtual-value reserve interface. -/
noncomputable def CommonCDFRegularReserve.commonRegularReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFRegularReserve rho) :
    A.CommonRegularReserve rho where
  phi := cdfVirtualValue h.cdf
  common_virtualValue := by
    intro i v
    simp [virtualValue, typeDensity, cdfVirtualValue, h.common_cdf i]
  strictMono_phi := h.strictMono_virtualValue
  reserve_zero := h.reserve_zero

/-- Convert a common-CDF positive-virtual-value reserve into the virtual-value interface. -/
noncomputable def CommonCDFVirtualValueReserve.commonVirtualValueReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.CommonVirtualValueReserve rho where
  phi := cdfVirtualValue h.cdf
  common_virtualValue := by
    intro i v
    simp [virtualValue, typeDensity, cdfVirtualValue, h.common_cdf i]
  strictMono_phi := h.strictMono_virtualValue
  virtualValue_reserve := h.virtualValue_reserve

/-- Forget the cutoff presentation of a common-CDF virtual-value reserve. -/
noncomputable def CommonCDFVirtualValueReserve.commonRegularReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.CommonRegularReserve rho :=
  h.commonVirtualValueReserve.commonRegularReserve

/-- Repackage a common-CDF virtual-value reserve as a common-CDF regular reserve. -/
noncomputable def CommonCDFVirtualValueReserve.commonCDFRegularReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.CommonCDFRegularReserve rho where
  cdf := h.cdf
  common_cdf := h.common_cdf
  strictMono_virtualValue := h.strictMono_virtualValue
  reserve_zero := h.virtualValue_reserve.reserve_zero

/-- Repackage a common-CDF positive-virtual-value reserve as a zero-cutoff reserve. -/
noncomputable def CommonCDFVirtualValueReserve.commonCDFVirtualValueCutoffReserve
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.CommonCDFVirtualValueCutoffReserve 0 rho where
  cdf := h.cdf
  common_cdf := h.common_cdf
  strictMono_virtualValue := h.strictMono_virtualValue
  cutoff_reserve := h.virtualValue_reserve.virtualValueCutoffReserve_zero

/-- Convert a common-CDF cutoff reserve into the virtual-value cutoff interface. -/
noncomputable def CommonCDFVirtualValueCutoffReserve.commonVirtualValueCutoffReserve
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonCDFVirtualValueCutoffReserve κ rho) :
    A.CommonVirtualValueCutoffReserve κ rho where
  phi := cdfVirtualValue h.cdf
  common_virtualValue := by
    intro i v
    simp [virtualValue, typeDensity, cdfVirtualValue, h.common_cdf i]
  strictMono_phi := h.strictMono_virtualValue
  cutoff_reserve := h.cutoff_reserve

/-- Build a common-CDF virtual-value reserve from continuity at the zero cutoff. -/
noncomputable def CommonCDFVirtualValueReserve.of_continuousAt
    {A : BayesianSingleItemAuction I} {cdf : ℝ → ℝ} {rho : ℝ}
    (hcommon : ∀ i, (A.typeData.cdf i).cdf = cdf)
    (hψ : StrictMono (cdfVirtualValue cdf))
    (hcont : ContinuousAt (cdfVirtualValue cdf) rho)
    (hrho : rho = positiveVirtualValueCutoff (cdfVirtualValue cdf))
    (hne : ({t : ℝ | 0 < cdfVirtualValue cdf t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | 0 < cdfVirtualValue cdf t}) :
    A.CommonCDFVirtualValueReserve rho where
  cdf := cdf
  common_cdf := hcommon
  strictMono_virtualValue := hψ
  virtualValue_reserve := VirtualValueReserve.of_continuousAt hcont hrho hne hbdd

/-- Build a common-CDF virtual-value cutoff reserve from continuity at the cutoff. -/
noncomputable def CommonCDFVirtualValueCutoffReserve.of_continuousAt
    {A : BayesianSingleItemAuction I} {cdf : ℝ → ℝ} {κ rho : ℝ}
    (hcommon : ∀ i, (A.typeData.cdf i).cdf = cdf)
    (hψ : StrictMono (cdfVirtualValue cdf))
    (hcont : ContinuousAt (cdfVirtualValue cdf) rho)
    (hrho : rho = virtualValueCutoff (cdfVirtualValue cdf) κ)
    (hne : ({t : ℝ | κ < cdfVirtualValue cdf t}).Nonempty)
    (hbdd : BddBelow {t : ℝ | κ < cdfVirtualValue cdf t}) :
    A.CommonCDFVirtualValueCutoffReserve κ rho where
  cdf := cdf
  common_cdf := hcommon
  strictMono_virtualValue := hψ
  cutoff_reserve := VirtualValueCutoffReserve.of_continuousAt hcont hrho hne hbdd

/-- A common-CDF regular reserve gives strict cross-bidder virtual-value order. -/
theorem CommonCDFRegularReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFRegularReserve rho) :
    A.HasStrictVirtualValueOrder :=
  h.commonRegularReserve.hasStrictVirtualValueOrder

/-- A common-CDF regular reserve implies regularity. -/
theorem CommonCDFRegularReserve.isRegular
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFRegularReserve rho) :
    A.IsRegular :=
  h.commonRegularReserve.isRegular

/-- A common-CDF regular reserve is a reserve threshold for every bidder. -/
theorem CommonCDFRegularReserve.isReserveThreshold
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFRegularReserve rho) :
    ∀ i, A.IsReserveThreshold i rho :=
  h.commonRegularReserve.isReserveThreshold

/-- Common-CDF virtual-value reserves give strict cross-bidder virtual-value order. -/
theorem CommonCDFVirtualValueReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.HasStrictVirtualValueOrder :=
  h.commonRegularReserve.hasStrictVirtualValueOrder

/-- Common-CDF virtual-value reserves are regular. -/
theorem CommonCDFVirtualValueReserve.isRegular
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    A.IsRegular :=
  h.hasStrictVirtualValueOrder.isRegular

/-- Common-CDF virtual-value reserves are reserve thresholds for every bidder. -/
theorem CommonCDFVirtualValueReserve.isReserveThreshold
    {A : BayesianSingleItemAuction I} {rho : ℝ}
    (h : A.CommonCDFVirtualValueReserve rho) :
    ∀ i, A.IsReserveThreshold i rho :=
  h.commonRegularReserve.isReserveThreshold

/-- Common-CDF virtual-value cutoff reserves give strict cross-bidder virtual-value order. -/
theorem CommonCDFVirtualValueCutoffReserve.hasStrictVirtualValueOrder
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonCDFVirtualValueCutoffReserve κ rho) :
    A.HasStrictVirtualValueOrder :=
  h.commonVirtualValueCutoffReserve.hasStrictVirtualValueOrder

/-- Common-CDF virtual-value cutoff reserves are regular. -/
theorem CommonCDFVirtualValueCutoffReserve.isRegular
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonCDFVirtualValueCutoffReserve κ rho) :
    A.IsRegular :=
  h.hasStrictVirtualValueOrder.isRegular

/-- Common-CDF virtual-value cutoff reserves are virtual-value cutoffs for every bidder. -/
theorem CommonCDFVirtualValueCutoffReserve.isVirtualValueCutoff
    {A : BayesianSingleItemAuction I} {κ rho : ℝ}
    (h : A.CommonCDFVirtualValueCutoffReserve κ rho) :
    ∀ i, A.IsVirtualValueCutoff i κ rho :=
  h.commonVirtualValueCutoffReserve.isVirtualValueCutoff

end VirtualValues

section VirtualSurplusMaximizingMechanism

/-- Virtual surplus of an allocation rule at a reported type profile. -/
noncomputable def virtualSurplus [Fintype I]
    (A : BayesianSingleItemAuction I) (x : (I → ℝ) → I → ℝ) (b : I → ℝ) : ℝ :=
  ∑ i, x b i * A.virtualValue i (b i)

/-- Ex-ante expected virtual surplus under the auction prior. -/
noncomputable def expectedVirtualSurplus [Fintype I]
    (A : BayesianSingleItemAuction I) (x : (I → ℝ) → I → ℝ) : ℝ :=
  ∫ t, A.virtualSurplus x t ∂A.prior

/-- Integrability condition for ex-ante virtual surplus under the auction prior. -/
def IntegrableVirtualSurplus [Fintype I]
    (A : BayesianSingleItemAuction I) (x : (I → ℝ) → I → ℝ) : Prop :=
  Integrable (fun t => A.virtualSurplus x t) A.prior

/-- Pointwise virtual-surplus dominance lifts to ex-ante dominance. -/
theorem expectedVirtualSurplus_le_of_forall_virtualSurplus_le [Fintype I]
    (A : BayesianSingleItemAuction I) {x y : (I → ℝ) → I → ℝ}
    (hx_int : A.IntegrableVirtualSurplus x)
    (hy_int : A.IntegrableVirtualSurplus y)
    (hxy : ∀ t, A.virtualSurplus x t ≤ A.virtualSurplus y t) :
    A.expectedVirtualSurplus x ≤ A.expectedVirtualSurplus y :=
  integral_mono hx_int hy_int hxy

/-- A nonnegative fractional allocation rule with total mass at most `1`. -/
def IsSingleItemAllocationRule [Fintype I]
    (x : (I → ℝ) → I → ℝ) : Prop :=
  (∀ b i, 0 ≤ x b i) ∧ ∀ b, (∑ i, x b i) ≤ 1

/-- A feasible single-item allocation gives each bidder probability at most `1`. -/
theorem IsSingleItemAllocationRule.le_one
    [Fintype I] [DecidableEq I] {x : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x) (b : I → ℝ) (i : I) :
    x b i ≤ 1 := by
  have hle_sum : x b i ≤ ∑ j, x b j := by
    exact Finset.single_le_sum (fun j _ => hx.1 b j) (Finset.mem_univ i)
  exact le_trans hle_sum (hx.2 b)

/-- A feasible single-item allocation rule satisfies `IsAllocFeasible` with any payment rule. -/
theorem withPayment_isAllocFeasible_of_isSingleItemAllocationRule
    [Fintype I] [DecidableEq I] {x p : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x) :
    ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsAllocFeasible := by
  intro b i
  exact ⟨hx.1 b i, hx.le_one b i⟩

/-- Feasible allocation rules that pointwise maximize virtual surplus. -/
def IsVirtualSurplusOptimalAllocationRule [Fintype I]
    (A : BayesianSingleItemAuction I) (x : (I → ℝ) → I → ℝ) : Prop :=
  IsSingleItemAllocationRule x ∧
    ∀ y, IsSingleItemAllocationRule y →
      ∀ b, A.virtualSurplus y b ≤ A.virtualSurplus x b

/-! ## Deterministic virtual-surplus maximization -/

/-- Lexicographic score used to break ties among virtual values. -/
noncomputable def virtualScore [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) : ℝ ×ₗ I :=
  toLex (A.virtualValue i (b i), i)

/-- The virtual-value winner with deterministic tie-breaking. -/
noncomputable def virtualSurplusMaximizingWinner
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) : I :=
  (Auction.BidProfile.ofFunction (A.virtualScore b)).argmaxBid

/-- The selected winner is exactly the bidder whose lexicographic virtual score
dominates every other bidder's score. -/
theorem virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingWinner b = i ↔
      ∀ j, A.virtualScore b j ≤ A.virtualScore b i := by
  constructor
  · intro hwinner j
    have hle :
        A.virtualScore b j ≤
          A.virtualScore b (A.virtualSurplusMaximizingWinner b) := by
      simpa [virtualSurplusMaximizingWinner] using
        Auction.bid_le_maxBid (A.virtualScore b) j
    simpa [hwinner] using hle
  · intro hmax
    let w := A.virtualSurplusMaximizingWinner b
    have hwi : A.virtualScore b w ≤ A.virtualScore b i := hmax w
    have hiw : A.virtualScore b i ≤ A.virtualScore b w := by
      simpa [w, virtualSurplusMaximizingWinner] using
        Auction.bid_le_maxBid (A.virtualScore b) i
    have hscore : A.virtualScore b w = A.virtualScore b i := le_antisymm hwi hiw
    have hpair :
        (A.virtualValue w (b w), w) = (A.virtualValue i (b i), i) := by
      apply toLex_inj.mp
      simpa [w, virtualScore] using hscore
    exact congrArg Prod.snd hpair

/-- The virtual value attained by the selected virtual-value winner. -/
noncomputable def winningVirtualValue
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) : ℝ :=
  A.virtualValue (A.virtualSurplusMaximizingWinner b)
    (b (A.virtualSurplusMaximizingWinner b))

/-- Allocates to the highest positive virtual value, otherwise withholds the item. -/
noncomputable def virtualSurplusMaximizingAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) : (I → ℝ) → I → ℝ :=
  fun b i =>
    let w := A.virtualSurplusMaximizingWinner b
    if 0 < A.winningVirtualValue b then
      if i = w then 1 else 0
    else
      0

/-- Myerson payment for `virtualSurplusMaximizingAllocationRule`. -/
noncomputable def virtualSurplusMaximizingPaymentRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) : (I → ℝ) → I → ℝ :=
  SingleParameterMechanism.myersonPayment A.virtualSurplusMaximizingAllocationRule

/-- The virtual-surplus allocation rule paired with its Myerson payment. -/
noncomputable def virtualSurplusMaximizingMechanism
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) : SingleParameterAuction I ℝ where
  allocationRule := A.virtualSurplusMaximizingAllocationRule
  paymentRule := A.virtualSurplusMaximizingPaymentRule

/-- The Bayesian auction using the virtual-surplus mechanism and the original priors. -/
noncomputable def virtualSurplusMaximizingAuction
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) : BayesianSingleItemAuction I where
  allocationRule := (A.virtualSurplusMaximizingMechanism).allocationRule
  paymentRule := (A.virtualSurplusMaximizingMechanism).paymentRule
  prior := A.prior
  prob_prior := A.prob_prior
  opponentPrior := A.opponentPrior
  prob_opponentPrior := A.prob_opponentPrior
  typeData := A.typeData

/-- The constructed mechanism uses the virtual-surplus-maximizing allocation rule. -/
@[simp] theorem virtualSurplusMaximizingMechanism_allocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingMechanism).allocationRule =
      A.virtualSurplusMaximizingAllocationRule := by
  rfl

/-- The constructed mechanism uses the Myerson payment rule for the virtual-surplus allocation. -/
@[simp] theorem virtualSurplusMaximizingMechanism_paymentRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingMechanism).paymentRule =
      A.virtualSurplusMaximizingPaymentRule := by
  rfl

/-- The lifted Bayesian auction keeps the virtual-surplus-maximizing allocation rule. -/
@[simp] theorem virtualSurplusMaximizingAuction_allocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).allocationRule =
      A.virtualSurplusMaximizingAllocationRule := by
  rfl

/-- The lifted Bayesian auction keeps the Myerson payment rule. -/
@[simp] theorem virtualSurplusMaximizingAuction_paymentRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).paymentRule =
      A.virtualSurplusMaximizingPaymentRule := by
  rfl

/-- The lifted virtual-surplus auction preserves the original prior. -/
@[simp] theorem virtualSurplusMaximizingAuction_prior
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).prior = A.prior := by
  rfl

/-- The lifted virtual-surplus auction preserves the original opponent priors. -/
@[simp] theorem virtualSurplusMaximizingAuction_opponentPrior
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).opponentPrior = A.opponentPrior := by
  rfl

/-- The lifted virtual-surplus auction preserves the original continuous type data. -/
@[simp] theorem virtualSurplusMaximizingAuction_typeData
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).typeData = A.typeData := by
  rfl

/-- Forgetting the lifted auction to a single-parameter auction recovers the
virtual-surplus-maximizing auction-layer mechanism. -/
@[simp] theorem virtualSurplusMaximizingAuction_toSingleParameterAuction
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).toSingleParameterAuction =
      A.virtualSurplusMaximizingMechanism := by
  rfl

/-- Forgetting the lifted auction further to a single-parameter mechanism
recovers the underlying virtual-surplus-maximizing mechanism. -/
@[simp] theorem virtualSurplusMaximizingAuction_toSingleParameterMechanism
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).toSingleParameterMechanism =
      (A.virtualSurplusMaximizingMechanism).toSingleParameterMechanism := by
  rfl

/-- Forgetting the lifted auction to a direct Bayesian mechanism preserves the
same prior, allocation, and payment fields. -/
@[simp] theorem virtualSurplusMaximizingAuction_toDirectBayesianMechanismWithTransfers
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).toDirectBayesianMechanismWithTransfers =
      ({ prior := A.prior
         prob_prior := A.prob_prior
         allocationRule := (A.virtualSurplusMaximizingMechanism).allocationRule
         paymentRule := (A.virtualSurplusMaximizingMechanism).paymentRule } :
        DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ) := by
  rfl

end VirtualSurplusMaximizingMechanism

section VirtualSurplusMaximality

/-! ## Allocation-rule facts and virtual-surplus maximality -/

private lemma virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hpos : 0 < A.winningVirtualValue b) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if i = A.virtualSurplusMaximizingWinner b then (1 : ℝ) else 0 := by
  funext i
  simp [virtualSurplusMaximizingAllocationRule, hpos]

private lemma virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hnotpos : ¬ 0 < A.winningVirtualValue b) :
    A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) := by
  funext i
  simp [virtualSurplusMaximizingAllocationRule, hnotpos]

private lemma virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I}
    (hwinner : A.virtualSurplusMaximizingWinner b = i)
    (hpos : 0 < A.winningVirtualValue b) :
    A.virtualSurplusMaximizingAllocationRule b i = 1 := by
  simp [virtualSurplusMaximizingAllocationRule, hpos, hwinner]

private lemma virtualSurplusMaximizingAllocationRule_eq_zero_of_ne_winner
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I}
    (hi : i ≠ A.virtualSurplusMaximizingWinner b) :
    A.virtualSurplusMaximizingAllocationRule b i = 0 := by
  by_cases hpos : 0 < A.winningVirtualValue b
  · simp [virtualSurplusMaximizingAllocationRule, hpos, hi]
  · simp [virtualSurplusMaximizingAllocationRule, hpos]

/-- The selected winner has maximal virtual value. -/
theorem virtualSurplusMaximizingWinner_virtualValue_ge
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualValue i (b i) ≤ A.winningVirtualValue b := by
  have hscore :
      A.virtualScore b i ≤ A.virtualScore b (A.virtualSurplusMaximizingWinner b) := by
    simpa [virtualSurplusMaximizingWinner] using Auction.bid_le_maxBid (A.virtualScore b) i
  rw [virtualScore, virtualScore, Prod.Lex.toLex_le_toLex] at hscore
  rcases hscore with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq

private lemma virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_of_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hpos : 0 < A.winningVirtualValue b) :
    A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b = A.winningVirtualValue b := by
  rw [virtualSurplus, A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos b hpos]
  simp [winningVirtualValue, Finset.sum_ite_eq', Finset.mem_univ]

private lemma virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hnotpos : ¬ 0 < A.winningVirtualValue b) :
    A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b = 0 := by
  rw [virtualSurplus, A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hnotpos]
  simp

private lemma virtualSurplus_le_totalAllocation_mul_winningVirtualValue
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ} {b : I → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x b i) :
    A.virtualSurplus x b ≤ (∑ i, x b i) * A.winningVirtualValue b := by
  have hterm :
      ∀ i, x b i * A.virtualValue i (b i) ≤ x b i * A.winningVirtualValue b := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (A.virtualSurplusMaximizingWinner_virtualValue_ge b i)
      (hx_nonneg i)
  calc
    A.virtualSurplus x b = ∑ i, x b i * A.virtualValue i (b i) := rfl
    _ ≤ ∑ i, x b i * A.winningVirtualValue b :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, x b i) * A.winningVirtualValue b := by
      rw [← Finset.sum_mul]

private lemma virtualSurplus_le_winningVirtualValue
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ} {b : I → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x b i)
    (hx_capacity : (∑ i, x b i) ≤ 1)
    (hwin_nonneg : 0 ≤ A.winningVirtualValue b) :
    A.virtualSurplus x b ≤ A.winningVirtualValue b := by
  calc
    A.virtualSurplus x b ≤ (∑ i, x b i) * A.winningVirtualValue b :=
      A.virtualSurplus_le_totalAllocation_mul_winningVirtualValue hx_nonneg
    _ ≤ 1 * A.winningVirtualValue b :=
      mul_le_mul_of_nonneg_right hx_capacity hwin_nonneg
    _ = A.winningVirtualValue b := by ring

private lemma virtualSurplus_nonpos_of_winningVirtualValue_nonpos
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ} {b : I → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x b i)
    (hwin_nonpos : A.winningVirtualValue b ≤ 0) :
    A.virtualSurplus x b ≤ 0 := by
  have hsum_nonneg : 0 ≤ ∑ i, x b i := Finset.sum_nonneg fun i _ => hx_nonneg i
  calc
    A.virtualSurplus x b ≤ (∑ i, x b i) * A.winningVirtualValue b :=
      A.virtualSurplus_le_totalAllocation_mul_winningVirtualValue hx_nonneg
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsum_nonneg hwin_nonpos

/-- Pointwise virtual-surplus maximality. -/
theorem virtualSurplus_le_virtualSurplusMaximizingAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ} {b : I → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x b i)
    (hx_capacity : (∑ i, x b i) ≤ 1) :
    A.virtualSurplus x b ≤
    A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b := by
  by_cases hpos : 0 < A.winningVirtualValue b
  · have hle := A.virtualSurplus_le_winningVirtualValue hx_nonneg hx_capacity (le_of_lt hpos)
    simpa [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_of_pos b hpos] using hle
  · have hle := A.virtualSurplus_nonpos_of_winningVirtualValue_nonpos hx_nonneg (le_of_not_gt hpos)
    simpa [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos]
      using hle

end VirtualSurplusMaximality

section ReserveInterpretation

/-! ## Reserve-price interpretation of the allocation rule -/

/-- If the winning virtual value is positive, allocate to the selected winner. -/
theorem virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hpos : 0 < A.winningVirtualValue b) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if i = A.virtualSurplusMaximizingWinner b then (1 : ℝ) else 0 :=
  A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos b hpos

/-- If the winning virtual value is positive, the selected winner receives `1`. -/
theorem virtualSurplusMaximizingAllocationRule_winner_eq_one_of_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ)
    (hpos : 0 < A.winningVirtualValue b) :
    A.virtualSurplusMaximizingAllocationRule b (A.virtualSurplusMaximizingWinner b) = 1 :=
  A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos rfl hpos

/-- The winning virtual value is positive iff some virtual value is positive. -/
theorem winningVirtualValue_pos_iff_exists_virtualValue_pos
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    0 < A.winningVirtualValue b ↔ ∃ i, 0 < A.virtualValue i (b i) := by
  constructor
  · intro hpos
    exact ⟨A.virtualSurplusMaximizingWinner b, by simpa [winningVirtualValue] using hpos⟩
  · rintro ⟨i, hi⟩
    exact lt_of_lt_of_le hi (A.virtualSurplusMaximizingWinner_virtualValue_ge b i)

/-- The winning virtual value is nonpositive iff all virtual values are. -/
theorem winningVirtualValue_nonpos_iff_forall_virtualValue_nonpos
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    A.winningVirtualValue b ≤ 0 ↔ ∀ i, A.virtualValue i (b i) ≤ 0 := by
  constructor
  · intro hwin i
    exact le_trans (A.virtualSurplusMaximizingWinner_virtualValue_ge b i) hwin
  · intro h
    simpa [winningVirtualValue] using h (A.virtualSurplusMaximizingWinner b)

/-- Allocation probability `1` characterizes the positive virtual-value winner. -/
theorem virtualSurplusMaximizingAllocationRule_eq_one_iff
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingAllocationRule b i = 1 ↔
      0 < A.winningVirtualValue b ∧ i = A.virtualSurplusMaximizingWinner b := by
  constructor
  · intro hi
    by_cases hpos : 0 < A.winningVirtualValue b
    · refine ⟨hpos, ?_⟩
      by_contra hne
      have hzero : A.virtualSurplusMaximizingAllocationRule b i = 0 :=
        A.virtualSurplusMaximizingAllocationRule_eq_zero_of_ne_winner hne
      exact zero_ne_one (hzero.symm.trans hi)
    · have hzero : A.virtualSurplusMaximizingAllocationRule b i = 0 := by
        simpa using
          congr_fun (A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos) i
      exact False.elim (zero_ne_one (by rw [← hzero, hi]))
  · rintro ⟨hpos, hi⟩
    exact A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos
      hi.symm hpos

/-- A bidder allocated probability `1` has positive virtual value. -/
theorem virtualValue_pos_of_virtualSurplusMaximizingAllocationRule_eq_one
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I}
    (hi : A.virtualSurplusMaximizingAllocationRule b i = 1) :
    0 < A.virtualValue i (b i) := by
  rcases (A.virtualSurplusMaximizingAllocationRule_eq_one_iff b i).mp hi with
    ⟨hpos, hi_winner⟩
  simpa [winningVirtualValue, hi_winner] using hpos

/-- An allocated bidder reports at least her reserve threshold. -/
theorem reserveThreshold_le_bid_of_virtualSurplusMaximizingAllocationRule_eq_one
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I} {ρ : ℝ}
    (hρ : A.IsReserveThreshold i ρ)
    (hi : A.virtualSurplusMaximizingAllocationRule b i = 1) :
    ρ ≤ b i := by
  by_contra hnot
  have hlt : b i < ρ := lt_of_not_ge hnot
  have hvirt_pos : 0 < A.virtualValue i (b i) :=
    A.virtualValue_pos_of_virtualSurplusMaximizingAllocationRule_eq_one hi
  exact (not_le_of_gt hvirt_pos) (A.virtualValue_nonpos_of_lt_isReserveThreshold hρ hlt)

/-- A sale occurs exactly when some bidder has positive virtual value. -/
theorem exists_virtualSurplusMaximizingAllocationRule_eq_one_iff_exists_virtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    (∃ i, A.virtualSurplusMaximizingAllocationRule b i = 1) ↔
      ∃ i, 0 < A.virtualValue i (b i) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, A.virtualValue_pos_of_virtualSurplusMaximizingAllocationRule_eq_one hi⟩
  · intro hpos_exists
    have hpos : 0 < A.winningVirtualValue b :=
      (A.winningVirtualValue_pos_iff_exists_virtualValue_pos b).2 hpos_exists
    exact ⟨A.virtualSurplusMaximizingWinner b,
      A.virtualSurplusMaximizingAllocationRule_winner_eq_one_of_winningVirtualValue_pos b hpos⟩

/-- A sale occurs exactly when the selected virtual value is positive. -/
theorem exists_virtualSurplusMaximizingAllocationRule_eq_one_iff_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    (∃ i, A.virtualSurplusMaximizingAllocationRule b i = 1) ↔
      0 < A.winningVirtualValue b := by
  rw [A.exists_virtualSurplusMaximizingAllocationRule_eq_one_iff_exists_virtualValue_pos,
    A.winningVirtualValue_pos_iff_exists_virtualValue_pos]

/-- If a sale occurs, some bidder reaches her reserve threshold. -/
theorem exists_reserveThreshold_le_bid_of_exists_virtualSurplusMaximizingAllocationRule_eq_one
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hsale : ∃ i, A.virtualSurplusMaximizingAllocationRule b i = 1) :
    ∃ i, ρ i ≤ b i := by
  rcases hsale with ⟨i, hi⟩
  exact ⟨i, A.reserveThreshold_le_bid_of_virtualSurplusMaximizingAllocationRule_eq_one
    (hρ i) hi⟩

/-- A positive virtual-value winner reaches her reserve threshold. -/
theorem reserveThreshold_le_winner_bid_of_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hpos : 0 < A.winningVirtualValue b) :
    ρ (A.virtualSurplusMaximizingWinner b) ≤ b (A.virtualSurplusMaximizingWinner b) :=
  A.reserveThreshold_le_bid_of_virtualSurplusMaximizingAllocationRule_eq_one
    (hρ (A.virtualSurplusMaximizingWinner b))
    (A.virtualSurplusMaximizingAllocationRule_winner_eq_one_of_winningVirtualValue_pos b hpos)

/-- Positive winning virtual value implies some report reaches reserve. -/
theorem exists_reserveThreshold_le_bid_of_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hpos : 0 < A.winningVirtualValue b) :
    ∃ i, ρ i ≤ b i :=
  ⟨A.virtualSurplusMaximizingWinner b,
    A.reserveThreshold_le_winner_bid_of_winningVirtualValue_pos hρ hpos⟩

/-- If all reports are below reserve, the winning virtual value is nonpositive. -/
theorem winningVirtualValue_nonpos_of_forall_lt_reserveThreshold
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hb : ∀ i, b i < ρ i) :
    A.winningVirtualValue b ≤ 0 :=
  (A.winningVirtualValue_nonpos_iff_forall_virtualValue_nonpos b).mpr
    fun i => A.virtualValue_nonpos_of_lt_isReserveThreshold (hρ i) (hb i)

/-- Positive winning virtual value rules out all reports below reserve. -/
theorem not_forall_lt_reserveThreshold_of_winningVirtualValue_pos
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hpos : 0 < A.winningVirtualValue b) :
    ¬ ∀ i, b i < ρ i := by
  intro hb
  exact not_le_of_gt hpos (A.winningVirtualValue_nonpos_of_forall_lt_reserveThreshold hρ hb)

/-- If all virtual values are nonpositive, withhold the item. -/
theorem virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ}
    (hnonpos : ∀ i, A.virtualValue i (b i) ≤ 0) :
    A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) := by
  have hwin_nonpos : A.winningVirtualValue b ≤ 0 := by
    simpa [winningVirtualValue] using hnonpos (A.virtualSurplusMaximizingWinner b)
  exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b
    (not_lt_of_ge hwin_nonpos)

/-- If all reports are below reserve thresholds, withhold the item. -/
theorem virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_lt_reserveThreshold
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {ρ b : I → ℝ}
    (hρ : ∀ i, A.IsReserveThreshold i (ρ i))
    (hb : ∀ i, b i < ρ i) :
    A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) :=
  A.virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos
    fun i => A.virtualValue_nonpos_of_lt_isReserveThreshold (hρ i) (hb i)

/-- If virtual values strictly preserve report order across bidders, the
virtual-surplus winner agrees with the unique highest bid. -/
theorem virtualSurplusMaximizingWinner_eq_argmaxBid_of_strictVirtualValueOrder
    [Fintype I] [Nontrivial I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder) {b : I → ℝ}
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingWinner b = Auction.argmaxBid b := by
  refine (A.virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le
    b (Auction.argmaxBid b)).2 ?_
  intro j
  by_cases hj : j = Auction.argmaxBid b
  · simp [hj]
  · have hvirt :
        A.virtualValue j (b j) <
          A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) :=
      hA (i := j) (j := Auction.argmaxBid b) (hstrict j hj)
    exact le_of_lt (by
      rw [virtualScore, virtualScore, Prod.Lex.toLex_lt_toLex]
      exact Or.inl hvirt)

/-- Allocation-level reserve bridge: with a common reserve and a unique highest
bid strictly above it, the Myerson allocation is the highest-bid indicator.

This is the allocation part of the usual common regular-reserve connection with
reserve second-price auctions; the payment equality is a separate
analytic/algebraic problem. -/
theorem virtualSurplusMaximizingAllocationRule_eq_argmaxBidIndicator_of_commonReserve_lt_argmaxBid
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.HasStrictVirtualValueOrder)
    {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hstrict : ∀ j, j ≠ Auction.argmaxBid b → b j < b (Auction.argmaxBid b))
    (hb : rho < b (Auction.argmaxBid b)) :
    A.virtualSurplusMaximizingAllocationRule b =
      fun i => if i = Auction.argmaxBid b then (1 : ℝ) else 0 := by
  have hwin :
      A.virtualSurplusMaximizingWinner b = Auction.argmaxBid b :=
    A.virtualSurplusMaximizingWinner_eq_argmaxBid_of_strictVirtualValueOrder hA hstrict
  have hargmax_pos : 0 < A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) := by
    have hnonneg : 0 ≤ A.virtualValue (Auction.argmaxBid b) rho :=
      A.virtualValue_nonneg_of_isReserveThreshold (hrho (Auction.argmaxBid b)) le_rfl
    have hlt :
        A.virtualValue (Auction.argmaxBid b) rho <
          A.virtualValue (Auction.argmaxBid b) (b (Auction.argmaxBid b)) :=
      hA (i := Auction.argmaxBid b) (j := Auction.argmaxBid b) hb
    exact lt_of_le_of_lt hnonneg hlt
  have hpos : 0 < A.winningVirtualValue b := by
    simpa [winningVirtualValue, hwin] using hargmax_pos
  simpa [hwin] using
    A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_winningVirtualValue_pos b hpos

/-- If the highest bid is strictly below a common reserve threshold, the Myerson
allocation withholds the item. -/
theorem virtualSurplusMaximizingAllocationRule_eq_zero_of_argmaxBid_lt_commonReserve
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {rho : ℝ} {b : I → ℝ}
    (hrho : ∀ i, A.IsReserveThreshold i rho)
    (hb : b (Auction.argmaxBid b) < rho) :
    A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ) := by
  have hbelow : ∀ i, b i < rho := by
    intro i
    exact lt_of_le_of_lt (Auction.bid_le_maxBid b i) hb
  exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos
    fun i => A.virtualValue_nonpos_of_lt_isReserveThreshold (hrho i) (hbelow i)

/-- Withholding is equivalent to all virtual values being nonpositive. -/
theorem virtualSurplusMaximizingAllocationRule_eq_zero_iff_forall_virtualValue_nonpos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} :
    (A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ)) ↔
      ∀ i, A.virtualValue i (b i) ≤ 0 := by
  constructor
  · intro hzero
    apply (A.winningVirtualValue_nonpos_iff_forall_virtualValue_nonpos b).mp
    by_contra hnot
    have hpos : 0 < A.winningVirtualValue b := lt_of_not_ge hnot
    have hone :
        A.virtualSurplusMaximizingAllocationRule b (A.virtualSurplusMaximizingWinner b) = 1 :=
      A.virtualSurplusMaximizingAllocationRule_winner_eq_one_of_winningVirtualValue_pos b hpos
    have hzero_at :
        A.virtualSurplusMaximizingAllocationRule b (A.virtualSurplusMaximizingWinner b) = 0 := by
      simpa using congr_fun hzero (A.virtualSurplusMaximizingWinner b)
    exact one_ne_zero (hone.symm.trans hzero_at)
  · exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_forall_virtualValue_nonpos

/-- Withholding is equivalent to nonpositive winning virtual value. -/
theorem virtualSurplusMaximizingAllocationRule_eq_zero_iff_winningVirtualValue_nonpos
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} :
    (A.virtualSurplusMaximizingAllocationRule b = fun _ => (0 : ℝ)) ↔
      A.winningVirtualValue b ≤ 0 := by
  constructor
  · intro hzero
    exact (A.winningVirtualValue_nonpos_iff_forall_virtualValue_nonpos b).mpr
      (A.virtualSurplusMaximizingAllocationRule_eq_zero_iff_forall_virtualValue_nonpos.mp hzero)
  · intro hwin
    exact A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b (not_lt_of_ge hwin)

/-- The constructed virtual surplus is the positive part of the winning virtual value. -/
theorem virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_max_winningVirtualValue_zero
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    A.virtualSurplus A.virtualSurplusMaximizingAllocationRule b =
      max (A.winningVirtualValue b) 0 := by
  by_cases hpos : 0 < A.winningVirtualValue b
  · have hnonneg : 0 ≤ A.winningVirtualValue b := le_of_lt hpos
    rw [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_of_pos b hpos,
      max_eq_left hnonneg]
  · have hnonpos : A.winningVirtualValue b ≤ 0 := le_of_not_gt hpos
    rw [A.virtualSurplus_virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos,
      max_eq_right hnonpos]

end ReserveInterpretation

section Feasibility

/-! ## Feasibility -/

/-- The virtual-surplus-maximizing allocation assigns nonnegative probabilities. -/
lemma virtualSurplusMaximizingAllocationRule_nonneg
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    0 ≤ A.virtualSurplusMaximizingAllocationRule b i := by
  classical
  by_cases hpos : 0 < A.winningVirtualValue b
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos b hpos]
    by_cases hi : i = A.virtualSurplusMaximizingWinner b <;> simp [hi]
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos]

/-- The virtual-surplus-maximizing allocation assigns probabilities at most one. -/
lemma virtualSurplusMaximizingAllocationRule_le_one
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingAllocationRule b i ≤ 1 := by
  classical
  by_cases hpos : 0 < A.winningVirtualValue b
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos b hpos]
    by_cases hi : i = A.virtualSurplusMaximizingWinner b <;> simp [hi]
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos]
    simp

/-- The virtual-surplus-maximizing allocation allocates to at most one bidder. -/
lemma virtualSurplusMaximizingAllocationRule_respectsSingleItemCapacity
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) :
    (∑ i, A.virtualSurplusMaximizingAllocationRule b i) ≤ 1 := by
  classical
  by_cases hpos : 0 < A.winningVirtualValue b
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_winnerIndicator_of_pos b hpos]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  · rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos]
    simp

/-- The virtual-surplus-maximizing allocation rule is feasible. -/
theorem virtualSurplusMaximizingAllocationRule_isSingleItemAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    IsSingleItemAllocationRule A.virtualSurplusMaximizingAllocationRule := by
  exact ⟨fun b i => A.virtualSurplusMaximizingAllocationRule_nonneg b i,
    fun b => A.virtualSurplusMaximizingAllocationRule_respectsSingleItemCapacity b⟩

/-- The virtual-surplus-maximizing mechanism is allocation-feasible. -/
theorem virtualSurplusMaximizingMechanism_isAllocFeasible
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingMechanism).IsAllocFeasible := by
  simpa [virtualSurplusMaximizingMechanism] using
    withPayment_isAllocFeasible_of_isSingleItemAllocationRule
      (p := A.virtualSurplusMaximizingPaymentRule)
      A.virtualSurplusMaximizingAllocationRule_isSingleItemAllocationRule

/-- The constructed auction is feasible. -/
theorem virtualSurplusMaximizingAuction_isFeasible
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).IsFeasible := by
  constructor
  · simpa using A.virtualSurplusMaximizingMechanism_isAllocFeasible
  · intro b
    simpa [virtualSurplusMaximizingAuction] using
      A.virtualSurplusMaximizingAllocationRule_respectsSingleItemCapacity b

/-- Auction feasibility gives allocation-rule feasibility. -/
theorem IsFeasible.isSingleItemAllocationRule
    [Fintype I] {B : BayesianSingleItemAuction I} (hB : B.IsFeasible) :
    IsSingleItemAllocationRule B.allocationRule := by
  exact ⟨fun b i => (hB.1 b i).1, hB.2⟩

end Feasibility

section Measurability

/-! ## Measurability helpers -/

private lemma measurable_virtualScore_le_of_measurable_virtualValues
    [Fintype I] [LinearOrder I] {α : Type*} [MeasurableSpace α]
    (A : BayesianSingleItemAuction I) (b : α → I → ℝ)
    (hb : ∀ j, Measurable fun t => A.virtualValue j (b t j)) (i j : I) :
    MeasurableSet {t | A.virtualScore (b t) j ≤ A.virtualScore (b t) i} := by
  have hset :
      {t | A.virtualScore (b t) j ≤ A.virtualScore (b t) i} =
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} := by
    ext t
    simp [virtualScore, Prod.Lex.toLex_le_toLex]
  rw [hset]
  by_cases hji : j ≤ i
  · have hset' :
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} =
          {t | A.virtualValue j (b t j) < A.virtualValue i (b t i)} ∪
            {t | A.virtualValue j (b t j) = A.virtualValue i (b t i)} := by
      ext t
      simp [hji]
    rw [hset']
    exact (measurableSet_lt (hb j) (hb i)).union
      (measurableSet_eq_fun (hb j) (hb i))
  · have hset' :
        {t | A.virtualValue j (b t j) < A.virtualValue i (b t i) ∨
          A.virtualValue j (b t j) = A.virtualValue i (b t i) ∧ j ≤ i} =
          {t | A.virtualValue j (b t j) < A.virtualValue i (b t i)} := by
      ext t
      simp [hji]
    rw [hset']
    exact measurableSet_lt (hb j) (hb i)

private lemma measurable_winner_eq_of_measurable_virtualValues
    [Fintype I] [Nontrivial I] [LinearOrder I] {α : Type*} [MeasurableSpace α]
    (A : BayesianSingleItemAuction I) (b : α → I → ℝ)
    (hb : ∀ j, Measurable fun t => A.virtualValue j (b t j)) (i : I) :
    MeasurableSet {t | A.virtualSurplusMaximizingWinner (b t) = i} := by
  classical
  haveI : Countable I := inferInstance
  have hset :
      {t | A.virtualSurplusMaximizingWinner (b t) = i} =
        ⋂ j, {t | A.virtualScore (b t) j ≤ A.virtualScore (b t) i} := by
    ext t
    simp [A.virtualSurplusMaximizingWinner_eq_iff_forall_virtualScore_le]
  rw [hset]
  exact MeasurableSet.iInter fun j =>
    A.measurable_virtualScore_le_of_measurable_virtualValues b hb i j

private lemma measurable_winningVirtualValue_pos_of_measurable_virtualValues
    [Fintype I] [Nontrivial I] [LinearOrder I] {α : Type*} [MeasurableSpace α]
    (A : BayesianSingleItemAuction I) (b : α → I → ℝ)
    (hb : ∀ j, Measurable fun t => A.virtualValue j (b t j)) :
    MeasurableSet {t | 0 < A.winningVirtualValue (b t)} := by
  classical
  haveI : Countable I := inferInstance
  have hset :
      {t | 0 < A.winningVirtualValue (b t)} =
        ⋃ j, {t | 0 < A.virtualValue j (b t j)} := by
    ext t
    simp [A.winningVirtualValue_pos_iff_exists_virtualValue_pos]
  rw [hset]
  exact MeasurableSet.iUnion fun j => measurableSet_lt measurable_const (hb j)

private lemma measurable_virtualSurplusMaximizingAllocationRule_comp_of_measurable_virtualValues
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {α : Type*} [MeasurableSpace α]
    (A : BayesianSingleItemAuction I) (b : α → I → ℝ)
    (hb : ∀ j, Measurable fun t => A.virtualValue j (b t j)) (i : I) :
    Measurable fun t => A.virtualSurplusMaximizingAllocationRule (b t) i := by
  classical
  refine Measurable.ite
    (A.measurable_winningVirtualValue_pos_of_measurable_virtualValues b hb) ?_
    measurable_const
  have hwinner : MeasurableSet {t | i = A.virtualSurplusMaximizingWinner (b t)} := by
    simpa [eq_comm] using A.measurable_winner_eq_of_measurable_virtualValues b hb i
  refine Measurable.ite
    hwinner ?_
    measurable_const
  · exact measurable_const

private lemma aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hmeas :
      ∀ i z_i j,
        Measurable fun t : OpponentTypeProfile I i =>
          A.virtualValue j (reportProfile i z_i t j)) :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t =>
          A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t)
        (A.opponentPrior i) := by
  intro i z_i
  have hmeas_alloc :
      Measurable fun t : OpponentTypeProfile I i =>
        A.virtualSurplusMaximizingAllocationRule (reportProfile i z_i t) i :=
    A.measurable_virtualSurplusMaximizingAllocationRule_comp_of_measurable_virtualValues
      (fun t => reportProfile i z_i t) (hmeas i z_i) i
  simpa [interimAllocationIntegrand, virtualSurplusMaximizingAuction,
    virtualSurplusMaximizingMechanism] using hmeas_alloc.aestronglyMeasurable

private lemma measurable_virtualValue_reportProfile_of_measurable_virtualValue
    (A : BayesianSingleItemAuction I)
    (hvirt : ∀ j, Measurable (A.virtualValue j)) :
    ∀ i z_i j,
      Measurable fun t : OpponentTypeProfile I i =>
        A.virtualValue j (reportProfile i z_i t j) := by
  classical
  intro i z_i j
  by_cases hji : j = i
  · subst hji
    simp
  · simpa [reportProfile, hji] using
      (hvirt j).comp (measurable_pi_apply (⟨j, hji⟩ : {j // j ≠ i}))

private lemma measurable_reportProfile_prod (i : I) :
    Measurable fun p : OpponentTypeProfile I i × ℝ => reportProfile i p.2 p.1 := by
  classical
  rw [measurable_pi_iff]
  intro j
  by_cases hji : j = i
  · simpa [reportProfile, hji] using
      (measurable_snd : Measurable fun p : OpponentTypeProfile I i × ℝ => p.2)
  · simpa [reportProfile, hji] using
      ((measurable_pi_apply (⟨j, hji⟩ : {j // j ≠ i})).comp
        (measurable_fst : Measurable fun p : OpponentTypeProfile I i × ℝ => p.1))

private lemma measurable_virtualSurplusMaximizingAllocationRule_reportProfile_prod_of_measurable_virtualValue
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hvirt : ∀ j, Measurable (A.virtualValue j)) (i k : I) :
    Measurable fun p : OpponentTypeProfile I i × ℝ =>
      A.virtualSurplusMaximizingAllocationRule (reportProfile i p.2 p.1) k := by
  exact
    A.measurable_virtualSurplusMaximizingAllocationRule_comp_of_measurable_virtualValues
      (fun p : OpponentTypeProfile I i × ℝ => reportProfile i p.2 p.1)
      (fun j => (hvirt j).comp ((measurable_pi_apply j).comp (measurable_reportProfile_prod i)))
      k

private lemma aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand_of_measurable_virtualValue
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hvirt : ∀ j, Measurable (A.virtualValue j)) :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t =>
          A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t)
        (A.opponentPrior i) :=
  A.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand
    (A.measurable_virtualValue_reportProfile_of_measurable_virtualValue hvirt)

private lemma aestronglyMeasurable_virtualSurplusMaximizingAuction_interimPaymentIntegrand_of_measurable_virtualValue
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hvirt : ∀ j, Measurable (A.virtualValue j)) :
    ∀ i z_i,
      AEStronglyMeasurable
        (fun t =>
          A.virtualSurplusMaximizingAuction.interimPaymentIntegrand i z_i t)
        (A.opponentPrior i) := by
  intro i z_i
  have halloc_fixed :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          A.virtualSurplusMaximizingAllocationRule (reportProfile i z_i t) i)
        (A.opponentPrior i) := by
    exact
      (A.measurable_virtualSurplusMaximizingAllocationRule_comp_of_measurable_virtualValues
        (fun t : OpponentTypeProfile I i => reportProfile i z_i t)
        (A.measurable_virtualValue_reportProfile_of_measurable_virtualValue hvirt i z_i)
        i).aestronglyMeasurable
  have hfirst :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          z_i * A.virtualSurplusMaximizingAllocationRule (reportProfile i z_i t) i)
        (A.opponentPrior i) :=
    halloc_fixed.const_mul z_i
  have hjoint :
      StronglyMeasurable
        (fun p : OpponentTypeProfile I i × ℝ =>
          A.virtualSurplusMaximizingAllocationRule (reportProfile i p.2 p.1) i) :=
    (A.measurable_virtualSurplusMaximizingAllocationRule_reportProfile_prod_of_measurable_virtualValue
      hvirt i i).stronglyMeasurable
  have hleft :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          ∫ z in Set.Ioc 0 z_i,
            A.virtualSurplusMaximizingAllocationRule (reportProfile i z t) i)
        (A.opponentPrior i) := by
    simpa using
      (hjoint.integral_prod_right'
        (ν := volume.restrict (Set.Ioc 0 z_i))).aestronglyMeasurable
  have hright :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          ∫ z in Set.Ioc z_i 0,
            A.virtualSurplusMaximizingAllocationRule (reportProfile i z t) i)
        (A.opponentPrior i) := by
    simpa using
      (hjoint.integral_prod_right'
        (ν := volume.restrict (Set.Ioc z_i 0))).aestronglyMeasurable
  have hintegral :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          ∫ z in 0..z_i, A.virtualSurplusMaximizingAllocationRule (reportProfile i z t) i)
        (A.opponentPrior i) := by
    simpa [intervalIntegral] using hleft.sub hright
  have hpay :
      AEStronglyMeasurable
        (fun t : OpponentTypeProfile I i =>
          z_i * A.virtualSurplusMaximizingAllocationRule (reportProfile i z_i t) i -
            ∫ z in 0..z_i,
              A.virtualSurplusMaximizingAllocationRule (reportProfile i z t) i)
        (A.opponentPrior i) :=
    hfirst.sub hintegral
  simpa [interimPaymentIntegrand, virtualSurplusMaximizingAuction,
    virtualSurplusMaximizingMechanism, virtualSurplusMaximizingPaymentRule,
    SingleParameterMechanism.withMyersonPayment, SingleParameterMechanism.myersonPayment] using hpay

end Measurability

section AllocationOptimality

/-! ## Allocation-rule optimality -/

/-- The deterministic virtual-surplus-maximizing allocation rule is feasible and
pointwise maximizes virtual surplus among all feasible fractional single-item
allocation rules. -/
theorem virtualSurplusMaximizingAllocationRule_isVirtualSurplusOptimalAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    A.IsVirtualSurplusOptimalAllocationRule A.virtualSurplusMaximizingAllocationRule := by
  constructor
  · exact A.virtualSurplusMaximizingAllocationRule_isSingleItemAllocationRule
  · intro y hy b
    exact A.virtualSurplus_le_virtualSurplusMaximizingAllocationRule
      (x := y) (b := b) (hy.1 b) (hy.2 b)

/-- The allocation rule of the Myerson-payment mechanism is virtual-surplus
optimal.  This exposes the optimal-allocation content at the mechanism layer,
while payments continue to be supplied by `MechanismDesign.Myerson`. -/
theorem virtualSurplusMaximizingMechanism_allocationRule_isVirtualSurplusOptimal
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.virtualSurplusMaximizingMechanism).allocationRule := by
  simpa [virtualSurplusMaximizingMechanism] using
    A.virtualSurplusMaximizingAllocationRule_isVirtualSurplusOptimalAllocationRule

/-- The allocation rule of the constructed Bayesian single-item auction is
virtual-surplus optimal. -/
theorem virtualSurplusMaximizingAuction_allocationRule_isVirtualSurplusOptimal
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    A.IsVirtualSurplusOptimalAllocationRule
      (A.virtualSurplusMaximizingAuction).allocationRule := by
  simpa [virtualSurplusMaximizingAuction, virtualSurplusMaximizingMechanism] using
    A.virtualSurplusMaximizingAllocationRule_isVirtualSurplusOptimalAllocationRule

/-- Ex-ante virtual-surplus optimality of the deterministic rule, conditional
on the explicit integrability assumptions needed by the Bochner integral. -/
theorem expectedVirtualSurplus_le_virtualSurplusMaximizingAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x)
    (hx_int : A.IntegrableVirtualSurplus x)
    (hopt_int : A.IntegrableVirtualSurplus A.virtualSurplusMaximizingAllocationRule) :
    A.expectedVirtualSurplus x ≤
      A.expectedVirtualSurplus A.virtualSurplusMaximizingAllocationRule :=
  A.expectedVirtualSurplus_le_of_forall_virtualSurplus_le hx_int hopt_int
    fun b => A.virtualSurplus_le_virtualSurplusMaximizingAllocationRule
      (x := x) (b := b) (hx.1 b) (hx.2 b)

/-- The allocation rule of the constructed Bayesian auction is ex-ante
virtual-surplus optimal under the same explicit integrability assumptions. -/
theorem expectedVirtualSurplus_le_virtualSurplusMaximizingAuction_allocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {x : (I → ℝ) → I → ℝ}
    (hx : IsSingleItemAllocationRule x)
    (hx_int : A.IntegrableVirtualSurplus x)
    (hopt_int : A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule) :
    A.expectedVirtualSurplus x ≤
      A.expectedVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule := by
  simpa [virtualSurplusMaximizingAuction, virtualSurplusMaximizingMechanism] using
    A.expectedVirtualSurplus_le_virtualSurplusMaximizingAllocationRule
      (x := x) hx hx_int hopt_int

/-- Feasibility of a Bayesian candidate is enough to compare its expected
virtual surplus with the virtual-surplus-maximizing auction. -/
theorem expectedVirtualSurplus_le_virtualSurplusMaximizingAuction_of_isFeasible
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A B : BayesianSingleItemAuction I)
    (hB : B.IsFeasible)
    (hB_int : A.IntegrableVirtualSurplus B.allocationRule)
    (hopt_int : A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule) :
    A.expectedVirtualSurplus B.allocationRule ≤
      A.expectedVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule :=
  A.expectedVirtualSurplus_le_virtualSurplusMaximizingAuction_allocationRule
    hB.isSingleItemAllocationRule hB_int hopt_int

end AllocationOptimality

section PaymentNormalization

/-- Zero normalization for a Bayesian single-item auction's payment rule:
reporting `0` gives payment `0`, holding the other reports fixed. -/
def IsZeroNormalized [DecidableEq I] (B : BayesianSingleItemAuction I) : Prop :=
  SingleParameterMechanism.ZeroNormalized B.paymentRule

/-- A zero-normalized payment rule has zero interim expected payment at type
`0`. -/
theorem interimExpectedPayment_zero_of_isZeroNormalized
    [DecidableEq I] (B : BayesianSingleItemAuction I) (hzero : B.IsZeroNormalized)
    (i : I) :
    B.interimExpectedPayment i 0 = 0 := by
  have hpoint :
      (fun t : OpponentTypeProfile I i => B.interimPaymentIntegrand i 0 t) =
        fun _ => 0 := by
    funext t
    have hz := hzero i (reportProfile i 0 t)
    simpa [IsZeroNormalized, SingleParameterMechanism.ZeroNormalized,
      interimPaymentIntegrand] using hz
  rw [B.interimExpectedPayment_eq_integral_interimPaymentIntegrand i 0, hpoint]
  simp

/-- Under the interim envelope formula and nonnegative envelope increments,
zero normalization implies support-restricted interim IR. -/
theorem isIndividuallyRationalOnSupport_of_isZeroNormalized_of_hasInterimEnvelopeFormula
    [DecidableEq I] (B : BayesianSingleItemAuction I)
    (hzero : B.IsZeroNormalized)
    (henv : B.HasInterimEnvelopeFormula)
    (hint_nonneg : B.HasNonnegativeInterimAllocationIntegralOnSupport) :
    B.IsIndividuallyRationalOnSupport := by
  exact
    (B.isIndividuallyRationalOnSupport_iff_interimExpectedPayment_zero_nonpos
      henv hint_nonneg).2
      (fun i => by
        rw [B.interimExpectedPayment_zero_of_isZeroNormalized hzero i])

end PaymentNormalization

section MonotonicityAndDSIC

/-! ## Monotonicity and Myerson implementation -/

private lemma virtualScore_update_ne
    [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) {i j : I} (hji : j ≠ i) (r : ℝ) :
    A.virtualScore (Function.update b i r) j = A.virtualScore b j := by
  simp [virtualScore, Function.update_of_ne hji]

private lemma virtualScore_update_self_mono_of_isRegular
    [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (b : I → ℝ) (i : I) {r s : ℝ} (hrs : r ≤ s) :
    A.virtualScore (Function.update b i r) i ≤
      A.virtualScore (Function.update b i s) i := by
  rw [virtualScore, virtualScore, Function.update_self, Function.update_self,
    Prod.Lex.toLex_le_toLex]
  rcases lt_or_eq_of_le (hA i hrs) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, le_rfl⟩

private lemma virtualSurplusMaximizingWinner_update_self_of_winner
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (b : I → ℝ) (i : I) {r s : ℝ} (hrs : r ≤ s)
    (hwinner : A.virtualSurplusMaximizingWinner (Function.update b i r) = i) :
    A.virtualSurplusMaximizingWinner (Function.update b i s) = i := by
  classical
  let bLo := Function.update b i r
  let bHi := Function.update b i s
  have hstrict : ∀ j, j ≠ i → A.virtualScore bHi j < A.virtualScore bHi i := by
    intro j hji
    have hwinner' : Auction.argmaxBid (A.virtualScore bLo) = i := by
      simpa [virtualSurplusMaximizingWinner, bLo] using hwinner
    have hle_lo :
        A.virtualScore bLo j ≤ A.virtualScore bLo i := by
      simpa [hwinner'] using
        Auction.bid_le_maxBid (A.virtualScore bLo) j
    have hne_lo : A.virtualScore bLo j ≠ A.virtualScore bLo i := by
      intro h
      exact hji (Prod.ext_iff.mp (toLex_inj.mp h)).2
    have hlt_lo : A.virtualScore bLo j < A.virtualScore bLo i :=
      lt_of_le_of_ne hle_lo hne_lo
    have hle_self : A.virtualScore bLo i ≤ A.virtualScore bHi i := by
      simpa [bLo, bHi] using
        A.virtualScore_update_self_mono_of_isRegular hA b i hrs
    have hlt_hi : A.virtualScore bLo j < A.virtualScore bHi i :=
      lt_of_lt_of_le hlt_lo hle_self
    simpa [bLo, bHi, virtualScore_update_ne A b hji s,
      virtualScore_update_ne A b hji r] using hlt_hi
  exact (Auction.eq_argmaxBid_of_strict_max (A.virtualScore bHi) i hstrict).symm

private lemma winningVirtualValue_update_self_of_winner
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) (r : ℝ)
    (hwinner : A.virtualSurplusMaximizingWinner (Function.update b i r) = i) :
    A.winningVirtualValue (Function.update b i r) = A.virtualValue i r := by
  rw [winningVirtualValue, hwinner, Function.update_self]

private lemma winningVirtualValue_update_self_pos_iff_of_winner
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) (r : ℝ)
    (hwinner : A.virtualSurplusMaximizingWinner (Function.update b i r) = i) :
    0 < A.winningVirtualValue (Function.update b i r) ↔ 0 < A.virtualValue i r := by
  rw [A.winningVirtualValue_update_self_of_winner b i r hwinner]

/-- Under regularity, the deterministic virtual-surplus-maximizing allocation
rule is monotone in the sense required by `SingleParameterMechanism`. -/
theorem virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    SingleParameterMechanism.IsMonotone
      ({ allocationRule := A.virtualSurplusMaximizingAllocationRule
         paymentRule := A.virtualSurplusMaximizingPaymentRule } :
        SingleParameterMechanism I ℝ) := by
  classical
  intro i r s hrs b
  change
    A.virtualSurplusMaximizingAllocationRule (Function.update b i r) i ≤
      A.virtualSurplusMaximizingAllocationRule (Function.update b i s) i
  by_cases hwin_lo :
      A.virtualSurplusMaximizingWinner (Function.update b i r) = i
  · have hwin_hi :
        A.virtualSurplusMaximizingWinner (Function.update b i s) = i :=
      A.virtualSurplusMaximizingWinner_update_self_of_winner hA b i hrs hwin_lo
    by_cases hpos_lo : 0 < A.virtualValue i r
    · have hpos_hi : 0 < A.virtualValue i s := lt_of_lt_of_le hpos_lo (hA i hrs)
      have hpos_lo' :
          0 < A.winningVirtualValue (Function.update b i r) :=
        (A.winningVirtualValue_update_self_pos_iff_of_winner b i r hwin_lo).2 hpos_lo
      have hpos_hi' :
          0 < A.winningVirtualValue (Function.update b i s) :=
        (A.winningVirtualValue_update_self_pos_iff_of_winner b i s hwin_hi).2 hpos_hi
      rw [A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos hwin_lo
          hpos_lo',
        A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos hwin_hi
          hpos_hi']
    · have hnotpos_lo :
          ¬ 0 < A.winningVirtualValue (Function.update b i r) :=
        mt (A.winningVirtualValue_update_self_pos_iff_of_winner b i r hwin_lo).1 hpos_lo
      rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos
        (Function.update b i r) hnotpos_lo]
      exact A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i s) i
  · have hi_ne : i ≠ A.virtualSurplusMaximizingWinner (Function.update b i r) :=
      fun hi => hwin_lo hi.symm
    rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_ne_winner hi_ne]
    exact A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i s) i

/-- The regular deterministic virtual-surplus-maximizing mechanism is DSIC by
the existing Myerson payment theorem. -/
theorem virtualSurplusMaximizingMechanism_isDSIC_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    (A.virtualSurplusMaximizingMechanism).IsDSIC := by
  simpa [virtualSurplusMaximizingMechanism, virtualSurplusMaximizingPaymentRule,
    virtualSurplusMaximizingAllocationRule] using
    (SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone
      (x := A.virtualSurplusMaximizingAllocationRule)
      (A.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular hA))

/-- The constructed Bayesian single-item auction is DSIC after forgetting to the
underlying single-parameter mechanism. -/
theorem virtualSurplusMaximizingAuction_isDSIC_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    (A.virtualSurplusMaximizingAuction).IsDSIC := by
  simpa [virtualSurplusMaximizingAuction, virtualSurplusMaximizingMechanism] using
    A.virtualSurplusMaximizingMechanism_isDSIC_of_isRegular hA

/-! ### Myerson payment formula and uniqueness -/

@[simp] theorem virtualSurplusMaximizingMechanism_eq_withMyersonPayment
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingMechanism).toSingleParameterMechanism =
      SingleParameterMechanism.withMyersonPayment A.virtualSurplusMaximizingAllocationRule := by
  rfl

@[simp] theorem virtualSurplusMaximizingPaymentRule_eq
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingPaymentRule b i =
      b i * A.virtualSurplusMaximizingAllocationRule b i -
        ∫ z in 0..b i, A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i := by
  rfl

private theorem intervalIntegral_unitStepFrom_eq_sub {c y : ℝ}
    (hc0 : 0 ≤ c) (hcy : c ≤ y) :
    (∫ z in 0..y, if c < z then (1 : ℝ) else 0) = y - c := by
  have h0y : 0 ≤ y := le_trans hc0 hcy
  have hcongr :
      (∫ z in 0..y, if c < z then (1 : ℝ) else 0) =
        ∫ z in 0..y, (Set.Ioc c y).indicator (fun _ : ℝ => (1 : ℝ)) z := by
    refine intervalIntegral.integral_congr_ae
      (μ := MeasureTheory.volume) (a := 0) (b := y)
      (f := fun z : ℝ => if c < z then (1 : ℝ) else 0)
      (g := fun z : ℝ => (Set.Ioc c y).indicator (fun _ : ℝ => (1 : ℝ)) z) ?_
    filter_upwards with z hz
    have hzIoc : z ∈ Set.Ioc 0 y := by
      simpa [Set.uIoc_of_le h0y] using hz
    by_cases hcz : c < z
    · have hzmem : z ∈ Set.Ioc c y := ⟨hcz, hzIoc.2⟩
      simp [hcz, hzmem]
    · have hznmem : z ∉ Set.Ioc c y := by
        intro hzmem
        exact hcz hzmem.1
      simp [hcz, hznmem]
  rw [hcongr, intervalIntegral.integral_of_le h0y,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  have hinter : Set.Ioc 0 y ∩ Set.Ioc c y = Set.Ioc c y := by
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨⟨lt_of_le_of_lt hc0 hz.1, hz.2⟩, hz⟩
  rw [hinter]
  simp [hcy]

private theorem intervalIntegral_unitStepFrom_eq_zero {c y : ℝ}
    (hy0 : 0 ≤ y) (hyc : y ≤ c) :
    (∫ z in 0..y, if c < z then (1 : ℝ) else 0) = 0 := by
  calc
    (∫ z in 0..y, if c < z then (1 : ℝ) else 0)
        = ∫ z in 0..y, (0 : ℝ) := by
          refine intervalIntegral.integral_congr_ae
            (μ := MeasureTheory.volume) (a := 0) (b := y)
            (f := fun z : ℝ => if c < z then (1 : ℝ) else 0)
            (g := fun _ : ℝ => (0 : ℝ)) ?_
          filter_upwards with z hz
          have hzIoc : z ∈ Set.Ioc 0 y := by
            simpa [Set.uIoc_of_le hy0] using hz
          have hnlt : ¬ c < z := not_lt_of_ge (le_trans hzIoc.2 hyc)
          simp [hnlt]
    _ = 0 := by simp

/-- Critical-value form of the Myerson payment formula.

If bidder `i` receives the item at profile `b`, and along `i`'s one-dimensional
deviation the allocation is a.e. the unit step at critical value `c`, then the
Myerson payment charged to `i` is exactly `c`. The a.e. formulation is designed
to ignore threshold tie-breaking at a single report. -/
theorem virtualSurplusMaximizingPaymentRule_eq_criticalValue_of_ae_stepAllocation
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I} {c : ℝ}
    (hc0 : 0 ≤ c) (hcy : c ≤ b i)
    (halloc : A.virtualSurplusMaximizingAllocationRule b i = 1)
    (hstep : ∀ᵐ z ∂MeasureTheory.volume, z ∈ Set.uIoc 0 (b i) →
      A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i =
        if c < z then (1 : ℝ) else 0) :
    A.virtualSurplusMaximizingPaymentRule b i = c := by
  rw [A.virtualSurplusMaximizingPaymentRule_eq, halloc]
  have hintegral :
      (∫ z in 0..b i,
          A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i) =
        b i - c := by
    calc
      (∫ z in 0..b i,
          A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i)
          = ∫ z in 0..b i, if c < z then (1 : ℝ) else 0 :=
            intervalIntegral.integral_congr_ae
              (μ := MeasureTheory.volume) (a := 0) (b := b i)
              (f := fun z : ℝ =>
                A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i)
              (g := fun z : ℝ => if c < z then (1 : ℝ) else 0) hstep
      _ = b i - c := intervalIntegral_unitStepFrom_eq_sub hc0 hcy
  rw [hintegral]
  ring

/-- Zero-payment form of the Myerson payment formula.

If bidder `i` receives allocation zero at profile `b`, and her one-dimensional
allocation is a.e. a step whose critical value is weakly above her report, then
the canonical Myerson payment is zero. -/
theorem virtualSurplusMaximizingPaymentRule_eq_zero_of_ae_stepAllocation
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {b : I → ℝ} {i : I} {c : ℝ}
    (hbi0 : 0 ≤ b i) (hbic : b i ≤ c)
    (halloc : A.virtualSurplusMaximizingAllocationRule b i = 0)
    (hstep : ∀ᵐ z ∂MeasureTheory.volume, z ∈ Set.uIoc 0 (b i) →
      A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i =
        if c < z then (1 : ℝ) else 0) :
    A.virtualSurplusMaximizingPaymentRule b i = 0 := by
  rw [A.virtualSurplusMaximizingPaymentRule_eq, halloc]
  have hintegral :
      (∫ z in 0..b i,
          A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i) = 0 := by
    calc
      (∫ z in 0..b i,
          A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i)
          = ∫ z in 0..b i, if c < z then (1 : ℝ) else 0 :=
            intervalIntegral.integral_congr_ae
              (μ := MeasureTheory.volume) (a := 0) (b := b i)
              (f := fun z : ℝ =>
                A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i)
              (g := fun z : ℝ => if c < z then (1 : ℝ) else 0) hstep
      _ = 0 := intervalIntegral_unitStepFrom_eq_zero hbi0 hbic
  rw [hintegral]
  ring

/-- The constructed Myerson payment is bounded by twice the absolute report.

This uses only the pointwise allocation bounds `0 ≤ x ≤ 1`; it is the boundedness
half of the interim-integrability proof route. -/
theorem norm_virtualSurplusMaximizingPaymentRule_le
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    ‖A.virtualSurplusMaximizingPaymentRule b i‖ ≤ 2 * ‖b i‖ := by
  let x : ℝ := A.virtualSurplusMaximizingAllocationRule b i
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using A.virtualSurplusMaximizingAllocationRule_nonneg b i
  have hx_le_one : x ≤ 1 := by
    simpa [x] using A.virtualSurplusMaximizingAllocationRule_le_one b i
  have hterm :
      ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖ ≤ ‖b i‖ := by
    calc
      ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖
          = |b i| * x := by
            simp [x, Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
      _ ≤ |b i| * 1 := mul_le_mul_of_nonneg_left hx_le_one (abs_nonneg (b i))
      _ = ‖b i‖ := by simp [Real.norm_eq_abs]
  have hintegral :
      ‖∫ z in 0..b i, A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖
        ≤ ‖b i‖ := by
    have hbound :
        ‖∫ z in 0..b i,
            A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖
          ≤ 1 * |b i - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun z _hz => by
          have hz_nonneg :
              0 ≤ A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i :=
            A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i z) i
          have hz_le_one :
              A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i ≤ 1 :=
            A.virtualSurplusMaximizingAllocationRule_le_one (Function.update b i z) i
          simpa [Real.norm_eq_abs, abs_of_nonneg hz_nonneg] using hz_le_one)
    simpa [Real.norm_eq_abs] using hbound
  calc
    ‖A.virtualSurplusMaximizingPaymentRule b i‖
        = ‖b i * A.virtualSurplusMaximizingAllocationRule b i -
            ∫ z in 0..b i,
              A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖ := by
          rw [A.virtualSurplusMaximizingPaymentRule_eq]
    _ ≤ ‖b i * A.virtualSurplusMaximizingAllocationRule b i‖ +
          ‖∫ z in 0..b i,
            A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i‖ :=
          norm_sub_le _ _
    _ ≤ ‖b i‖ + ‖b i‖ := add_le_add hterm hintegral
    _ = 2 * ‖b i‖ := by ring

/-- For each fixed report, the constructed Myerson payment integrand is bounded
uniformly over opponent profiles. -/
theorem virtualSurplusMaximizingAuction_interimPaymentIntegrand_bound
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (i : I) (z_i : ℝ) :
    ∀ᵐ t ∂A.opponentPrior i,
      ‖A.virtualSurplusMaximizingAuction.interimPaymentIntegrand i z_i t‖ ≤
        2 * ‖z_i‖ := by
  refine Filter.Eventually.of_forall ?_
  intro t
  simpa [interimPaymentIntegrand, virtualSurplusMaximizingAuction,
    virtualSurplusMaximizingMechanism, virtualSurplusMaximizingPaymentRule,
    SingleParameterMechanism.withMyersonPayment, SingleParameterMechanism.myersonPayment] using
    A.norm_virtualSurplusMaximizingPaymentRule_le (reportProfile i z_i t) i

/-- Once the constructed allocation and payment integrands are measurable,
boundedness gives interim integrability for the constructed auction. -/
theorem virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (halloc_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t =>
            A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t)
          (A.opponentPrior i))
    (hpay_meas :
      ∀ i z_i,
        AEStronglyMeasurable
          (fun t =>
            A.virtualSurplusMaximizingAuction.interimPaymentIntegrand i z_i t)
          (A.opponentPrior i)) :
    A.virtualSurplusMaximizingAuction.HasIntegrableInterimObjects :=
  A.virtualSurplusMaximizingAuction
    |>.hasIntegrableInterimObjects_of_aestronglyMeasurable_of_bound
      (by simpa [virtualSurplusMaximizingAuction_opponentPrior] using halloc_meas)
      (by simpa [virtualSurplusMaximizingAuction_opponentPrior] using hpay_meas)
      (by
        intro i z_i
        refine ⟨1, Filter.Eventually.of_forall ?_⟩
        intro t
        have hx :=
          A.virtualSurplusMaximizingAuction_isFeasible.1 (reportProfile i z_i t) i
        have hnonneg :
            0 ≤
              A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t := by
          simpa [interimAllocationIntegrand] using hx.1
        have hle :
            A.virtualSurplusMaximizingAuction.interimAllocationIntegrand i z_i t ≤ 1 := by
          simpa [interimAllocationIntegrand] using hx.2
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hle)
      (by
        intro i z_i
        exact ⟨2 * ‖z_i‖,
          A.virtualSurplusMaximizingAuction_interimPaymentIntegrand_bound i z_i⟩)

theorem virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    A.virtualSurplusMaximizingAuction.HasIntegrableInterimObjects :=
  A.virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_aestronglyMeasurable
    (A.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimAllocationIntegrand_of_measurable_virtualValue
      (A.measurable_virtualValue_of_isRegular hA))
    (A.aestronglyMeasurable_virtualSurplusMaximizingAuction_interimPaymentIntegrand_of_measurable_virtualValue
      (A.measurable_virtualValue_of_isRegular hA))

/-- The Myerson payment rule charges zero to a bidder reporting zero. -/
theorem virtualSurplusMaximizingPaymentRule_zeroNormalized
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    SingleParameterMechanism.ZeroNormalized A.virtualSurplusMaximizingPaymentRule := by
  simpa [virtualSurplusMaximizingPaymentRule] using
    SingleParameterMechanism.myersonPayment_zeroNormalized
      A.virtualSurplusMaximizingAllocationRule

/-- The lifted virtual-surplus-maximizing Bayesian auction is zero-normalized. -/
theorem virtualSurplusMaximizingAuction_isZeroNormalized
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    (A.virtualSurplusMaximizingAuction).IsZeroNormalized := by
  simpa [BayesianSingleItemAuction.IsZeroNormalized, virtualSurplusMaximizingAuction,
    virtualSurplusMaximizingMechanism] using
    A.virtualSurplusMaximizingPaymentRule_zeroNormalized

/-- Quasilinear utility under the Myerson payment rule equals the envelope
expression: current surplus plus accumulated allocation. -/
theorem virtualSurplusMaximizingMechanism_quasiLinearUtility_eq
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (v b : I → ℝ) (i : I) :
    (A.virtualSurplusMaximizingMechanism).quasiLinearUtility b v i =
      (v i - b i) * A.virtualSurplusMaximizingAllocationRule b i +
        ∫ z in 0..b i, A.virtualSurplusMaximizingAllocationRule (Function.update b i z) i := by
  simpa [virtualSurplusMaximizingMechanism, virtualSurplusMaximizingPaymentRule] using
    SingleParameterMechanism.withMyersonPayment_quasiLinearUtility_eq
      A.virtualSurplusMaximizingAllocationRule v b i

/-- Regular virtual values make the virtual-surplus-maximizing allocation
implementable by Myerson's monotonicity criterion. -/
theorem virtualSurplusMaximizingAllocationRule_isImplementable_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    SingleParameterMechanism.IsImplementable A.virtualSurplusMaximizingAllocationRule := by
  exact
    SingleParameterMechanism.isImplementable_of_isMonotone
      (by
        simpa [virtualSurplusMaximizingPaymentRule] using
          A.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular hA)

/-- Any zero-normalized DSIC payment rule implementing the virtual-surplus-maximizing
allocation is the canonical Myerson payment rule. -/
theorem paymentRule_eq_virtualSurplusMaximizingPaymentRule_of_isDSIC_of_zeroNormalized
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) {p : (I → ℝ) → I → ℝ}
    (hdsic :
      ({ allocationRule := A.virtualSurplusMaximizingAllocationRule
         paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC)
    (hzero : SingleParameterMechanism.ZeroNormalized p) :
    p = A.virtualSurplusMaximizingPaymentRule := by
  simpa [virtualSurplusMaximizingPaymentRule] using
    SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized
      (x := A.virtualSurplusMaximizingAllocationRule) (p := p) hdsic hzero

/-- The canonical Myerson payment rule is the unique zero-normalized DSIC
payment rule for the virtual-surplus-maximizing allocation. -/
theorem existsUnique_zeroNormalized_paymentRule_for_virtualSurplusMaximizingAllocationRule
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    ∃! p : (I → ℝ) → I → ℝ,
      SingleParameterMechanism.ZeroNormalized p ∧
        ({ allocationRule := A.virtualSurplusMaximizingAllocationRule
           paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC := by
  exact
    SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone
      (x := A.virtualSurplusMaximizingAllocationRule)
      (by
        simpa [virtualSurplusMaximizingPaymentRule] using
          A.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular hA)

/-- Main mechanism-level package theorem for the regular case: the
virtual-surplus-maximizing mechanism uses a virtual-surplus-optimal allocation
rule and is DSIC with the canonical Myerson payment rule. -/
theorem virtualSurplusMaximizingMechanism_isVirtualSurplusOptimal_and_isDSIC_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    A.IsVirtualSurplusOptimalAllocationRule
        (A.virtualSurplusMaximizingMechanism).allocationRule ∧
      (A.virtualSurplusMaximizingMechanism).IsDSIC := by
  exact ⟨A.virtualSurplusMaximizingMechanism_allocationRule_isVirtualSurplusOptimal,
    A.virtualSurplusMaximizingMechanism_isDSIC_of_isRegular hA⟩

/-- Main auction-level package theorem for the regular case: the constructed
Bayesian single-item auction has a virtual-surplus-optimal allocation rule, is
feasible, and is DSIC after forgetting to the underlying single-parameter
mechanism. -/
theorem virtualSurplusMaximizingAuction_isVirtualSurplusOptimal_and_isFeasible_and_isDSIC_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    A.IsVirtualSurplusOptimalAllocationRule
        (A.virtualSurplusMaximizingAuction).allocationRule ∧
      (A.virtualSurplusMaximizingAuction).IsFeasible ∧
        (A.virtualSurplusMaximizingAuction).IsDSIC := by
  exact ⟨A.virtualSurplusMaximizingAuction_allocationRule_isVirtualSurplusOptimal,
    A.virtualSurplusMaximizingAuction_isFeasible,
    A.virtualSurplusMaximizingAuction_isDSIC_of_isRegular hA⟩

end MonotonicityAndDSIC

section AnalyticSupportAndDensity

/-! ## Support and density assumptions for the analytic identity layer -/

/-- Agent `i`'s type lies in `[0, ωᵢ]`. -/
def IsOnTypeSupport (A : BayesianSingleItemAuction I) (i : I) (v : ℝ) : Prop :=
  0 ≤ v ∧ v ≤ A.typeData.omega i

/-- A type profile lies in the product support. -/
def IsOnTypeProfileSupport (A : BayesianSingleItemAuction I) (t : I → ℝ) : Prop :=
  ∀ i, A.IsOnTypeSupport i (t i)

/-- Densities are positive on support interiors. -/
def HasPositiveDensityOnSupport (A : BayesianSingleItemAuction I) : Prop :=
  ∀ i v, 0 < v → v < A.typeData.omega i → 0 < A.typeDensity i v

/-- Densities are nonnegative on supports. -/
def HasNonnegativeDensityOnSupport (A : BayesianSingleItemAuction I) : Prop :=
  ∀ i v, 0 ≤ v → v ≤ A.typeData.omega i → 0 ≤ A.typeDensity i v

/-- The joint density is positive at a profile. -/
def HasPositiveJointDensityAt [Fintype I]
    (A : BayesianSingleItemAuction I) (t : I → ℝ) : Prop :=
  0 < A.jointDensity t

/-- A profile lies in the interior of the product support. -/
def IsOnTypeProfileInterior (A : BayesianSingleItemAuction I) (t : I → ℝ) : Prop :=
  ∀ i, 0 < t i ∧ t i < A.typeData.omega i

theorem isOnTypeSupport_left
    (A : BayesianSingleItemAuction I) {i : I} {v : ℝ}
    (hv : A.IsOnTypeSupport i v) :
    0 ≤ v :=
  hv.1

theorem isOnTypeSupport_right
    (A : BayesianSingleItemAuction I) {i : I} {v : ℝ}
    (hv : A.IsOnTypeSupport i v) :
    v ≤ A.typeData.omega i :=
  hv.2

theorem isOnTypeProfileSupport_apply
    (A : BayesianSingleItemAuction I) {t : I → ℝ}
    (ht : A.IsOnTypeProfileSupport t) (i : I) :
    A.IsOnTypeSupport i (t i) :=
  ht i

theorem isOnTypeProfileInterior_isOnTypeProfileSupport
    (A : BayesianSingleItemAuction I) {t : I → ℝ}
    (ht : A.IsOnTypeProfileInterior t) :
    A.IsOnTypeProfileSupport t := by
  intro i
  exact ⟨le_of_lt (ht i).1, le_of_lt (ht i).2⟩

theorem typeDensity_pos_of_hasPositiveDensityOnSupport
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) {i : I} {v : ℝ}
    (h0 : 0 < v) (homega : v < A.typeData.omega i) :
    0 < A.typeDensity i v :=
  hA i v h0 homega

theorem typeDensity_nonneg_of_hasNonnegativeDensityOnSupport
    (A : BayesianSingleItemAuction I)
    (hA : A.HasNonnegativeDensityOnSupport) {i : I} {v : ℝ}
    (h0 : 0 ≤ v) (homega : v ≤ A.typeData.omega i) :
    0 ≤ A.typeDensity i v :=
  hA i v h0 homega

theorem typeDensity_measurable (A : BayesianSingleItemAuction I) (i : I) :
    Measurable (A.typeDensity i) := by
  simpa [typeDensity] using measurable_deriv (A.typeData.cdf i).cdf

theorem typeDensity_ennreal_ofReal_aemeasurable
    (A : BayesianSingleItemAuction I) (i : I) :
    AEMeasurable
      (fun v => ENNReal.ofReal (A.typeDensity i v))
      (volume.restrict (Set.Ioc 0 (A.typeData.omega i))) :=
  (A.typeDensity_measurable i).aemeasurable.ennreal_ofReal

theorem typeDensity_nonnegative_ae_of_hasPositiveDensityOnSupport
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) (i : I) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
      0 ≤ A.typeDensity i v := by
  have hne :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        v ≠ A.typeData.omega i :=
    ae_restrict_of_ae (Measure.ae_ne volume (A.typeData.omega i))
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with v hv hvne
  exact (A.typeDensity_pos_of_hasPositiveDensityOnSupport hA hv.1
    (lt_of_le_of_ne hv.2 hvne)).le

theorem typeMeasure_isProbabilityMeasure_of_cdf_absolutelyContinuous_of_density_nonnegative_ae
    (A : BayesianSingleItemAuction I)
    (i : I)
    (hAC :
      AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i))
    (hdens_ae :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v) :
    IsProbabilityMeasure (A.typeMeasure i) := by
  refine ⟨?_⟩
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have hint : Integrable (A.typeDensity i) (volume.restrict s) := by
    have hinterval :
        IntervalIntegrable (A.typeDensity i) volume 0 (A.typeData.omega i) := by
      simpa [typeDensity] using hAC.intervalIntegrable_deriv
    have hio :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (A.typeData.cdf i).omega_nonneg).mp hinterval
    simpa [IntegrableOn, s] using hio
  have hintegral : (∫ v, A.typeDensity i v ∂volume.restrict s) = 1 := by
    have hinterval :
        (∫ v in 0..A.typeData.omega i, A.typeDensity i v) = 1 := by
      calc
        (∫ v in 0..A.typeData.omega i, A.typeDensity i v)
            = (A.typeData.cdf i).cdf (A.typeData.omega i) -
                (A.typeData.cdf i).cdf 0 := by
              simpa [typeDensity] using hAC.integral_deriv_eq_sub
        _ = 1 := by
              rw [(A.typeData.cdf i).cdf_upper, (A.typeData.cdf i).cdf_zero]
              ring
    rw [← intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg]
    exact hinterval
  have hlintegral :
      (∫⁻ v, ENNReal.ofReal (A.typeDensity i v) ∂volume.restrict s) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (by simpa [s] using hdens_ae),
      hintegral]
    norm_num
  simpa [typeMeasure, s] using hlintegral

theorem typeMeasure_isProbabilityMeasure_of_cdf_absolutelyContinuous_of_positiveDensity
    (A : BayesianSingleItemAuction I)
    (hdens : A.HasPositiveDensityOnSupport)
    (i : I)
    (hAC :
      AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i)) :
    IsProbabilityMeasure (A.typeMeasure i) :=
  A.typeMeasure_isProbabilityMeasure_of_cdf_absolutelyContinuous_of_density_nonnegative_ae
    i hAC (A.typeDensity_nonnegative_ae_of_hasPositiveDensityOnSupport hdens i)

theorem typeDensity_pos_of_hasPositiveDensityOnSupport_of_profileInterior
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) {t : I → ℝ}
    (ht : A.IsOnTypeProfileInterior t) (i : I) :
    0 < A.typeDensity i (t i) :=
  A.typeDensity_pos_of_hasPositiveDensityOnSupport hA (ht i).1 (ht i).2

theorem jointDensity_pos_of_hasPositiveDensityOnSupport_of_profileInterior
    [Fintype I] (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) {t : I → ℝ}
    (ht : A.IsOnTypeProfileInterior t) :
    A.HasPositiveJointDensityAt t := by
  dsimp [HasPositiveJointDensityAt, jointDensity]
  exact Finset.prod_pos fun i _ =>
    A.typeDensity_pos_of_hasPositiveDensityOnSupport_of_profileInterior hA ht i

/-- Integration by parts for the survival term. -/
theorem survivalIntegral_eq_intervalIntegral_mul_deriv
    {F Q : ℝ → ℝ} {ω : ℝ}
    (hω : 0 ≤ ω)
    (hF : AbsolutelyContinuousOnInterval F 0 ω)
    (hF0 : F 0 = 0) (hFω : F ω = 1)
    (hQ : IntervalIntegrable Q volume 0 ω) :
    (∫ v in 0..ω, Q v * (1 - F v)) =
      ∫ v in 0..ω, (∫ z in 0..v, Q z) * deriv F v := by
  let G : ℝ → ℝ := fun v => ∫ z in 0..v, Q z
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 ω := by
    rw [Set.uIcc_of_le hω]
    exact ⟨le_rfl, hω⟩
  have hG : AbsolutelyContinuousOnInterval G 0 ω :=
    hQ.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hQF : IntervalIntegrable (fun v => Q v * F v) volume 0 ω :=
    by simpa [mul_comm] using hQ.continuousOn_mul hF.continuousOn
  have hderiv_ae :
      ∀ᵐ v ∂volume, v ∈ Set.uIoc 0 ω → deriv G v = Q v := by
    filter_upwards [hQ.ae_hasDerivAt_integral] with v hv hv_mem
    exact (hv (Set.uIoc_subset_uIcc hv_mem) 0 h0mem).deriv
  have hderiv_integral :
      (∫ v in 0..ω, deriv G v * F v) =
        ∫ v in 0..ω, Q v * F v := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv_ae] with v hv hv_mem
    rw [hv hv_mem]
  have hibp :
      (∫ v in 0..ω, G v * deriv F v) =
        (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
    calc
      (∫ v in 0..ω, G v * deriv F v)
          = G ω * F ω - G 0 * F 0 - ∫ v in 0..ω, deriv G v * F v :=
            hG.integral_mul_deriv_eq_deriv_mul hF
      _ = (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
            rw [hderiv_integral]
            simp [G, hF0, hFω]
  have hsurvival :
      (∫ v in 0..ω, Q v * (1 - F v)) =
        (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
    calc
      (∫ v in 0..ω, Q v * (1 - F v))
          = ∫ v in 0..ω, Q v - Q v * F v := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with v hv_mem
            ring
      _ = (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
            rw [intervalIntegral.integral_sub hQ hQF]
  exact hsurvival.trans hibp.symm

/-- CDF assumptions for the interim virtual-surplus comparison. -/
structure EnvelopeVirtualSurplusAnalyticAssumptions
    (A B : BayesianSingleItemAuction I) : Prop where
  cdf_absolutelyContinuous :
    ∀ i : I, AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i)
  positive_density_on_support :
    A.HasPositiveDensityOnSupport
  interim_allocation_intervalIntegrable :
    ∀ i : I, IntervalIntegrable (B.interimAllocProb i) volume 0 (A.typeData.omega i)
  interim_allocation_survival_integrable :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))
        volume 0 (A.typeData.omega i)
  interim_virtual_surplus_integrable :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i)

/-- Environment-level analytic assumptions for the envelope/virtual-surplus
comparison. -/
structure EnvelopeVirtualSurplusEnvironmentAssumptions
    (A : BayesianSingleItemAuction I) : Prop where
  /-- Type CDFs are absolutely continuous on their support intervals. -/
  cdf_absolutelyContinuous :
    ∀ i : I, AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i)
  /-- Type densities are positive on support. -/
  positive_density_on_support :
    A.HasPositiveDensityOnSupport
  /-- Virtual values are integrable under the one-dimensional type measures. -/
  virtualValue_integrable :
    ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)

/-- Build the environment-level envelope package from primitive distribution
assumptions and one-dimensional virtual-value integrability. -/
theorem EnvelopeVirtualSurplusEnvironmentAssumptions.of_primitives
    {A : BayesianSingleItemAuction I}
    (hAC :
      ∀ i : I, AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i))
    (hdens : A.HasPositiveDensityOnSupport)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)) :
    A.EnvelopeVirtualSurplusEnvironmentAssumptions where
  cdf_absolutelyContinuous := hAC
  positive_density_on_support := hdens
  virtualValue_integrable := hvirt

theorem EnvelopeVirtualSurplusEnvironmentAssumptions.typeDensity_nonnegative_ae
    {A : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusEnvironmentAssumptions) (i : I) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
      0 ≤ A.typeDensity i v :=
  A.typeDensity_nonnegative_ae_of_hasPositiveDensityOnSupport
    h.positive_density_on_support i

theorem EnvelopeVirtualSurplusEnvironmentAssumptions.typeMeasure_isProbabilityMeasure
    {A : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusEnvironmentAssumptions) (i : I) :
    IsProbabilityMeasure (A.typeMeasure i) :=
  A.typeMeasure_isProbabilityMeasure_of_cdf_absolutelyContinuous_of_positiveDensity
    h.positive_density_on_support i (h.cdf_absolutelyContinuous i)

theorem EnvelopeVirtualSurplusEnvironmentAssumptions.virtualValue_integrable_on_typeMeasure
    {A : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusEnvironmentAssumptions) (i : I) :
    Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.virtualValue_integrable i

theorem EnvelopeVirtualSurplusEnvironmentAssumptions.virtualValue_integrable_all
    {A : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusEnvironmentAssumptions) :
    ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.virtualValue_integrable

theorem envelopeVirtualSurplusAnalyticAssumptions_of_environment
    {A B : BayesianSingleItemAuction I}
    (henv : A.EnvelopeVirtualSurplusEnvironmentAssumptions)
    (hQ :
      ∀ i : I, IntervalIntegrable (B.interimAllocProb i) volume 0 (A.typeData.omega i))
    (hQsurv :
      ∀ i : I,
        IntervalIntegrable
          (fun v => B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))
          volume 0 (A.typeData.omega i))
    (hvirt :
      ∀ i : I,
        IntervalIntegrable
          (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
          volume 0 (A.typeData.omega i)) :
    A.EnvelopeVirtualSurplusAnalyticAssumptions B where
  cdf_absolutelyContinuous := henv.cdf_absolutelyContinuous
  positive_density_on_support := henv.positive_density_on_support
  interim_allocation_intervalIntegrable := hQ
  interim_allocation_survival_integrable := hQsurv
  interim_virtual_surplus_integrable := hvirt

theorem HasPositiveDensityOnSupport.nonzero_on_support
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) {i : I} {v : ℝ}
    (h0 : 0 < v) (homega : v < A.typeData.omega i) :
    A.typeDensity i v ≠ 0 :=
  (A.typeDensity_pos_of_hasPositiveDensityOnSupport hA h0 homega).ne'

/-- On support, virtual-value density equals value density minus survival probability. -/
theorem virtualValue_mul_typeDensity_eq_valueDensity_sub_survival_onSupport
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) (i : I) :
    Set.EqOn
      (fun v => A.virtualValue i v * A.typeDensity i v)
      (fun v => v * A.typeDensity i v - (1 - (A.typeData.cdf i).cdf v))
      (Set.uIoc 0 (A.typeData.omega i)) := by
  intro v hv
  have hv' : v ∈ Set.Ioc 0 (A.typeData.omega i) := by
    simpa [Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg] using hv
  have h0 : 0 < v := hv'.1
  have homega : v ≤ A.typeData.omega i := hv'.2
  have homega_lt_or_eq : v < A.typeData.omega i ∨ v = A.typeData.omega i :=
    lt_or_eq_of_le homega
  rcases homega_lt_or_eq with homega_lt | rfl
  · have hdens_ne : A.typeDensity i v ≠ 0 :=
      hA.nonzero_on_support A h0 homega_lt
    simp [virtualValue, sub_mul, div_eq_mul_inv, hdens_ne]
  · have hFω : (A.typeData.cdf i).cdf (A.typeData.omega i) = 1 :=
      (A.typeData.cdf i).cdf_upper
    have hsurv_zero : 1 - (A.typeData.cdf i).cdf (A.typeData.omega i) = 0 := by
      rw [hFω]
      ring
    simp [virtualValue, hsurv_zero]

/-- Density-side virtual-value integral as value-density minus survival. -/
theorem integral_virtualValue_mul_typeDensity_eq_valueDensity_sub_survival
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) (i : I)
    (hvalue :
      IntervalIntegrable
        (fun v => v * A.typeDensity i v)
        volume 0 (A.typeData.omega i))
    (hsurvival :
      IntervalIntegrable
        (fun v => 1 - (A.typeData.cdf i).cdf v)
        volume 0 (A.typeData.omega i)) :
    (∫ v in 0..A.typeData.omega i, A.virtualValue i v * A.typeDensity i v) =
      (∫ v in 0..A.typeData.omega i, v * A.typeDensity i v) -
        ∫ v in 0..A.typeData.omega i, 1 - (A.typeData.cdf i).cdf v := by
  calc
    (∫ v in 0..A.typeData.omega i, A.virtualValue i v * A.typeDensity i v)
        =
          ∫ v in 0..A.typeData.omega i,
            v * A.typeDensity i v - (1 - (A.typeData.cdf i).cdf v) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with v hv
          exact
            A.virtualValue_mul_typeDensity_eq_valueDensity_sub_survival_onSupport
              hA i hv
    _ = (∫ v in 0..A.typeData.omega i, v * A.typeDensity i v) -
          ∫ v in 0..A.typeData.omega i, 1 - (A.typeData.cdf i).cdf v := by
          rw [intervalIntegral.integral_sub hvalue hsurvival]

/-- Density-side MSZ 12.56: the virtual-value integral is zero when the
value-density integral equals the survival integral. -/
theorem integral_virtualValue_mul_typeDensity_eq_zero_of_valueDensity_eq_survival
    (A : BayesianSingleItemAuction I)
    (hA : A.HasPositiveDensityOnSupport) (i : I)
    (hvalue :
      IntervalIntegrable
        (fun v => v * A.typeDensity i v)
        volume 0 (A.typeData.omega i))
    (hsurvival :
      IntervalIntegrable
        (fun v => 1 - (A.typeData.cdf i).cdf v)
        volume 0 (A.typeData.omega i))
    (hmean :
      (∫ v in 0..A.typeData.omega i, v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i, 1 - (A.typeData.cdf i).cdf v) :
    (∫ v in 0..A.typeData.omega i, A.virtualValue i v * A.typeDensity i v) = 0 := by
  rw [A.integral_virtualValue_mul_typeDensity_eq_valueDensity_sub_survival hA i hvalue hsurvival,
    hmean]
  ring

/-- Assumptions for the MSZ 12.56 virtual-value mean-zero identity.

It records the density-side value integral, the survival integral, and the
tail-integral identity equating them.  Together with the environment-level
positive-density assumptions, it implies that each bidder's virtual value has
zero expectation.
-/
structure VirtualValueMeanZeroAnalyticAssumptions
    (A : BayesianSingleItemAuction I) : Prop where
  /-- The value-density integrand is interval-integrable on support. -/
  value_density_integrable :
    ∀ i : I,
      IntervalIntegrable
        (fun v => v * A.typeDensity i v)
        volume 0 (A.typeData.omega i)
  /-- The survival function is interval-integrable on support. -/
  survival_integrable :
    ∀ i : I,
      IntervalIntegrable
        (fun v => 1 - (A.typeData.cdf i).cdf v)
        volume 0 (A.typeData.omega i)
  /-- The value-density integral agrees with the survival integral. -/
  value_density_eq_survival :
    ∀ i : I,
      (∫ v in 0..A.typeData.omega i, v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i, 1 - (A.typeData.cdf i).cdf v

/-- Projection: value-density integrability for MSZ 12.56. -/
theorem VirtualValueMeanZeroAnalyticAssumptions.valueDensity_integrable
    {A : BayesianSingleItemAuction I}
    (h : A.VirtualValueMeanZeroAnalyticAssumptions) (i : I) :
    IntervalIntegrable
      (fun v => v * A.typeDensity i v)
      volume 0 (A.typeData.omega i) :=
  h.value_density_integrable i

/-- Projection: survival integrability for MSZ 12.56. -/
theorem VirtualValueMeanZeroAnalyticAssumptions.survival_integrable_onSupport
    {A : BayesianSingleItemAuction I}
    (h : A.VirtualValueMeanZeroAnalyticAssumptions) (i : I) :
    IntervalIntegrable
      (fun v => 1 - (A.typeData.cdf i).cdf v)
      volume 0 (A.typeData.omega i) :=
  h.survival_integrable i

/-- Projection: the tail-integral identity used in MSZ 12.56. -/
theorem VirtualValueMeanZeroAnalyticAssumptions.valueDensity_eq_survival
    {A : BayesianSingleItemAuction I}
    (h : A.VirtualValueMeanZeroAnalyticAssumptions) (i : I) :
    (∫ v in 0..A.typeData.omega i, v * A.typeDensity i v) =
      ∫ v in 0..A.typeData.omega i, 1 - (A.typeData.cdf i).cdf v :=
  h.value_density_eq_survival i

/-- Density-side MSZ 12.56 from the packaged tail-integral identity. -/
theorem VirtualValueMeanZeroAnalyticAssumptions.integral_virtualValue_mul_typeDensity_eq_zero
    {A : BayesianSingleItemAuction I}
    (h : A.VirtualValueMeanZeroAnalyticAssumptions)
    (hpos : A.HasPositiveDensityOnSupport) (i : I) :
    (∫ v in 0..A.typeData.omega i, A.virtualValue i v * A.typeDensity i v) = 0 :=
  A.integral_virtualValue_mul_typeDensity_eq_zero_of_valueDensity_eq_survival
    hpos i
    (h.valueDensity_integrable i)
    (h.survival_integrable_onSupport i)
    (h.valueDensity_eq_survival i)

/-- MSZ 12.56 in type-measure form: each virtual value has zero expectation. -/
theorem VirtualValueMeanZeroAnalyticAssumptions.integral_virtualValue_typeMeasure_eq_zero
    {A : BayesianSingleItemAuction I}
    (h : A.VirtualValueMeanZeroAnalyticAssumptions)
    (henv : A.EnvelopeVirtualSurplusEnvironmentAssumptions) (i : I) :
    (∫ v, A.virtualValue i v ∂A.typeMeasure i) = 0 := by
  rw [A.integral_typeMeasure_eq_intervalIntegral_mul i
    (A.virtualValue i)
    (A.typeDensity_ennreal_ofReal_aemeasurable i)
    (henv.typeDensity_nonnegative_ae i)]
  exact h.integral_virtualValue_mul_typeDensity_eq_zero henv.positive_density_on_support i

theorem EnvelopeVirtualSurplusAnalyticAssumptions.interim_allocation_intervalIntegrableOnSupport
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    IntervalIntegrable (B.interimAllocProb i) volume 0 (A.typeData.omega i) :=
  h.interim_allocation_intervalIntegrable i

theorem EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegrand_eq_onSupport
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    Set.EqOn
      (fun v =>
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      (fun v =>
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
          B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
            (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      (Set.uIoc 0 (A.typeData.omega i)) := by
  intro v hv
  have hv' : v ∈ Set.Ioc 0 (A.typeData.omega i) := by
    simpa [Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg] using hv
  have h0 : 0 < v := hv'.1
  have homega : v ≤ A.typeData.omega i := hv'.2
  have homega_lt_or_eq : v < A.typeData.omega i ∨ v = A.typeData.omega i :=
    lt_or_eq_of_le homega
  rcases homega_lt_or_eq with homega_lt | rfl
  · have hdens_ne :
        A.typeDensity i v ≠ 0 :=
      h.positive_density_on_support.nonzero_on_support A h0 homega_lt
    simp [virtualValue, mul_sub, sub_mul, mul_assoc, div_eq_mul_inv, hdens_ne]
  · have hFω : (A.typeData.cdf i).cdf (A.typeData.omega i) = 1 :=
      (A.typeData.cdf i).cdf_upper
    have hsurv_zero : 1 - (A.typeData.cdf i).cdf (A.typeData.omega i) = 0 := by
      rw [hFω]
      ring
    simp [virtualValue, hsurv_zero, sub_mul]

theorem EnvelopeVirtualSurplusAnalyticAssumptions.accumulatedAllocation_density_integrable
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    IntervalIntegrable
      (fun v => (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  have hQ := h.interim_allocation_intervalIntegrableOnSupport i
  have hAC := h.cdf_absolutelyContinuous i
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 (A.typeData.omega i) := by
    rw [Set.uIcc_of_le (A.typeData.cdf i).omega_nonneg]
    exact ⟨le_rfl, (A.typeData.cdf i).omega_nonneg⟩
  have hG : AbsolutelyContinuousOnInterval
      (fun v => ∫ z in 0..v, B.interimAllocProb i z) 0 (A.typeData.omega i) :=
    hQ.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hderiv_int :
      IntervalIntegrable
        (fun v => (∫ z in 0..v, B.interimAllocProb i z) * deriv (A.typeData.cdf i).cdf v)
        volume 0 (A.typeData.omega i) :=
    hAC.intervalIntegrable_deriv.continuousOn_mul hG.continuousOn
  simpa [typeDensity] using hderiv_int

theorem EnvelopeVirtualSurplusAnalyticAssumptions.survivalIntegral_eq_accumulatedDensity
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    (∫ v in 0..A.typeData.omega i,
        B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v)) =
      ∫ v in 0..A.typeData.omega i,
        (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
  simpa [typeDensity] using
    survivalIntegral_eq_intervalIntegral_mul_deriv
      (F := (A.typeData.cdf i).cdf)
      (Q := B.interimAllocProb i)
      (ω := A.typeData.omega i)
      (A.typeData.cdf i).omega_nonneg
      (h.cdf_absolutelyContinuous i)
      (A.typeData.cdf i).cdf_zero
      (A.typeData.cdf i).cdf_upper
      (h.interim_allocation_intervalIntegrableOnSupport i)

theorem EnvelopeVirtualSurplusAnalyticAssumptions.envelope_density_integrable
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    IntervalIntegrable
      (fun v =>
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  have hQsurv := h.interim_allocation_survival_integrable i
  have hvirtual := h.interim_virtual_surplus_integrable i
  have hderiv_int := h.accumulatedAllocation_density_integrable i
  have hsplit :
      IntervalIntegrable
        (fun v =>
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
            B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
              (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
        volume 0 (A.typeData.omega i) :=
    (hvirtual.add hQsurv).sub hderiv_int
  exact hsplit.congr (h.envelopeIntegrand_eq_onSupport i).symm

end AnalyticSupportAndDensity

section RevenueOptimalityInterface

/-! ## Abstract expected-revenue optimality interface -/

/-- Myerson-payment revenue of `B`, evaluated in environment `A`. -/
noncomputable def myersonPaymentRevenueInEnvironment [Fintype I] [DecidableEq I]
    (A B : BayesianSingleItemAuction I) : ℝ :=
  A.expectedPaymentRevenueInEnvironment
    (SingleParameterMechanism.myersonPayment B.allocationRule)

/-- Ex-ante virtual surplus through interim allocation probabilities. -/
noncomputable def expectedInterimVirtualSurplus [Fintype I]
    (A B : BayesianSingleItemAuction I) : ℝ :=
  ∑ i, ∫ v in 0..A.typeData.omega i,
    B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v

/-- Expected revenue equals expected virtual surplus. -/
def HasExpectedRevenueVirtualSurplusIdentity [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.expectedSellerRevenueInEnvironment B =
    A.expectedVirtualSurplus B.allocationRule

/-- Expected revenue is bounded above by expected virtual surplus. -/
def HasExpectedRevenueVirtualSurplusUpperBound [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.expectedSellerRevenueInEnvironment B ≤
    A.expectedVirtualSurplus B.allocationRule

/-- Myerson-payment revenue equals expected virtual surplus. -/
def HasMyersonPaymentRevenueVirtualSurplusIdentity [Fintype I] [DecidableEq I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.myersonPaymentRevenueInEnvironment B =
    A.expectedVirtualSurplus B.allocationRule

/-- Ex-ante virtual surplus agrees with the interim expression. -/
def HasExpectedVirtualSurplusInterimIdentity [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.expectedVirtualSurplus B.allocationRule =
    A.expectedInterimVirtualSurplus B

/-- Fubini hypotheses connecting ex-ante and interim expressions. -/
structure InterimFubiniAnalyticAssumptions [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop where
  payment_integrable :
    ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior
  virtual_surplus_integrable :
    ∀ i : I, Integrable (fun t => B.allocationRule t i * A.virtualValue i (t i)) A.prior
  payment_interim_fubini :
    ∀ i : I,
      (∫ t, B.paymentRule t i ∂A.prior) =
        ∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v
  virtual_surplus_interim_fubini :
    ∀ i : I,
      (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v

theorem InterimFubiniAnalyticAssumptions.toPaymentInterimFubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.InterimFubiniAnalyticAssumptions B) :
    A.PaymentInterimFubiniAssumptions B where
  payment_integrable := h.payment_integrable
  payment_interim_fubini := h.payment_interim_fubini

theorem InterimFubiniAnalyticAssumptions.expectedPaymentRevenueIntegrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.InterimFubiniAnalyticAssumptions B) :
    Integrable (fun t => ∑ i, B.paymentRule t i) A.prior :=
  h.toPaymentInterimFubini.expectedPaymentRevenueIntegrable

theorem InterimFubiniAnalyticAssumptions.integrableVirtualSurplus
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.InterimFubiniAnalyticAssumptions B) :
    A.IntegrableVirtualSurplus B.allocationRule := by
  dsimp [IntegrableVirtualSurplus, virtualSurplus]
  exact integrable_finsetSum Finset.univ fun i _ => h.virtual_surplus_integrable i

theorem InterimFubiniAnalyticAssumptions.hasExpectedRevenueInterimPaymentIdentity
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.InterimFubiniAnalyticAssumptions B) :
    A.HasExpectedRevenueInterimPaymentIdentity B := by
  exact h.toPaymentInterimFubini.hasExpectedRevenueInterimPaymentIdentity

theorem InterimFubiniAnalyticAssumptions.hasExpectedVirtualSurplusInterimIdentity
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.InterimFubiniAnalyticAssumptions B) :
    A.HasExpectedVirtualSurplusInterimIdentity B := by
  dsimp [
    HasExpectedVirtualSurplusInterimIdentity,
    expectedVirtualSurplus,
    virtualSurplus,
    expectedInterimVirtualSurplus]
  calc
    (∫ t, ∑ i, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior)
        = ∑ i, ∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior := by
          simpa using
            (integral_finsetSum (s := Finset.univ)
              (f := fun i t => B.allocationRule t i * A.virtualValue i (t i))
              (fun i _ => h.virtual_surplus_integrable i))
    _ = ∑ i, ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
          exact Finset.sum_congr rfl fun i _ => h.virtual_surplus_interim_fubini i

/-- Type-measure Fubini hypotheses. -/
structure TypeMeasureInterimFubiniAnalyticAssumptions [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop where
  payment_integrable :
    ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior
  virtual_surplus_integrable :
    ∀ i : I, Integrable (fun t => B.allocationRule t i * A.virtualValue i (t i)) A.prior
  type_density_measurable :
    ∀ i : I,
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i)))
  type_density_nonnegative_ae :
    ∀ i : I,
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v
  payment_typeMeasure_fubini :
    ∀ i : I,
      (∫ t, B.paymentRule t i ∂A.prior) =
        ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i
  virtual_surplus_typeMeasure_fubini :
    ∀ i : I,
      (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior) =
        ∫ v, B.interimAllocProb i v * A.virtualValue i v ∂A.typeMeasure i

theorem typeMeasureInterimFubiniAnalyticAssumptions_of_typeMeasure_fubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hpay_int : ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior)
    (hvs_int :
      ∀ i : I, Integrable (fun t => B.allocationRule t i * A.virtualValue i (t i))
        A.prior)
    (hpay_fubini :
      ∀ i : I,
        (∫ t, B.paymentRule t i ∂A.prior) =
          ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i)
    (hvs_fubini :
      ∀ i : I,
        (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior) =
          ∫ v, B.interimAllocProb i v * A.virtualValue i v ∂A.typeMeasure i) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B where
  payment_integrable := hpay_int
  virtual_surplus_integrable := hvs_int
  type_density_measurable := fun i => A.typeDensity_ennreal_ofReal_aemeasurable i
  type_density_nonnegative_ae := hdens_ae
  payment_typeMeasure_fubini := hpay_fubini
  virtual_surplus_typeMeasure_fubini := hvs_fubini

theorem TypeMeasureInterimFubiniAnalyticAssumptions.toInterimFubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.TypeMeasureInterimFubiniAnalyticAssumptions B) :
    A.InterimFubiniAnalyticAssumptions B where
  payment_integrable := h.payment_integrable
  virtual_surplus_integrable := h.virtual_surplus_integrable
  payment_interim_fubini := by
    intro i
    calc
      (∫ t, B.paymentRule t i ∂A.prior)
          = ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i :=
            h.payment_typeMeasure_fubini i
      _ = ∫ v in 0..A.typeData.omega i,
            B.interimExpectedPayment i v * A.typeDensity i v := by
            exact A.integral_typeMeasure_eq_intervalIntegral_mul i
              (B.interimExpectedPayment i)
              (h.type_density_measurable i)
              (h.type_density_nonnegative_ae i)
  virtual_surplus_interim_fubini := by
    intro i
    calc
      (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior)
          = ∫ v, B.interimAllocProb i v * A.virtualValue i v ∂A.typeMeasure i :=
            h.virtual_surplus_typeMeasure_fubini i
      _ = ∫ v in 0..A.typeData.omega i,
            (B.interimAllocProb i v * A.virtualValue i v) * A.typeDensity i v := by
            exact A.integral_typeMeasure_eq_intervalIntegral_mul i
              (fun v => B.interimAllocProb i v * A.virtualValue i v)
              (h.type_density_measurable i)
              (h.type_density_nonnegative_ae i)
      _ = ∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with v _hv
            ring

/-- Interim-payment revenue is bounded by interim virtual surplus. -/
def HasInterimPaymentVirtualSurplusUpperBound [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  ∀ i : I,
    (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) ≤
      ∫ v in 0..A.typeData.omega i,
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v

/-- The envelope-term upper bound for interim expected payments. -/
def HasInterimPaymentEnvelopeUpperBound [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  ∀ i : I,
    (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) ≤
      ∫ v in 0..A.typeData.omega i,
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v

/-- Envelope-term revenue is bounded by interim virtual surplus. -/
def HasEnvelopeVirtualSurplusUpperBound [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  ∀ i : I,
    (∫ v in 0..A.typeData.omega i,
      (B.interimAllocProb i v * v -
        ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) ≤
      ∫ v in 0..A.typeData.omega i,
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v

theorem EnvelopeVirtualSurplusAnalyticAssumptions.envelopeIntegral_eq_virtualSurplusIntegral
    {A B : BayesianSingleItemAuction I}
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) (i : I) :
    (∫ v in 0..A.typeData.omega i,
      (B.interimAllocProb i v * v -
        ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) =
      ∫ v in 0..A.typeData.omega i,
        B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
  have hsurv := h.survivalIntegral_eq_accumulatedDensity i
  have hvirt_int := h.interim_virtual_surplus_integrable i
  have hcongr :
      (∫ v in 0..A.typeData.omega i,
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
            B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
              (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with v hv
    exact h.envelopeIntegrand_eq_onSupport i hv
  have hderiv_int := h.accumulatedAllocation_density_integrable i
  calc
    (∫ v in 0..A.typeData.omega i,
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
        = ∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v +
              B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v) -
                (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := hcongr
    _ = (∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v) -
          (-(∫ v in 0..A.typeData.omega i,
            B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))) -
            ∫ v in 0..A.typeData.omega i,
              (∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
          rw [intervalIntegral.integral_sub
            (hvirt_int.add (h.interim_allocation_survival_integrable i)) hderiv_int,
            intervalIntegral.integral_add hvirt_int (h.interim_allocation_survival_integrable i)]
          ring
    _ = ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
          rw [hsurv]
          ring

theorem hasEnvelopeVirtualSurplusUpperBound_of_analyticAssumptions
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (h : A.EnvelopeVirtualSurplusAnalyticAssumptions B) :
    A.HasEnvelopeVirtualSurplusUpperBound B := by
  intro i
  exact le_of_eq (h.envelopeIntegral_eq_virtualSurplusIntegral i)

/-- Product-side virtual-surplus integrability gives interval integrability of
the density-weighted interim virtual surplus. -/
theorem intervalIntegrable_interimAllocProb_mul_virtualValue_mul_typeDensity_of_profileSplit_integrable
    {A B : BayesianSingleItemAuction I} (i : I)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v)
    (hvs :
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i))) :
    IntervalIntegrable
      (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
      volume 0 (A.typeData.omega i) := by
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have hinner :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i)
        (A.typeMeasure i) := by
    simpa using hvs.integral_prod_left
  have htop :
      ∀ᵐ v ∂(volume.restrict s),
        ENNReal.ofReal (A.typeDensity i v) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hinner' :
      Integrable
        (fun v : ℝ =>
          ∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i)
        ((volume.restrict s).withDensity fun v => ENNReal.ofReal (A.typeDensity i v)) := by
    simpa [typeMeasure, s] using hinner
  have hsmul :
      Integrable
        (fun v : ℝ =>
          (ENNReal.ofReal (A.typeDensity i v)).toReal •
            (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
              ∂B.opponentPrior i))
        (volume.restrict s) :=
    (integrable_withDensity_iff_integrable_smul₀' hmeas htop).mp hinner'
  have hmul :
      Integrable
        (fun v : ℝ =>
          (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i) * A.typeDensity i v)
        (volume.restrict s) := by
    refine hsmul.congr ?_
    filter_upwards [hnonneg] with v hv
    rw [ENNReal.toReal_ofReal hv]
    simp [smul_eq_mul, mul_comm]
  have hcongr :
      (fun v : ℝ =>
          (∫ t, B.allocationRule (reportProfile i v t) i * A.virtualValue i v
            ∂B.opponentPrior i) * A.typeDensity i v) =
        fun v : ℝ =>
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
    funext v
    simp [interimAllocProb, interimExpectation, integral_mul_const]
  have hint :
      Integrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        (volume.restrict s) := by
    simpa [hcongr, s] using hmul
  rw [intervalIntegrable_iff, Set.uIoc_of_le (A.typeData.cdf i).omega_nonneg]
  simpa [IntegrableOn, s] using hint

@[simp] theorem virtualSurplusMaximizingAuction_hasSameSellingEnvironment
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) :
    A.HasSameSellingEnvironment A.virtualSurplusMaximizingAuction := by
  simp [HasSameSellingEnvironment]

/-- Product-side virtual-surplus integrability gives ex-ante virtual-surplus
integrability under independent priors. -/
theorem integrableVirtualSurplus_of_profileSplit_integrable_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B)
    (hvs_prod_int :
      ∀ i : I,
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i))) :
    A.IntegrableVirtualSurplus B.allocationRule := by
  dsimp [IntegrableVirtualSurplus, virtualSurplus]
  exact integrable_finsetSum Finset.univ fun i _ => by
    apply A.integrable_prior_of_integrable_profileSplit_of_hasIndependentTypePriors hind i
    have hprod := hvs_prod_int i
    rw [henv.opponentPrior_eq] at hprod
    simpa using hprod

/-- Build type-measure Fubini hypotheses from independent priors and product-side
integrability. This is the main bridge from the full prior to interim
one-dimensional expressions. -/
theorem typeMeasureInterimFubiniAnalyticAssumptions_of_independentTypePriors
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
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
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hvs_prod_int :
      ∀ i : I,
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i))) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B where
  payment_integrable := by
    intro i
    apply A.integrable_prior_of_integrable_profileSplit_of_hasIndependentTypePriors hind i
    have hprod := hpay_prod_int i
    rwa [henv.opponentPrior_eq] at hprod
  virtual_surplus_integrable := by
    intro i
    apply A.integrable_prior_of_integrable_profileSplit_of_hasIndependentTypePriors hind i
    have hprod := hvs_prod_int i
    rw [henv.opponentPrior_eq] at hprod
    simpa using hprod
  type_density_measurable := fun i => A.typeDensity_ennreal_ofReal_aemeasurable i
  type_density_nonnegative_ae := hdens_ae
  payment_typeMeasure_fubini := by
    intro i
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
  virtual_surplus_typeMeasure_fubini := by
    intro i
    have hprod :
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (A.opponentPrior i)) := by
      have h := hvs_prod_int i
      rwa [henv.opponentPrior_eq] at h
    have hprod_full :
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i *
              A.virtualValue i ((reportProfile i p.1 p.2) i))
          ((A.typeMeasure i).prod (A.opponentPrior i)) := by
      simpa using hprod
    have hfubini :=
      A.integral_prior_eq_integral_typeMeasure_opponentPrior_of_hasIndependentTypePriors
        hind i (fun t => B.allocationRule t i * A.virtualValue i (t i)) hprod_full
    calc
      (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior)
          = ∫ v, ∫ t,
              B.allocationRule (reportProfile i v t) i *
                A.virtualValue i ((reportProfile i v t) i)
              ∂A.opponentPrior i ∂A.typeMeasure i := hfubini
      _ = ∫ v, ∫ t,
              B.allocationRule (reportProfile i v t) i * A.virtualValue i v
              ∂A.opponentPrior i ∂A.typeMeasure i := by
            refine integral_congr_ae ?_
            filter_upwards with v
            refine integral_congr_ae ?_
            filter_upwards with t
            simp
      _ = ∫ v,
            (∫ t, B.allocationRule (reportProfile i v t) i ∂A.opponentPrior i) *
              A.virtualValue i v ∂A.typeMeasure i := by
            refine integral_congr_ae ?_
            filter_upwards with v
            rw [integral_mul_const]
      _ = ∫ v, B.interimAllocProb i v * A.virtualValue i v ∂A.typeMeasure i := by
            refine integral_congr_ae ?_
            filter_upwards with v
            simp [interimAllocProb, interimExpectation, henv.opponentPrior_eq]

theorem interimFubiniAnalyticAssumptions_of_independentTypePriors
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
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
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hvs_prod_int :
      ∀ i : I,
        Integrable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i))) :
    A.InterimFubiniAnalyticAssumptions B :=
  (A.typeMeasureInterimFubiniAnalyticAssumptions_of_independentTypePriors
    hdens_ae hind henv hpay_prod_int hvs_prod_int).toInterimFubini

/-- Product-side profile-split integrability for one candidate auction. -/
structure ProfileSplitIntegrabilityAssumptions
    (A B : BayesianSingleItemAuction I) : Prop where
  /-- Candidate payments are integrable after splitting each profile into one
  bidder's type and the opponents' profile. -/
  payment_integrable :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i))
  /-- Candidate allocation-weighted virtual surplus is integrable after the same
  one-coordinate/opponent-profile split. -/
  virtual_surplus_integrable :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i))

/-- Product-side profile-split measurability for one candidate auction. -/
structure ProfileSplitMeasurabilityAssumptions
    (A B : BayesianSingleItemAuction I) : Prop where
  /-- Candidate payments are a.e. strongly measurable after profile splitting. -/
  payment_aestronglyMeasurable :
    ∀ i : I,
      AEStronglyMeasurable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i))
  /-- Candidate allocation-weighted virtual surplus is a.e. strongly measurable
  after profile splitting. -/
  virtual_surplus_aestronglyMeasurable :
    ∀ i : I,
      AEStronglyMeasurable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i))

/-- Profile-split integrability implies profile-split measurability. -/
theorem ProfileSplitIntegrabilityAssumptions.toProfileSplitMeasurabilityAssumptions
    {A B : BayesianSingleItemAuction I}
    (h : A.ProfileSplitIntegrabilityAssumptions B) :
    A.ProfileSplitMeasurabilityAssumptions B where
  payment_aestronglyMeasurable := fun i => (h.payment_integrable i).aestronglyMeasurable
  virtual_surplus_aestronglyMeasurable :=
    fun i => (h.virtual_surplus_integrable i).aestronglyMeasurable

/-- Measurable profile-split integrands give the a.e.-strong measurability package. -/
theorem ProfileSplitMeasurabilityAssumptions.of_measurable
    {A B : BayesianSingleItemAuction I}
    (hpay_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.paymentRule (reportProfile i p.1 p.2) i))
    (hvs_meas :
      ∀ i : I,
        Measurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)) :
    A.ProfileSplitMeasurabilityAssumptions B where
  payment_aestronglyMeasurable := fun i => (hpay_meas i).aestronglyMeasurable
  virtual_surplus_aestronglyMeasurable := fun i => (hvs_meas i).aestronglyMeasurable

/-- A.e. strong measurability and bounds imply profile-split payment integrability. -/
theorem profileSplit_payment_integrable_of_aestronglyMeasurable_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hpay_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i)) := by
  intro i
  rcases hpay_bound i with ⟨C, hC⟩
  exact Integrable.of_bound (hpay_meas i) C hC

/-- A.e. strong measurability and bounds imply profile-split virtual-surplus integrability. -/
theorem profileSplit_virtual_surplus_integrable_of_aestronglyMeasurable_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hvs_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1‖ ≤ C) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) := by
  intro i
  rcases hvs_bound i with ⟨C, hC⟩
  exact Integrable.of_bound (hvs_meas i) C hC

/-- A.e. strong measurability and bounds imply profile-split integrability. -/
theorem profileSplitIntegrabilityAssumptions_of_aestronglyMeasurable_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (hpay_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.paymentRule (reportProfile i p.1 p.2) i)
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i)))
    (hpay_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C)
    (hvs_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1‖ ≤ C) :
    A.ProfileSplitIntegrabilityAssumptions B where
  payment_integrable :=
    profileSplit_payment_integrable_of_aestronglyMeasurable_of_bound
      hpay_meas hpay_bound
  virtual_surplus_integrable :=
    profileSplit_virtual_surplus_integrable_of_aestronglyMeasurable_of_bound
      hvs_meas hvs_bound

/-- Profile-split payment measurability and bounds imply payment integrability. -/
theorem ProfileSplitMeasurabilityAssumptions.payment_integrable_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitMeasurabilityAssumptions B)
    (hpay_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  profileSplit_payment_integrable_of_aestronglyMeasurable_of_bound
    h.payment_aestronglyMeasurable hpay_bound

/-- Profile-split virtual-surplus measurability and bounds imply integrability. -/
theorem ProfileSplitMeasurabilityAssumptions.virtual_surplus_integrable_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitMeasurabilityAssumptions B)
    (hvs_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1‖ ≤ C) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  profileSplit_virtual_surplus_integrable_of_aestronglyMeasurable_of_bound
    h.virtual_surplus_aestronglyMeasurable hvs_bound

/-- Profile-split measurability and bounds imply profile-split integrability. -/
theorem ProfileSplitMeasurabilityAssumptions.toProfileSplitIntegrabilityAssumptions_of_bound
    {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitMeasurabilityAssumptions B)
    (hpay_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C)
    (hvs_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1‖ ≤ C) :
    A.ProfileSplitIntegrabilityAssumptions B :=
  { payment_integrable := h.payment_integrable_of_bound hpay_bound
    virtual_surplus_integrable := h.virtual_surplus_integrable_of_bound hvs_bound }

/-- Feasibility and one-dimensional virtual-value integrability imply
profile-split virtual-surplus integrability. -/
theorem profileSplit_virtual_surplus_integrable_of_virtualValue_integrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hfeas : B.IsFeasible)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i))
    (hvs_meas :
      ∀ i : I,
        AEStronglyMeasurable
          (fun p : ℝ × OpponentTypeProfile I i =>
            B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
          ((A.typeMeasure i).prod (B.opponentPrior i))) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) := by
  intro i
  let μ := (A.typeMeasure i).prod (B.opponentPrior i)
  have hbase :
      Integrable (fun p : ℝ × OpponentTypeProfile I i => A.virtualValue i p.1) μ := by
    simpa [μ] using (hvirt i).comp_fst (B.opponentPrior i)
  refine hbase.mono (hvs_meas i) ?_
  filter_upwards with p
  have halloc := hfeas.1 (reportProfile i p.1 p.2) i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg halloc.1, ← Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) halloc.2

/-- Profile-split measurability, feasibility, and one-dimensional virtual-value
integrability imply profile-split virtual-surplus integrability. -/
theorem ProfileSplitMeasurabilityAssumptions.virtual_surplus_integrable_of_virtualValue_integrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.ProfileSplitMeasurabilityAssumptions B)
    (hfeas : B.IsFeasible)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  profileSplit_virtual_surplus_integrable_of_virtualValue_integrable
    hfeas hvirt h.virtual_surplus_aestronglyMeasurable

/-- Profile-split measurability, payment bounds, feasibility, and one-dimensional
virtual-value integrability imply profile-split integrability. -/
theorem ProfileSplitMeasurabilityAssumptions.toProfileSplitIntegrabilityAssumptions_of_paymentBound_of_virtualValue_integrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitMeasurabilityAssumptions B)
    (hfeas : B.IsFeasible)
    (hpay_bound :
      ∀ i : I,
        ∃ C : ℝ,
          ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
            ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)) :
    A.ProfileSplitIntegrabilityAssumptions B where
  payment_integrable := by
    intro i
    rcases hpay_bound i with ⟨C, hC⟩
    exact Integrable.of_bound (h.payment_aestronglyMeasurable i) C hC
  virtual_surplus_integrable :=
    h.virtual_surplus_integrable_of_virtualValue_integrable hfeas hvirt

/-- Profile-split payment integrability gives density-integrable interim payments. -/
theorem ProfileSplitIntegrabilityAssumptions.payment_density_integrable
    {A B : BayesianSingleItemAuction I}
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) := by
  intro i
  exact A.intervalIntegrable_interimExpectedPayment_mul_typeDensity_of_profileSplit_integrable
    i
    (A.typeDensity_ennreal_ofReal_aemeasurable i)
    (hdens_ae i)
    (h.payment_integrable i)

/-- Profile-split virtual-surplus integrability gives the interim density form. -/
theorem ProfileSplitIntegrabilityAssumptions.virtual_surplus_density_integrable
    {A B : BayesianSingleItemAuction I}
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) := by
  intro i
  exact
    A.intervalIntegrable_interimAllocProb_mul_virtualValue_mul_typeDensity_of_profileSplit_integrable
      i
      (A.typeDensity_ennreal_ofReal_aemeasurable i)
      (hdens_ae i)
      (h.virtual_surplus_integrable i)

/-- Profile-split integrability plus independent priors gives type-measure Fubini. -/
theorem ProfileSplitIntegrabilityAssumptions.toTypeMeasureInterimFubini
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B :=
  A.typeMeasureInterimFubiniAnalyticAssumptions_of_independentTypePriors
    hdens_ae hind henv h.payment_integrable h.virtual_surplus_integrable

/-- Profile-split integrability plus independent priors gives interim Fubini. -/
theorem ProfileSplitIntegrabilityAssumptions.toInterimFubini
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B) :
    A.InterimFubiniAnalyticAssumptions B :=
  (h.toTypeMeasureInterimFubini hdens_ae hind henv).toInterimFubini

/-- Profile-split virtual-surplus integrability gives ex-ante integrability. -/
theorem ProfileSplitIntegrabilityAssumptions.integrableVirtualSurplus
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B) :
    A.IntegrableVirtualSurplus B.allocationRule :=
  A.integrableVirtualSurplus_of_profileSplit_integrable_of_hasIndependentTypePriors
    hind henv h.virtual_surplus_integrable

/-- Feasible candidates with revenue equal to virtual surplus. -/
def IsRevenueComparable [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.HasSameSellingEnvironment B ∧
    B.IsFeasible ∧
    A.IntegrableVirtualSurplus B.allocationRule ∧
      A.HasExpectedRevenueVirtualSurplusIdentity B

/-- Feasible candidates with revenue bounded by virtual surplus. -/
def IsRevenueUpperBounded [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.HasSameSellingEnvironment B ∧
    B.IsFeasible ∧
    A.IntegrableVirtualSurplus B.allocationRule ∧
      A.HasExpectedRevenueVirtualSurplusUpperBound B

/-- A revenue-comparable candidate keeps the base selling environment. -/
theorem IsRevenueComparable.hasSameSellingEnvironment
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueComparable B) :
    A.HasSameSellingEnvironment B :=
  hB.1

/-- A revenue-comparable candidate is feasible. -/
theorem IsRevenueComparable.isFeasible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueComparable B) :
    B.IsFeasible :=
  hB.2.1

/-- A revenue-comparable candidate has integrable virtual surplus. -/
theorem IsRevenueComparable.integrableVirtualSurplus
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueComparable B) :
    A.IntegrableVirtualSurplus B.allocationRule :=
  hB.2.2.1

/-- A revenue-comparable candidate satisfies the revenue/virtual-surplus identity. -/
theorem IsRevenueComparable.expectedRevenueVirtualSurplusIdentity
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueComparable B) :
    A.HasExpectedRevenueVirtualSurplusIdentity B :=
  hB.2.2.2

/-- A revenue-upper-bounded candidate keeps the base selling environment. -/
theorem IsRevenueUpperBounded.hasSameSellingEnvironment
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueUpperBounded B) :
    A.HasSameSellingEnvironment B :=
  hB.1

/-- A revenue-upper-bounded candidate is feasible. -/
theorem IsRevenueUpperBounded.isFeasible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueUpperBounded B) :
    B.IsFeasible :=
  hB.2.1

/-- A revenue-upper-bounded candidate has integrable virtual surplus. -/
theorem IsRevenueUpperBounded.integrableVirtualSurplus
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueUpperBounded B) :
    A.IntegrableVirtualSurplus B.allocationRule :=
  hB.2.2.1

/-- A revenue-upper-bounded candidate satisfies the revenue/virtual-surplus upper bound. -/
theorem IsRevenueUpperBounded.expectedRevenueVirtualSurplusUpperBound
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRevenueUpperBounded B) :
    A.HasExpectedRevenueVirtualSurplusUpperBound B :=
  hB.2.2.2

/-- Feasible IC/IR candidates with integrable virtual surplus. -/
def IsFeasibleICIRIntegrable [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.HasSameSellingEnvironment B ∧
    B.IsFeasible ∧
    B.IsIncentiveCompatible ∧
      B.IsIndividuallyRationalOnSupport ∧
        A.IntegrableVirtualSurplus B.allocationRule

/-- A feasible IC/IR integrable candidate keeps the base selling environment. -/
theorem IsFeasibleICIRIntegrable.hasSameSellingEnvironment
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.HasSameSellingEnvironment B :=
  hB.1

/-- A feasible IC/IR integrable candidate is feasible. -/
theorem IsFeasibleICIRIntegrable.isFeasible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B) :
    B.IsFeasible :=
  hB.2.1

/-- A feasible IC/IR integrable candidate is interim incentive compatible. -/
theorem IsFeasibleICIRIntegrable.isIncentiveCompatible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B) :
    B.IsIncentiveCompatible :=
  hB.2.2.1

/-- A feasible IC/IR integrable candidate is individually rational on support. -/
theorem IsFeasibleICIRIntegrable.isIndividuallyRationalOnSupport
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B) :
    B.IsIndividuallyRationalOnSupport :=
  hB.2.2.2.1

/-- A feasible IC/IR integrable candidate has integrable virtual surplus. -/
theorem IsFeasibleICIRIntegrable.integrableVirtualSurplus
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.IntegrableVirtualSurplus B.allocationRule :=
  hB.2.2.2.2

/-- Profile-split integrability plus the economic IC/IR conditions forms a
feasible IC/IR integrable candidate. -/
theorem ProfileSplitIntegrabilityAssumptions.toIsFeasibleICIRIntegrable
    [Fintype I] [DecidableEq I] {A B : BayesianSingleItemAuction I}
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.ProfileSplitIntegrabilityAssumptions B)
    (hind : A.HasIndependentTypePriors)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.IsFeasibleICIRIntegrable B :=
  ⟨henv, hfeas, hIC, hIR, h.integrableVirtualSurplus hind henv⟩

/-! ## Environment assumptions for MSZ 12.59 -/

/-- Environment assumptions for the MSZ 12.59 IC/IR revenue comparison.

This package isolates the selling environment from candidate-specific
profile-split obligations.
-/
structure RegularMyersonICIREnvironmentAssumptions
    [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) : Prop where
  /-- The auction environment has independent type priors. -/
  independent_type_priors :
    A.HasIndependentTypePriors
  /-- CDF, density, and envelope assumptions used to compare interim payments
  with interim virtual surplus. -/
  envelope_environment :
    A.EnvelopeVirtualSurplusEnvironmentAssumptions

/-- Build the regular-Myerson environment package from primitive environment
data: independent priors, CDF absolute continuity, positive density on support,
and one-dimensional virtual-value integrability. -/
theorem RegularMyersonICIREnvironmentAssumptions.of_primitives
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (hind : A.HasIndependentTypePriors)
    (hAC :
      ∀ i : I, AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i))
    (hdens : A.HasPositiveDensityOnSupport)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i)) :
    A.RegularMyersonICIREnvironmentAssumptions where
  independent_type_priors := hind
  envelope_environment :=
    EnvelopeVirtualSurplusEnvironmentAssumptions.of_primitives hAC hdens hvirt

/-- Build the regular-Myerson environment package from independent priors and
an already packaged envelope/virtual-surplus environment. -/
theorem RegularMyersonICIREnvironmentAssumptions.of_envelopeEnvironment
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (hind : A.HasIndependentTypePriors)
    (henv : A.EnvelopeVirtualSurplusEnvironmentAssumptions) :
    A.RegularMyersonICIREnvironmentAssumptions where
  independent_type_priors := hind
  envelope_environment := henv

/-- Projection: the auction environment has independent type priors. -/
theorem RegularMyersonICIREnvironmentAssumptions.hasIndependentTypePriors
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIREnvironmentAssumptions) :
    A.HasIndependentTypePriors :=
  h.independent_type_priors

/-- Projection: the environment-level envelope/virtual-surplus assumptions. -/
theorem RegularMyersonICIREnvironmentAssumptions.envelopeEnvironment
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIREnvironmentAssumptions) :
    A.EnvelopeVirtualSurplusEnvironmentAssumptions :=
  h.envelope_environment

/-- Projection: type measures are probability measures under the environment package. -/
theorem RegularMyersonICIREnvironmentAssumptions.typeMeasure_isProbabilityMeasure
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIREnvironmentAssumptions) (i : I) :
    IsProbabilityMeasure (A.typeMeasure i) :=
  h.envelopeEnvironment.typeMeasure_isProbabilityMeasure i

/-- Projection: virtual values are type-measure integrable under the environment package. -/
theorem RegularMyersonICIREnvironmentAssumptions.virtualValue_integrable_on_typeMeasure
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIREnvironmentAssumptions) (i : I) :
    Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.envelopeEnvironment.virtualValue_integrable_on_typeMeasure i

/-- Projection: all virtual values are type-measure integrable under the environment package. -/
theorem RegularMyersonICIREnvironmentAssumptions.virtualValue_integrable_all
    [Fintype I] [DecidableEq I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIREnvironmentAssumptions) :
    ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.envelopeEnvironment.virtualValue_integrable_all

/-! ## Candidate assumptions for MSZ 12.59 -/

/-- Candidate assumptions that imply profile-split integrability.

This package separates candidate measurability from payment bounds.  Together
with the environment-level virtual-value integrability and candidate
feasibility, it reconstructs `ProfileSplitIntegrabilityAssumptions`.
-/
structure RegularMyersonICIRCandidateProfileSplitAssumptions
    [Fintype I] (A : BayesianSingleItemAuction I) : Prop where
  /-- Candidate payments and allocation-weighted virtual surplus are measurable
  after splitting profiles into one bidder's type and the opponents' profile. -/
  candidate_profileSplit_measurability :
    ∀ B : BayesianSingleItemAuction I,
      B.IsFeasible →
        B.IsIncentiveCompatible →
          B.IsIndividuallyRationalOnSupport →
            A.ProfileSplitMeasurabilityAssumptions B
  /-- Candidate payments are a.e. bounded after profile splitting. -/
  candidate_payment_bound :
    ∀ B : BayesianSingleItemAuction I,
      B.IsFeasible →
        B.IsIncentiveCompatible →
          B.IsIndividuallyRationalOnSupport →
            ∀ i : I,
              ∃ C : ℝ,
                ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
                  ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C

/-- Projection: candidate profile-split measurability. -/
theorem RegularMyersonICIRCandidateProfileSplitAssumptions.candidate_profileSplitMeasurabilityAssumptions
    [Fintype I] {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRCandidateProfileSplitAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.ProfileSplitMeasurabilityAssumptions B :=
  h.candidate_profileSplit_measurability B hfeas hIC hIR

/-- Projection: candidate profile-split payment bounds. -/
theorem RegularMyersonICIRCandidateProfileSplitAssumptions.candidate_paymentBound
    [Fintype I] {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRCandidateProfileSplitAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      ∃ C : ℝ,
        ∀ᵐ p ∂((A.typeMeasure i).prod (B.opponentPrior i)),
          ‖B.paymentRule (reportProfile i p.1 p.2) i‖ ≤ C :=
  h.candidate_payment_bound B hfeas hIC hIR

/-- Candidate-side measurability and payment bounds imply profile-split
integrability under the environment-level virtual-value assumptions. -/
theorem RegularMyersonICIRCandidateProfileSplitAssumptions.candidate_profileSplitIntegrabilityAssumptions
    [Fintype I] {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRCandidateProfileSplitAssumptions)
    (henv : A.EnvelopeVirtualSurplusEnvironmentAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.ProfileSplitIntegrabilityAssumptions B := by
  haveI : ∀ i : I, IsProbabilityMeasure (A.typeMeasure i) :=
    henv.typeMeasure_isProbabilityMeasure
  exact
    (h.candidate_profileSplitMeasurabilityAssumptions B hfeas hIC hIR)
      |>.toProfileSplitIntegrabilityAssumptions_of_paymentBound_of_virtualValue_integrable
        hfeas
        (h.candidate_paymentBound B hfeas hIC hIR)
        henv.virtualValue_integrable_all

/-! ## Analytic package for MSZ 12.59 -/

/-- Analytic package for the MSZ 12.59 IC/IR revenue comparison.

It keeps the economic hypotheses separate from measure-theoretic Fubini and
integrability obligations for arbitrary feasible IC/IR candidates.
-/
structure RegularMyersonICIRAnalyticAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) : Prop where
  /-- The auction environment has independent type priors. -/
  independent_type_priors :
    A.HasIndependentTypePriors
  /-- CDF, density, and envelope assumptions used to compare interim payments
  with interim virtual surplus. -/
  envelope_environment :
    A.EnvelopeVirtualSurplusEnvironmentAssumptions
  /-- Candidate payment and virtual-surplus integrability after profile splitting. -/
  candidate_profileSplit_integrability :
    ∀ B : BayesianSingleItemAuction I,
      B.IsFeasible →
        B.IsIncentiveCompatible →
          B.IsIndividuallyRationalOnSupport →
            A.ProfileSplitIntegrabilityAssumptions B

/-- Build the regular Myerson analytic package from candidate-side
profile-split measurability and payment bounds. -/
theorem RegularMyersonICIRAnalyticAssumptions.of_candidateProfileSplitAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (hind : A.HasIndependentTypePriors)
    (henv : A.EnvelopeVirtualSurplusEnvironmentAssumptions)
    (hcand : A.RegularMyersonICIRCandidateProfileSplitAssumptions) :
    A.RegularMyersonICIRAnalyticAssumptions where
  independent_type_priors := hind
  envelope_environment := henv
  candidate_profileSplit_integrability := by
    intro B hfeas hIC hIR
    exact hcand.candidate_profileSplitIntegrabilityAssumptions henv B hfeas hIC hIR

/-- Build the regular Myerson analytic package from the environment package and
candidate-side profile-split assumptions. -/
theorem RegularMyersonICIRAnalyticAssumptions.of_environment_candidateProfileSplitAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (henv : A.RegularMyersonICIREnvironmentAssumptions)
    (hcand : A.RegularMyersonICIRCandidateProfileSplitAssumptions) :
    A.RegularMyersonICIRAnalyticAssumptions :=
  RegularMyersonICIRAnalyticAssumptions.of_candidateProfileSplitAssumptions
    henv.hasIndependentTypePriors henv.envelopeEnvironment hcand

/-- Build the regular Myerson analytic package directly from primitive
environment assumptions and the candidate profile-split package. -/
theorem RegularMyersonICIRAnalyticAssumptions.of_primitives_candidateProfileSplitAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (hind : A.HasIndependentTypePriors)
    (hAC :
      ∀ i : I, AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i))
    (hdens : A.HasPositiveDensityOnSupport)
    (hvirt : ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i))
    (hcand : A.RegularMyersonICIRCandidateProfileSplitAssumptions) :
    A.RegularMyersonICIRAnalyticAssumptions :=
  RegularMyersonICIRAnalyticAssumptions.of_environment_candidateProfileSplitAssumptions
    (RegularMyersonICIREnvironmentAssumptions.of_primitives hind hAC hdens hvirt)
    hcand

/-! ### Projections from the analytic package -/

/-- Projection: the auction environment has independent type priors. -/
theorem RegularMyersonICIRAnalyticAssumptions.hasIndependentTypePriors
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.HasIndependentTypePriors :=
  h.independent_type_priors

/-- Projection: the environment-level envelope/virtual-surplus assumptions. -/
theorem RegularMyersonICIRAnalyticAssumptions.envelopeEnvironment
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.EnvelopeVirtualSurplusEnvironmentAssumptions :=
  h.envelope_environment

/-- Projection: CDFs are absolutely continuous on support. -/
theorem RegularMyersonICIRAnalyticAssumptions.cdf_absolutelyContinuous
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) (i : I) :
    AbsolutelyContinuousOnInterval (A.typeData.cdf i).cdf 0 (A.typeData.omega i) :=
  h.envelopeEnvironment.cdf_absolutelyContinuous i

/-- Projection: densities are positive on support. -/
theorem RegularMyersonICIRAnalyticAssumptions.positiveDensityOnSupport
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.HasPositiveDensityOnSupport :=
  h.envelopeEnvironment.positive_density_on_support

/-- Projection: candidate profile-split integrability package. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_profileSplitIntegrabilityAssumptions
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.ProfileSplitIntegrabilityAssumptions B :=
  h.candidate_profileSplit_integrability B hfeas hIC hIR

/-- Projection: candidate payment profile-split integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_profileSplit_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).payment_integrable

/-- Projection: candidate virtual-surplus profile-split integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_virtual_surplus_profileSplit_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).virtual_surplus_integrable

/-- Projection: each one-dimensional type measure is a probability measure. -/
theorem RegularMyersonICIRAnalyticAssumptions.typeMeasure_isProbabilityMeasure
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) (i : I) :
    IsProbabilityMeasure (A.typeMeasure i) :=
  h.envelopeEnvironment.typeMeasure_isProbabilityMeasure i

/-- Projection: each type density is a.e. nonnegative on its support interval. -/
theorem RegularMyersonICIRAnalyticAssumptions.typeDensity_nonnegative_ae
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) (i : I) :
    ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
      0 ≤ A.typeDensity i v :=
  h.envelopeEnvironment.typeDensity_nonnegative_ae i

/-- Projection: each virtual-value function is integrable under its type measure. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualValue_integrable_on_typeMeasure
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) (i : I) :
    Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.envelopeEnvironment.virtualValue_integrable_on_typeMeasure i

/-- Projection: all virtual-value functions are integrable under type measures. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualValue_integrable_all
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    ∀ i : I, Integrable (A.virtualValue i) (A.typeMeasure i) :=
  h.envelopeEnvironment.virtualValue_integrable_all

/-- Projection: candidate payment integrability as a one-dimensional density integral. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_density_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) :=
  (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).payment_density_integrable
    h.typeDensity_nonnegative_ae

/-- Projection: candidate virtual-surplus integrability as a density integral. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_interim_virtual_surplus_density_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) :=
  (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).virtual_surplus_density_integrable
    h.typeDensity_nonnegative_ae

/-- Projection: the envelope survival term is interval-integrable. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (_hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (_hIR : B.IsIndividuallyRationalOnSupport) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))
        volume 0 (A.typeData.omega i) := by
  intro i
  exact (B.hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible
    hIC i 0 (A.typeData.omega i)).mul_continuousOn
      (continuousOn_const.sub (h.cdf_absolutelyContinuous i).continuousOn)

/-- Projection: build the envelope/virtual-surplus analytic package for a candidate. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_envelope_analytic
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
  A.EnvelopeVirtualSurplusAnalyticAssumptions B :=
  envelopeVirtualSurplusAnalyticAssumptions_of_environment
    h.envelopeEnvironment
    (fun i => B.hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible
      hIC i 0 (A.typeData.omega i))
    (h.candidate_allocation_survival_integrable B hfeas hIC hIR)
    (h.candidate_interim_virtual_surplus_density_integrable B hfeas hIC hIR)

/-- Projection: build type-measure Fubini hypotheses for a candidate. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_typeMeasure_interim_fubini
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B := by
  haveI : ∀ i : I, IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).toTypeMeasureInterimFubini
    h.typeDensity_nonnegative_ae h.hasIndependentTypePriors henv

/-- Projection: convert type-measure Fubini to the prior-level interim package. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_interim_fubini
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.InterimFubiniAnalyticAssumptions B :=
  (h.candidate_typeMeasure_interim_fubini B henv hfeas hIC hIR).toInterimFubini

/-- Projection: feasible IC/IR candidates have integrable virtual surplus. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_integrableVirtualSurplus
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.IntegrableVirtualSurplus B.allocationRule := by
  haveI : ∀ i : I, IsProbabilityMeasure (A.typeMeasure i) :=
    h.typeMeasure_isProbabilityMeasure
  exact (h.candidate_profileSplitIntegrabilityAssumptions B hfeas hIC hIR).integrableVirtualSurplus
    h.hasIndependentTypePriors henv

/-- Upgrade a same-environment feasible IC/IR candidate to the packaged
integrable candidate class used in MSZ 12.59. -/
theorem RegularMyersonICIRAnalyticAssumptions.toIsFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (B : BayesianSingleItemAuction I)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.IsFeasibleICIRIntegrable B :=
  ⟨henv, hfeas, hIC, hIR,
    h.candidate_integrableVirtualSurplus B henv hfeas hIC hIR⟩

/-- Projection: packaged feasible IC/IR candidates have profile-split integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_profileSplitIntegrabilityAssumptions_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.ProfileSplitIntegrabilityAssumptions B :=
  h.candidate_profileSplitIntegrabilityAssumptions B
    hB.isFeasible hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: packaged feasible IC/IR candidates have payment profile-split
integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_profileSplit_integrable_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.paymentRule (reportProfile i p.1 p.2) i)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  (h.candidate_profileSplitIntegrabilityAssumptions_of_isFeasibleICIRIntegrable hB)
    |>.payment_integrable

/-- Projection: packaged feasible IC/IR candidates have virtual-surplus
profile-split integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_virtual_surplus_profileSplit_integrable_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    ∀ i : I,
      Integrable
        (fun p : ℝ × OpponentTypeProfile I i =>
          B.allocationRule (reportProfile i p.1 p.2) i * A.virtualValue i p.1)
        ((A.typeMeasure i).prod (B.opponentPrior i)) :=
  (h.candidate_profileSplitIntegrabilityAssumptions_of_isFeasibleICIRIntegrable hB)
    |>.virtual_surplus_integrable

/-- Projection: packaged feasible IC/IR candidates have payment density
integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_density_integrable_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) :=
  h.candidate_payment_density_integrable B
    hB.isFeasible hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: packaged feasible IC/IR candidates have interim virtual-surplus
density integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_interim_virtual_surplus_density_integrable_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v)
        volume 0 (A.typeData.omega i) :=
  h.candidate_interim_virtual_surplus_density_integrable B
    hB.isFeasible hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: packaged feasible IC/IR candidates have envelope survival-term
integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_allocation_survival_integrable_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    ∀ i : I,
      IntervalIntegrable
        (fun v => B.interimAllocProb i v * (1 - (A.typeData.cdf i).cdf v))
        volume 0 (A.typeData.omega i) :=
  h.candidate_allocation_survival_integrable B
    hB.isFeasible hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: packaged feasible IC/IR candidates have envelope analytics. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_envelope_analytic_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.EnvelopeVirtualSurplusAnalyticAssumptions B :=
  envelopeVirtualSurplusAnalyticAssumptions_of_environment
    h.envelopeEnvironment
    (fun i => B.hasIntervalIntegrableInterimAllocation_of_isIncentiveCompatible
      hB.isIncentiveCompatible i 0 (A.typeData.omega i))
    (h.candidate_allocation_survival_integrable_of_isFeasibleICIRIntegrable hB)
    (h.candidate_interim_virtual_surplus_density_integrable_of_isFeasibleICIRIntegrable hB)

/-- Projection: packaged feasible IC/IR candidates satisfy type-measure Fubini. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_typeMeasure_interim_fubini_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.TypeMeasureInterimFubiniAnalyticAssumptions B :=
  h.candidate_typeMeasure_interim_fubini B hB.hasSameSellingEnvironment
    hB.isFeasible hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: packaged feasible IC/IR candidates satisfy interim Fubini. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_interim_fubini_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.InterimFubiniAnalyticAssumptions B :=
  (h.candidate_typeMeasure_interim_fubini_of_isFeasibleICIRIntegrable hB).toInterimFubini

/-- Expected seller-revenue optimality among candidates. -/
def IsExpectedSellerRevenueOptimalInEnvironmentAmong [Fintype I]
    (A B : BayesianSingleItemAuction I)
    (Candidate : BayesianSingleItemAuction I → Prop) : Prop :=
  Candidate B ∧
    ∀ C, Candidate C →
      A.expectedSellerRevenueInEnvironment C ≤
        A.expectedSellerRevenueInEnvironment B

/-- A candidate with the same expected seller revenue as an optimal candidate is
also expected-revenue optimal. -/
theorem IsExpectedSellerRevenueOptimalInEnvironmentAmong.of_revenue_eq
    [Fintype I] {A B D : BayesianSingleItemAuction I}
    {Candidate : BayesianSingleItemAuction I → Prop}
    (hopt : A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B Candidate)
    (hD : Candidate D)
    (heq :
      A.expectedSellerRevenueInEnvironment B =
        A.expectedSellerRevenueInEnvironment D) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong D Candidate := by
  constructor
  · exact hD
  · intro C hC
    exact (hopt.2 C hC).trans_eq heq

/-- Extract that the chosen auction belongs to the candidate class. -/
theorem IsExpectedSellerRevenueOptimalInEnvironmentAmong.candidate
    [Fintype I] {A B : BayesianSingleItemAuction I}
    {Candidate : BayesianSingleItemAuction I → Prop}
    (hopt : A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B Candidate) :
    Candidate B :=
  hopt.1

/-- Extract the expected-revenue comparison against any candidate. -/
theorem IsExpectedSellerRevenueOptimalInEnvironmentAmong.expectedSellerRevenue_le
    [Fintype I] {A B C : BayesianSingleItemAuction I}
    {Candidate : BayesianSingleItemAuction I → Prop}
    (hopt : A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B Candidate)
    (hC : Candidate C) :
    A.expectedSellerRevenueInEnvironment C ≤
      A.expectedSellerRevenueInEnvironment B :=
  hopt.2 C hC

/-- Regular Myerson optimality among feasible IC/IR mechanisms. -/
def IsRegularMyersonOptimalICIRAuction [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop :=
  A.IsVirtualSurplusOptimalAllocationRule B.allocationRule ∧
    B.IsFeasible ∧
      B.IsIncentiveCompatible ∧
        B.IsIndividuallyRationalOnSupport ∧
      A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B
        (fun C => A.IsFeasibleICIRIntegrable C)

/-- Assemble regular-Myerson optimality from allocation optimality, feasible
IC/IR integrability, and expected-revenue optimality. -/
theorem IsFeasibleICIRIntegrable.toIsRegularMyersonOptimalICIRAuction
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsFeasibleICIRIntegrable B)
    (halloc : A.IsVirtualSurplusOptimalAllocationRule B.allocationRule)
    (hrevenue :
      A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B
        (fun C => A.IsFeasibleICIRIntegrable C)) :
    A.IsRegularMyersonOptimalICIRAuction B :=
  ⟨halloc, hB.isFeasible, hB.isIncentiveCompatible,
    hB.isIndividuallyRationalOnSupport, hrevenue⟩

/-- Extract the virtual-surplus optimal allocation component of regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isVirtualSurplusOptimalAllocationRule
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    A.IsVirtualSurplusOptimalAllocationRule B.allocationRule :=
  hB.1

/-- Extract feasibility from regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isFeasible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    B.IsFeasible :=
  hB.2.1

/-- Extract interim incentive compatibility from regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isIncentiveCompatible
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    B.IsIncentiveCompatible :=
  hB.2.2.1

/-- Extract supportwise interim IR from regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isIndividuallyRationalOnSupport
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    B.IsIndividuallyRationalOnSupport :=
  hB.2.2.2.1

/-- Extract expected-revenue optimality among feasible IC/IR candidates from
regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isExpectedSellerRevenueOptimal
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong B
      (fun C => A.IsFeasibleICIRIntegrable C) :=
  hB.2.2.2.2

/-- Extract the packaged feasible IC/IR integrable candidate component from
regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.isFeasibleICIRIntegrable
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    A.IsFeasibleICIRIntegrable B :=
  hB.isExpectedSellerRevenueOptimal.candidate

/-- Extract same-environment compatibility from regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.hasSameSellingEnvironment
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    A.HasSameSellingEnvironment B :=
  hB.isFeasibleICIRIntegrable.hasSameSellingEnvironment

/-- Extract virtual-surplus integrability from regular Myerson optimality. -/
theorem IsRegularMyersonOptimalICIRAuction.integrableVirtualSurplus
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B) :
    A.IntegrableVirtualSurplus B.allocationRule :=
  hB.isFeasibleICIRIntegrable.integrableVirtualSurplus

/-- Extract the expected-revenue comparison against any feasible IC/IR candidate. -/
theorem IsRegularMyersonOptimalICIRAuction.expectedSellerRevenue_le
    [Fintype I] {A B C : BayesianSingleItemAuction I}
    (hB : A.IsRegularMyersonOptimalICIRAuction B)
    (hC : A.IsFeasibleICIRIntegrable C) :
    A.expectedSellerRevenueInEnvironment C ≤
      A.expectedSellerRevenueInEnvironment B :=
  hB.isExpectedSellerRevenueOptimal.expectedSellerRevenue_le hC

/-- Virtual-surplus comparison gives revenue comparison under identity. -/
theorem expectedSellerRevenueInEnvironment_le_of_expectedVirtualSurplus_le
    [Fintype I] (A : BayesianSingleItemAuction I)
    {B C : BayesianSingleItemAuction I}
    (hB : A.HasExpectedRevenueVirtualSurplusIdentity B)
    (hC : A.HasExpectedRevenueVirtualSurplusIdentity C)
    (hvs :
      A.expectedVirtualSurplus B.allocationRule ≤
        A.expectedVirtualSurplus C.allocationRule) :
    A.expectedSellerRevenueInEnvironment B ≤
      A.expectedSellerRevenueInEnvironment C := by
  rw [hB, hC]
  exact hvs

/-- Revenue/virtual-surplus identity implies the corresponding one-sided upper bound. -/
theorem hasExpectedRevenueVirtualSurplusUpperBound_of_identity
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hB : A.HasExpectedRevenueVirtualSurplusIdentity B) :
    A.HasExpectedRevenueVirtualSurplusUpperBound B := by
  dsimp [HasExpectedRevenueVirtualSurplusUpperBound]
  exact le_of_eq hB

/-- For a DSIC zero-normalized single-parameter auction, the payment rule is
the Myerson payment associated with its allocation rule. -/
theorem paymentRule_eq_myersonPayment_of_isDSIC_of_isZeroNormalized
    [Fintype I] [DecidableEq I]
    (B : BayesianSingleItemAuction I)
    (hdsic : B.IsDSIC)
    (hzero : B.IsZeroNormalized) :
    B.paymentRule = SingleParameterMechanism.myersonPayment B.allocationRule :=
  SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized
    (x := B.allocationRule) (p := B.paymentRule) hdsic hzero

/-- Under DSIC and zero normalization, expected seller revenue equals the
environmental revenue computed with Myerson payments. -/
theorem expectedSellerRevenueInEnvironment_eq_myersonPaymentRevenueInEnvironment_of_isDSIC_of_isZeroNormalized
    [Fintype I] [DecidableEq I]
    (A B : BayesianSingleItemAuction I)
    (hdsic : B.IsDSIC)
    (hzero : B.IsZeroNormalized) :
    A.expectedSellerRevenueInEnvironment B =
      A.myersonPaymentRevenueInEnvironment B := by
  have hpay :
      B.paymentRule = SingleParameterMechanism.myersonPayment B.allocationRule :=
    B.paymentRule_eq_myersonPayment_of_isDSIC_of_isZeroNormalized hdsic hzero
  simp [expectedSellerRevenueInEnvironment, myersonPaymentRevenueInEnvironment, hpay]

/-- Convert the Myerson-payment revenue/virtual-surplus identity into the
ordinary expected-revenue/virtual-surplus identity under DSIC and zero normalization. -/
theorem hasExpectedRevenueVirtualSurplusIdentity_of_myersonPaymentIdentity_of_isDSIC_of_isZeroNormalized
    [Fintype I] [DecidableEq I]
    (A B : BayesianSingleItemAuction I)
    (hmyerson : A.HasMyersonPaymentRevenueVirtualSurplusIdentity B)
    (hdsic : B.IsDSIC)
    (hzero : B.IsZeroNormalized) :
    A.HasExpectedRevenueVirtualSurplusIdentity B := by
  dsimp [HasExpectedRevenueVirtualSurplusIdentity]
  rw [
    A.expectedSellerRevenueInEnvironment_eq_myersonPaymentRevenueInEnvironment_of_isDSIC_of_isZeroNormalized
      B hdsic hzero]
  exact hmyerson

/-- Interim revenue identity plus an interim payment/virtual-surplus upper
bound gives an ex-ante revenue/virtual-surplus upper bound. -/
theorem hasExpectedRevenueVirtualSurplusUpperBound_of_interim_identities
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hrev : A.HasExpectedRevenueInterimPaymentIdentity B)
    (hvs : A.HasExpectedVirtualSurplusInterimIdentity B)
    (hupper : A.HasInterimPaymentVirtualSurplusUpperBound B) :
    A.HasExpectedRevenueVirtualSurplusUpperBound B := by
  dsimp [
    HasExpectedRevenueVirtualSurplusUpperBound,
    HasExpectedRevenueInterimPaymentIdentity,
    HasExpectedVirtualSurplusInterimIdentity,
    HasInterimPaymentVirtualSurplusUpperBound,
    expectedInterimPaymentRevenue,
    expectedInterimVirtualSurplus] at *
  rw [hrev, hvs]
  exact Finset.sum_le_sum fun i _ => hupper i

/-- Bidder-wise equality of interim payment and virtual-surplus integrals gives
the ex-ante revenue/virtual-surplus identity. -/
theorem hasExpectedRevenueVirtualSurplusIdentity_of_interim_identities
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hrev : A.HasExpectedRevenueInterimPaymentIdentity B)
    (hvs : A.HasExpectedVirtualSurplusInterimIdentity B)
    (hid : ∀ i : I,
      (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v) :
    A.HasExpectedRevenueVirtualSurplusIdentity B := by
  dsimp [
    HasExpectedRevenueVirtualSurplusIdentity,
    HasExpectedRevenueInterimPaymentIdentity,
    HasExpectedVirtualSurplusInterimIdentity,
    expectedInterimPaymentRevenue,
    expectedInterimVirtualSurplus] at *
  rw [hrev, hvs]
  exact Finset.sum_congr rfl fun i _ => hid i

/-- Combine an interim payment/envelope upper bound with an envelope/virtual-surplus
upper bound. -/
theorem hasInterimPaymentVirtualSurplusUpperBound_of_envelope_upper
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hpay : A.HasInterimPaymentEnvelopeUpperBound B)
    (henv : A.HasEnvelopeVirtualSurplusUpperBound B) :
    A.HasInterimPaymentVirtualSurplusUpperBound B := by
  intro i
  exact le_trans (hpay i) (henv i)

/-- Zero normalization and the interim payment formula identify interim payments
with the envelope expression after integration against the base density. -/
theorem hasInterimPaymentEnvelopeIdentity_of_zeroNormalized_of_interimPaymentFormula
    [Fintype I] [DecidableEq I] (A B : BayesianSingleItemAuction I)
    (hzero : B.IsZeroNormalized)
    (hpay_formula : B.HasInterimPaymentFormula) :
    ∀ i : I,
      (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          (B.interimAllocProb i v * v -
            ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
  intro i
  have hM0 : B.interimExpectedPayment i 0 = 0 :=
    B.interimExpectedPayment_zero_of_isZeroNormalized hzero i
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with v _hv
  have hpay := hpay_formula i v
  rw [hM0] at hpay
  calc
    B.interimExpectedPayment i v * A.typeDensity i v
        = (B.interimAllocProb i v * v -
            ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v := by
          rw [hpay]
          ring

/-- Under the envelope analytic assumptions, the zero-normalized interim payment
formula identifies expected interim payments with interim virtual surplus. -/
theorem hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula
    [Fintype I] [DecidableEq I] (A B : BayesianSingleItemAuction I)
    (hzero : B.IsZeroNormalized)
    (hpay_formula : B.HasInterimPaymentFormula)
    (henv :
      A.EnvelopeVirtualSurplusAnalyticAssumptions B) :
    ∀ i : I,
      (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
  intro i
  calc
    (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v)
        = ∫ v in 0..A.typeData.omega i,
            (B.interimAllocProb i v * v -
              ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v :=
          A.hasInterimPaymentEnvelopeIdentity_of_zeroNormalized_of_interimPaymentFormula
            B hzero hpay_formula i
    _ = ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v :=
          henv.envelopeIntegral_eq_virtualSurplusIntegral i

/-- A pointwise envelope upper bound integrates to an interim payment/envelope
upper bound under nonnegative densities. -/
theorem hasInterimPaymentEnvelopeUpperBound_of_pointwise
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hint_pay :
      ∀ i : I,
        IntervalIntegrable
          (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hint_env :
      ∀ i : I,
        IntervalIntegrable
          (fun v =>
            (B.interimAllocProb i v * v -
              ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hpoint :
      ∀ (i : I) (v : ℝ),
        0 ≤ v →
          v ≤ A.typeData.omega i →
            B.interimExpectedPayment i v ≤
              B.interimAllocProb i v * v -
                ∫ z in 0..v, B.interimAllocProb i z) :
    A.HasInterimPaymentEnvelopeUpperBound B := by
  intro i
  have hae :
      (fun v : ℝ => B.interimExpectedPayment i v * A.typeDensity i v)
        ≤ᵐ[volume.restrict (Set.Ioc 0 (A.typeData.omega i))]
      (fun v : ℝ =>
        (B.interimAllocProb i v * v -
          ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hdens_ae i] with v hv hdens_v
    exact mul_le_mul_of_nonneg_right (hpoint i v hv.1.le hv.2) hdens_v
  rw [intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg,
    intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg]
  exact setIntegral_mono_ae_restrict (hint_pay i).1 (hint_env i).1 hae

/-- IC and supportwise IR supply the pointwise envelope upper bound, hence the
integrated interim payment/envelope upper bound. -/
theorem hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hint_pay :
      ∀ i : I,
        IntervalIntegrable
          (fun v => B.interimExpectedPayment i v * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hint_env :
      ∀ i : I,
        IntervalIntegrable
          (fun v =>
            (B.interimAllocProb i v * v -
              ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v)
          volume 0 (A.typeData.omega i))
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.HasInterimPaymentEnvelopeUpperBound B :=
  A.hasInterimPaymentEnvelopeUpperBound_of_pointwise B hdens_ae hint_pay hint_env
    (fun i v _h0 _homega =>
      BayesianSingleItemAuction.interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
        B hIC hIR i v)

/-! ### Revenue-identity projections from the analytic package -/

/-- Projection: feasible IC/IR candidates satisfy the interim payment/envelope upper bound. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_envelope_upper
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.HasInterimPaymentEnvelopeUpperBound B :=
  A.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    B h.typeDensity_nonnegative_ae
    (h.candidate_payment_density_integrable B hfeas hIC hIR)
    (fun i =>
      (h.candidate_envelope_analytic B hfeas hIC hIR).envelope_density_integrable i)
    hIC hIR

/-- Projection: packaged feasible IC/IR candidates satisfy the payment envelope upper bound. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_payment_envelope_upper_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.HasInterimPaymentEnvelopeUpperBound B :=
  A.hasInterimPaymentEnvelopeUpperBound_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    B h.typeDensity_nonnegative_ae
    (h.candidate_payment_density_integrable_of_isFeasibleICIRIntegrable hB)
    (fun i =>
      (h.candidate_envelope_analytic_of_isFeasibleICIRIntegrable hB).envelope_density_integrable i)
    hB.isIncentiveCompatible hB.isIndividuallyRationalOnSupport

/-- Projection: ex-ante revenue equals interim payment for same-environment candidates. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_revenue_interim_identity
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.HasExpectedRevenueInterimPaymentIdentity B :=
  (h.candidate_interim_fubini B henv hfeas hIC hIR)
    |>.hasExpectedRevenueInterimPaymentIdentity

/-- Projection: packaged feasible IC/IR candidates identify revenue with interim payment. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_revenue_interim_identity_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.HasExpectedRevenueInterimPaymentIdentity B :=
  (h.candidate_interim_fubini_of_isFeasibleICIRIntegrable hB)
    |>.hasExpectedRevenueInterimPaymentIdentity

/-- Projection: ex-ante virtual surplus equals the interim virtual-surplus expression. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_virtual_surplus_interim_identity
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.HasExpectedVirtualSurplusInterimIdentity B :=
  (h.candidate_interim_fubini B henv hfeas hIC hIR)
    |>.hasExpectedVirtualSurplusInterimIdentity

/-- Projection: packaged feasible IC/IR candidates identify virtual surplus with
the interim expression. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_virtual_surplus_interim_identity_of_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.HasExpectedVirtualSurplusInterimIdentity B :=
  (h.candidate_interim_fubini_of_isFeasibleICIRIntegrable hB)
    |>.hasExpectedVirtualSurplusInterimIdentity

/-- Revenue-comparable candidates are revenue-upper-bounded candidates. -/
theorem isRevenueUpperBounded_of_isRevenueComparable
    [Fintype I] (A B : BayesianSingleItemAuction I)
    (hB : A.IsRevenueComparable B) :
    A.IsRevenueUpperBounded B :=
  ⟨hB.hasSameSellingEnvironment,
    hB.isFeasible,
    hB.integrableVirtualSurplus,
    A.hasExpectedRevenueVirtualSurplusUpperBound_of_identity B
      hB.expectedRevenueVirtualSurplusIdentity⟩

/-- Feasible IC/IR integrable candidates satisfy the one-sided revenue upper
bound under the regular Myerson analytic assumptions. -/
theorem isRevenueUpperBounded_of_ic_ir_upper
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A B : BayesianSingleItemAuction I)
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.IsRevenueUpperBounded B := by
  exact ⟨hB.hasSameSellingEnvironment, hB.isFeasible, hB.integrableVirtualSurplus,
    A.hasExpectedRevenueVirtualSurplusUpperBound_of_interim_identities B
      (h.candidate_revenue_interim_identity_of_isFeasibleICIRIntegrable hB)
      (h.candidate_virtual_surplus_interim_identity_of_isFeasibleICIRIntegrable hB)
      (A.hasInterimPaymentVirtualSurplusUpperBound_of_envelope_upper B
        (h.candidate_payment_envelope_upper_of_isFeasibleICIRIntegrable hB)
      (A.hasEnvelopeVirtualSurplusUpperBound_of_analyticAssumptions B
          (h.candidate_envelope_analytic_of_isFeasibleICIRIntegrable hB)))⟩

/-- Projection: under the regular Myerson analytic assumptions, every packaged
feasible IC/IR candidate is revenue-upper-bounded by virtual surplus. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_isRevenueUpperBounded
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.IsRevenueUpperBounded B :=
  A.isRevenueUpperBounded_of_ic_ir_upper B h hB

/-- Projection: same-environment feasible IC/IR candidates are
revenue-upper-bounded once the analytic package supplies integrability. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_isRevenueUpperBounded_of_sameEnvironment_of_isFeasibleICIR
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.IsRevenueUpperBounded B :=
  h.candidate_isRevenueUpperBounded
    (h.toIsFeasibleICIRIntegrable B henv hfeas hIC hIR)

/-- Projection: every packaged feasible IC/IR candidate has seller revenue
bounded above by its expected virtual surplus. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_expectedVirtualSurplus
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.expectedSellerRevenueInEnvironment B ≤ A.expectedVirtualSurplus B.allocationRule :=
  (h.candidate_isRevenueUpperBounded hB).expectedRevenueVirtualSurplusUpperBound

/-- Projection: the raw same-environment feasible IC/IR assumptions already
imply the seller-revenue/virtual-surplus upper bound. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_expectedVirtualSurplus_of_sameEnvironment_of_isFeasibleICIR
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.expectedSellerRevenueInEnvironment B <= A.expectedVirtualSurplus B.allocationRule :=
  (h.candidate_isRevenueUpperBounded_of_sameEnvironment_of_isFeasibleICIR
    henv hfeas hIC hIR).expectedRevenueVirtualSurplusUpperBound

/-- A DSIC zero-normalized candidate with the Myerson-payment revenue identity
is revenue-comparable. -/
theorem isRevenueComparable_of_myersonPaymentIdentity_of_isDSIC_of_isZeroNormalized
    [Fintype I] [DecidableEq I]
    (A B : BayesianSingleItemAuction I)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hint : A.IntegrableVirtualSurplus B.allocationRule)
    (hmyerson : A.HasMyersonPaymentRevenueVirtualSurplusIdentity B)
    (hdsic : B.IsDSIC)
    (hzero : B.IsZeroNormalized) :
    A.IsRevenueComparable B :=
  ⟨henv, hfeas, hint,
    A.hasExpectedRevenueVirtualSurplusIdentity_of_myersonPaymentIdentity_of_isDSIC_of_isZeroNormalized
      B hmyerson hdsic hzero⟩

/-- A revenue-comparable candidate has expected seller revenue at most the
virtual-surplus-maximizing auction. -/
theorem expectedSellerRevenueInEnvironment_le_virtualSurplusMaximizingAuction
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A B : BayesianSingleItemAuction I)
    (hB : A.IsRevenueComparable B)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.expectedSellerRevenueInEnvironment B ≤
      A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction := by
  exact A.expectedSellerRevenueInEnvironment_le_of_expectedVirtualSurplus_le
    hB.expectedRevenueVirtualSurplusIdentity hopt_id
    (A.expectedVirtualSurplus_le_virtualSurplusMaximizingAuction_allocationRule
      (x := B.allocationRule)
      hB.isFeasible.isSingleItemAllocationRule
      hB.integrableVirtualSurplus
      hopt_int)

/-- A revenue-upper-bounded candidate has expected seller revenue at most the
virtual-surplus-maximizing auction. -/
theorem expectedSellerRevenueInEnvironment_le_virtualSurplusMaximizingAuction_of_revenueUpperBounded
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A B : BayesianSingleItemAuction I)
    (hB : A.IsRevenueUpperBounded B)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.expectedSellerRevenueInEnvironment B ≤
      A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction := by
  calc
    A.expectedSellerRevenueInEnvironment B
        ≤ A.expectedVirtualSurplus B.allocationRule :=
          hB.expectedRevenueVirtualSurplusUpperBound
    _ ≤ A.expectedVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule :=
        A.expectedVirtualSurplus_le_virtualSurplusMaximizingAuction_allocationRule
          (x := B.allocationRule)
          hB.isFeasible.isSingleItemAllocationRule
          hB.integrableVirtualSurplus
          hopt_int
    _ = A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction := by
        exact hopt_id.symm

/-- The virtual-surplus-maximizing auction is revenue-comparable once its
revenue/virtual-surplus identity and integrability are available. -/
theorem virtualSurplusMaximizingAuction_isRevenueComparable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.IsRevenueComparable A.virtualSurplusMaximizingAuction :=
  ⟨A.virtualSurplusMaximizingAuction_hasSameSellingEnvironment,
    A.virtualSurplusMaximizingAuction_isFeasible, hopt_int, hopt_id⟩

/-- The virtual-surplus-maximizing auction is revenue-upper-bounded once its
revenue/virtual-surplus identity and integrability are available. -/
theorem virtualSurplusMaximizingAuction_isRevenueUpperBounded
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.IsRevenueUpperBounded A.virtualSurplusMaximizingAuction :=
  A.isRevenueUpperBounded_of_isRevenueComparable
    A.virtualSurplusMaximizingAuction
    (A.virtualSurplusMaximizingAuction_isRevenueComparable hopt_int hopt_id)

/-- Regularity gives interim incentive compatibility for the lifted
virtual-surplus-maximizing auction. -/
theorem virtualSurplusMaximizingAuction_isIncentiveCompatible_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    (A.virtualSurplusMaximizingAuction).IsIncentiveCompatible := by
  have hint : A.virtualSurplusMaximizingAuction.HasIntegrableInterimObjects :=
    A.virtualSurplusMaximizingAuction_hasIntegrableInterimObjects_of_isRegular hA
  exact A.virtualSurplusMaximizingAuction.isIncentiveCompatible_of_isDSIC
    hint (A.virtualSurplusMaximizingAuction_isDSIC_of_isRegular hA)

/-- Zero normalization plus the envelope formula gives supportwise interim IR for
the virtual-surplus-maximizing auction. -/
theorem virtualSurplusMaximizingAuction_isIndividuallyRationalOnSupport
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (henv : A.virtualSurplusMaximizingAuction.HasInterimEnvelopeFormula)
    (hint_nonneg :
      A.virtualSurplusMaximizingAuction.HasNonnegativeInterimAllocationIntegralOnSupport) :
    (A.virtualSurplusMaximizingAuction).IsIndividuallyRationalOnSupport :=
  A.virtualSurplusMaximizingAuction
    |>.isIndividuallyRationalOnSupport_of_isZeroNormalized_of_hasInterimEnvelopeFormula
      A.virtualSurplusMaximizingAuction_isZeroNormalized henv hint_nonneg

/-- MSZ 12.58: regular Myerson is IC and IR. -/
theorem virtualSurplusMaximizingAuction_isIncentiveCompatible_and_individuallyRationalOnSupport_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    (A.virtualSurplusMaximizingAuction).IsIncentiveCompatible ∧
      (A.virtualSurplusMaximizingAuction).IsIndividuallyRationalOnSupport := by
  have hIC :
      (A.virtualSurplusMaximizingAuction).IsIncentiveCompatible :=
    A.virtualSurplusMaximizingAuction_isIncentiveCompatible_of_isRegular hA
  have henv :
      A.virtualSurplusMaximizingAuction.HasInterimEnvelopeFormula :=
    A.virtualSurplusMaximizingAuction.hasInterimEnvelopeFormula_of_isIncentiveCompatible hIC
  have hint_nonneg :
      A.virtualSurplusMaximizingAuction.HasNonnegativeInterimAllocationIntegralOnSupport :=
    A.virtualSurplusMaximizingAuction
      |>.hasNonnegativeInterimAllocationIntegralOnSupport_of_isFeasible
        A.virtualSurplusMaximizingAuction_isFeasible
  exact ⟨
    hIC,
    A.virtualSurplusMaximizingAuction_isIndividuallyRationalOnSupport henv hint_nonneg⟩

/-- IR half of MSZ 12.58. -/
theorem virtualSurplusMaximizingAuction_isIndividuallyRationalOnSupport_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    (A.virtualSurplusMaximizingAuction).IsIndividuallyRationalOnSupport :=
  (A.virtualSurplusMaximizingAuction_isIncentiveCompatible_and_individuallyRationalOnSupport_of_isRegular
    hA).2

/-- Method-style projection: the regular Myerson auction is a feasible IC/IR
integrable candidate. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.IsFeasibleICIRIntegrable A.virtualSurplusMaximizingAuction := by
  have hICIR :
      (A.virtualSurplusMaximizingAuction).IsIncentiveCompatible ∧
        (A.virtualSurplusMaximizingAuction).IsIndividuallyRationalOnSupport :=
    A.virtualSurplusMaximizingAuction_isIncentiveCompatible_and_individuallyRationalOnSupport_of_isRegular
      hA
  exact h.toIsFeasibleICIRIntegrable
    A.virtualSurplusMaximizingAuction
    A.virtualSurplusMaximizingAuction_hasSameSellingEnvironment
    A.virtualSurplusMaximizingAuction_isFeasible
    hICIR.1
    hICIR.2

/-- The virtual-surplus-maximizing auction satisfies the revenue/virtual-surplus identity. -/
theorem RegularMyersonICIRAnalyticAssumptions.opt_identity
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction := by
  have hcand :
      A.IsFeasibleICIRIntegrable A.virtualSurplusMaximizingAuction :=
    h.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable hA
  have hrev :
      A.HasExpectedRevenueInterimPaymentIdentity A.virtualSurplusMaximizingAuction :=
    h.candidate_revenue_interim_identity_of_isFeasibleICIRIntegrable hcand
  have hvs :
      A.HasExpectedVirtualSurplusInterimIdentity A.virtualSurplusMaximizingAuction :=
    h.candidate_virtual_surplus_interim_identity_of_isFeasibleICIRIntegrable hcand
  have hpay_formula :
    A.virtualSurplusMaximizingAuction.HasInterimPaymentFormula :=
    A.virtualSurplusMaximizingAuction.hasInterimPaymentFormula_of_isIncentiveCompatible
      hcand.isIncentiveCompatible
  have hanalytic :
      A.EnvelopeVirtualSurplusAnalyticAssumptions A.virtualSurplusMaximizingAuction :=
    h.candidate_envelope_analytic_of_isFeasibleICIRIntegrable hcand
  exact
    A.hasExpectedRevenueVirtualSurplusIdentity_of_interim_identities
      A.virtualSurplusMaximizingAuction
      hrev
      hvs
      (A.hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula
        A.virtualSurplusMaximizingAuction
        A.virtualSurplusMaximizingAuction_isZeroNormalized
        hpay_formula
        hanalytic)

/-- Method-style projection: the virtual-surplus-maximizing auction satisfies
the expected-revenue/expected-virtual-surplus identity. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_expectedRevenueVirtualSurplusIdentity
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction :=
  h.opt_identity hA

/-- Method-style projection: the virtual-surplus-maximizing auction has
integrable virtual surplus under the regular Myerson analytic assumptions. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_integrableVirtualSurplus
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule :=
  (h.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable hA).integrableVirtualSurplus

/-- Method-style projection: the virtual-surplus-maximizing auction is
revenue-comparable under the regular Myerson analytic assumptions. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_isRevenueComparable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.IsRevenueComparable A.virtualSurplusMaximizingAuction :=
  A.virtualSurplusMaximizingAuction_isRevenueComparable
    (h.virtualSurplusMaximizingAuction_integrableVirtualSurplus hA)
    (h.virtualSurplusMaximizingAuction_expectedRevenueVirtualSurplusIdentity hA)

/-- Method-style projection: the virtual-surplus-maximizing auction is
revenue-upper-bounded under the regular Myerson analytic assumptions. -/
theorem RegularMyersonICIRAnalyticAssumptions.virtualSurplusMaximizingAuction_isRevenueUpperBounded
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular) :
    A.IsRevenueUpperBounded A.virtualSurplusMaximizingAuction :=
  A.virtualSurplusMaximizingAuction_isRevenueUpperBounded
    (h.virtualSurplusMaximizingAuction_integrableVirtualSurplus hA)
    (h.virtualSurplusMaximizingAuction_expectedRevenueVirtualSurplusIdentity hA)

/-- The regular Myerson auction is a feasible IC/IR integrable candidate. -/
theorem virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.IsFeasibleICIRIntegrable A.virtualSurplusMaximizingAuction :=
  h.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable hA

/-- Revenue optimality among revenue-comparable candidates. -/
theorem virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongRevenueComparable
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      A.virtualSurplusMaximizingAuction
      (fun B => A.IsRevenueComparable B) := by
  constructor
  · exact A.virtualSurplusMaximizingAuction_isRevenueComparable hopt_int hopt_id
  · intro B hB
    exact A.expectedSellerRevenueInEnvironment_le_virtualSurplusMaximizingAuction
      B hB hopt_int hopt_id

/-- Revenue optimality under the one-sided revenue upper bound. -/
theorem virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongRevenueUpperBounded
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I)
    (hopt_int :
      A.IntegrableVirtualSurplus (A.virtualSurplusMaximizingAuction).allocationRule)
    (hopt_id :
      A.HasExpectedRevenueVirtualSurplusIdentity A.virtualSurplusMaximizingAuction) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      A.virtualSurplusMaximizingAuction
      (fun B => A.IsRevenueUpperBounded B) := by
  constructor
  · exact A.virtualSurplusMaximizingAuction_isRevenueUpperBounded hopt_int hopt_id
  · intro B hB
    exact
      A.expectedSellerRevenueInEnvironment_le_virtualSurplusMaximizingAuction_of_revenueUpperBounded
        B hB hopt_int hopt_id

/-- Projection: under regularity, any packaged feasible IC/IR candidate earns at
most the virtual-surplus-maximizing auction. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular)
    (hB : A.IsFeasibleICIRIntegrable B) :
    A.expectedSellerRevenueInEnvironment B ≤
      A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction := by
  exact
    A.expectedSellerRevenueInEnvironment_le_virtualSurplusMaximizingAuction_of_revenueUpperBounded
      B
      (h.candidate_isRevenueUpperBounded hB)
      (h.virtualSurplusMaximizingAuction_integrableVirtualSurplus hA)
      (h.virtualSurplusMaximizingAuction_expectedRevenueVirtualSurplusIdentity hA)

/-- Projection: a raw same-environment feasible IC/IR candidate earns at most
the virtual-surplus-maximizing auction under regularity. -/
theorem RegularMyersonICIRAnalyticAssumptions.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular_of_sameEnvironment_of_isFeasibleICIR
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    {A B : BayesianSingleItemAuction I}
    (h : A.RegularMyersonICIRAnalyticAssumptions)
    (hA : A.IsRegular)
    (henv : A.HasSameSellingEnvironment B)
    (hfeas : B.IsFeasible)
    (hIC : B.IsIncentiveCompatible)
    (hIR : B.IsIndividuallyRationalOnSupport) :
    A.expectedSellerRevenueInEnvironment B <=
      A.expectedSellerRevenueInEnvironment A.virtualSurplusMaximizingAuction :=
  h.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular hA
    (h.toIsFeasibleICIRIntegrable B henv hfeas hIC hIR)

/-- MSZ 12.59: revenue optimality among IC/IR candidates. -/
theorem virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.IsExpectedSellerRevenueOptimalInEnvironmentAmong
      A.virtualSurplusMaximizingAuction
      (fun B => A.IsFeasibleICIRIntegrable B) := by
  have hcand :
      A.IsFeasibleICIRIntegrable A.virtualSurplusMaximizingAuction :=
    h.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable hA
  constructor
  · exact hcand
  · intro B hB
    exact h.candidate_expectedSellerRevenue_le_virtualSurplusMaximizingAuction_of_isRegular hA hB

/-- MSZ 12.59 compact theorem. -/
theorem virtualSurplusMaximizingAuction_regularMyersonOptimalICIR_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular)
    (h : A.RegularMyersonICIRAnalyticAssumptions) :
    A.IsRegularMyersonOptimalICIRAuction A.virtualSurplusMaximizingAuction := by
  have hcand :
      A.IsFeasibleICIRIntegrable A.virtualSurplusMaximizingAuction :=
    h.virtualSurplusMaximizingAuction_isFeasibleICIRIntegrable hA
  exact hcand.toIsRegularMyersonOptimalICIRAuction
    A.virtualSurplusMaximizingAuction_allocationRule_isVirtualSurplusOptimal
    (A.virtualSurplusMaximizingAuction_isExpectedSellerRevenueOptimalInEnvironmentAmongFeasibleICIRIntegrable_of_isRegular
      hA h)

end RevenueOptimalityInterface

end BayesianSingleItemAuction
