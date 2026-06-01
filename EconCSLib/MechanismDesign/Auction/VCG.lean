/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.MechanismDesign.Auction.Transfer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# EconCSLib.MechanismDesign.Auction.VCG

Multiple-parameter mechanisms for VCG-style mechanism design.

This file builds the VCG mechanism as a specialization of the
multiple-parameter transfer-mechanism layer from `MechanismDesign.Auction.Transfer`.

The transfer layer keeps utility external to the mechanism.  A mechanism stores
only an allocation rule and a payment rule; quasi-linear DSIC and ex-post IR are
then stated through `MechanismWithTransfers.isQuasiLinearDSIC` and
`MechanismWithTransfers.isQuasiLinearExPostIR`.

In the multiple-parameter VCG setting, agent `i`'s type/report is a valuation
function `A → ℝ` on the allocation space.  The VCG allocation maximizes reported
social welfare, and the Clarke-pivot payment charges each agent the externality
imposed on the other agents.

## Structure hierarchy

```
MechanismWithTransfers I (fun _ => A → ℝ) A ℝ     -- valuation reports over A
  └─ MultipleParameterMechanism I A ℝ ℝ           -- named multiple-parameter layer
       └─ VCGMechanism                            -- efficient allocation + Clarke payments

VCGTransferMechanism                              -- same rule viewed as MechanismWithTransfers
```
-/

namespace MultipleParameterMechanism

section vcg

open scoped BigOperators

variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]

/-- Reported social welfare of allocation `a` under a profile of valuations. -/
def socialWelfare (v : ∀ _ : I, Valuation A ℝ) (a : A) : ℝ :=
  ∑ i, v i a

/-- The maximum reported social welfare over all allocations. -/
noncomputable def maxSocialWelfare (v : ∀ _ : I, Valuation A ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (socialWelfare v)

/-- There exists an allocation maximizing reported social welfare. -/
lemma exists_efficientAllocation (v : ∀ _ : I, Valuation A ℝ) :
    ∃ a : A, ∀ b : A, socialWelfare v b ≤ socialWelfare v a := by
  classical
  obtain ⟨a, _ha_mem, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset A))
      (H := Finset.univ_nonempty) (f := socialWelfare v)
  refine ⟨a, ?_⟩
  intro b
  have hb : socialWelfare v b ≤ maxSocialWelfare v := by
    exact Finset.le_sup' (socialWelfare v) (Finset.mem_univ b)
  simpa [maxSocialWelfare, ha] using hb

/-- A welfare-maximizing allocation, chosen noncomputably from finite `A`. -/
noncomputable def efficientAllocation (v : ∀ _ : I, Valuation A ℝ) : A :=
  Classical.choose (exists_efficientAllocation v)

/-- The chosen VCG allocation maximizes reported social welfare. -/
lemma efficientAllocation_isOptimal (v : ∀ _ : I, Valuation A ℝ) (a : A) :
    socialWelfare v a ≤ socialWelfare v (efficientAllocation v) :=
  Classical.choose_spec (exists_efficientAllocation v) a

variable [DecidableEq I]

/-- Reported social welfare of all agents except `i`. -/
def welfareWithout (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) : ℝ :=
  (Finset.univ.erase i).sum fun j => v j a

omit [Fintype A] [Nonempty A] in
/-- Social welfare decomposes into agent `i`'s value plus the welfare of the
other agents. -/
lemma socialWelfare_eq_value_add_welfareWithout
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) :
    socialWelfare v a = v i a + welfareWithout v i a := by
  rw [socialWelfare, welfareWithout]
  exact (Finset.add_sum_erase Finset.univ (fun j => v j a) (Finset.mem_univ i)).symm

omit [Fintype A] [Nonempty A] in
/-- If all valuations are nonnegative, then the welfare of agents other than
`i` is bounded by total social welfare. -/
lemma welfareWithout_le_socialWelfare
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) (a : A) :
    welfareWithout v i a ≤ socialWelfare v a := by
  rw [socialWelfare, welfareWithout]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset i Finset.univ)
    (fun j _ _ => hnonneg j a)

omit [Fintype A] [Nonempty A] in
/-- If agent `i`'s valuation is nonnegative, then the welfare of agents other
than `i` is bounded by total social welfare. -/
lemma welfareWithout_le_socialWelfare_of_nonneg_i
    (v : ∀ _ : I, Valuation A ℝ)
    (i : I) (hi_nonneg : ∀ a : A, 0 ≤ v i a) (a : A) :
    welfareWithout v i a ≤ socialWelfare v a := by
  have hdecomp := socialWelfare_eq_value_add_welfareWithout v i a
  have hi := hi_nonneg a
  linarith

omit [Fintype A] [Nonempty A] in
/-- Changing agent `i`'s report does not change the welfare of agents other
than `i`. -/
lemma welfareWithout_update_self
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (report : Valuation A ℝ) (a : A) :
    welfareWithout (Function.update v i report) i a = welfareWithout v i a := by
  rw [welfareWithout, welfareWithout]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    simpa using hj
  simp [Function.update, hji]

/-- The maximum reported welfare of agents other than `i`. -/
noncomputable def maxWelfareWithout (v : ∀ _ : I, Valuation A ℝ) (i : I) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (welfareWithout v i)

/-- Changing agent `i`'s report does not change the maximum welfare achievable
by the other agents. -/
lemma maxWelfareWithout_update_self
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (report : Valuation A ℝ) :
    maxWelfareWithout (Function.update v i report) i = maxWelfareWithout v i := by
  rw [maxWelfareWithout, maxWelfareWithout]
  exact Finset.sup'_congr Finset.univ_nonempty rfl
    (fun a _ => welfareWithout_update_self v i report a)

/-- There exists an allocation maximizing the reported welfare of agents other
than `i`. -/
lemma exists_withoutAllocation (v : ∀ _ : I, Valuation A ℝ) (i : I) :
    ∃ a : A, ∀ b : A, welfareWithout v i b ≤ welfareWithout v i a := by
  classical
  obtain ⟨a, _ha_mem, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset A))
      (H := Finset.univ_nonempty) (f := welfareWithout v i)
  refine ⟨a, ?_⟩
  intro b
  have hb : welfareWithout v i b ≤ maxWelfareWithout v i := by
    exact Finset.le_sup' (welfareWithout v i) (Finset.mem_univ b)
  simpa [maxWelfareWithout, ha] using hb

/-- A welfare-maximizing allocation for agents other than `i`. -/
noncomputable def withoutAllocation (v : ∀ _ : I, Valuation A ℝ) (i : I) : A :=
  Classical.choose (exists_withoutAllocation v i)

/-- The chosen allocation without agent `i` maximizes the reported welfare of
the other agents. -/
lemma withoutAllocation_isOptimal (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) :
    welfareWithout v i a ≤ welfareWithout v i (withoutAllocation v i) :=
  Classical.choose_spec (exists_withoutAllocation v i) a

/-- The Clarke-pivot VCG payment charged to agent `i`: the best welfare that
the other agents could get without `i`, minus the other agents' welfare at the
efficient allocation chosen from all reports. -/
noncomputable def vcgPayment (v : ∀ _ : I, Valuation A ℝ) (i : I) : ℝ :=
  maxWelfareWithout v i - welfareWithout v i (efficientAllocation v)

/-- The finite-allocation VCG mechanism induced by welfare maximization and
Clarke-pivot payments. -/
noncomputable def VCGMechanism : MultipleParameterMechanism I A ℝ ℝ where
  allocationRule := efficientAllocation
  paymentRule := vcgPayment

/-- The underlying transfer mechanism of `VCGMechanism`.

This is the object to which the generic definitions in `Transfer.lean`, such as
`isQuasiLinearDSIC` and `isQuasiLinearExPostIR`, are applied. -/
noncomputable def VCGTransferMechanism :
    MechanismWithTransfers I (fun _ => Valuation A ℝ) A ℝ where
  allocationRule := (VCGMechanism : MultipleParameterMechanism I A ℝ ℝ).allocationRule
  paymentRule := (VCGMechanism : MultipleParameterMechanism I A ℝ ℝ).paymentRule

/-- VCG utility can be rewritten as total welfare under the profile that uses
agent `i`'s true valuation and keeps all other reports fixed, minus the maximal
welfare achievable by the other agents alone. -/
lemma VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout
    (reports trueTypes : ∀ _ : I, Valuation A ℝ) (i : I) :
    MechanismWithTransfers.quasiLinearUtility
        VCGTransferMechanism valueOfAllocation id id reports trueTypes i =
      socialWelfare (Function.update reports i (trueTypes i)) (efficientAllocation reports) -
        maxWelfareWithout reports i := by
  let aStar := efficientAllocation reports
  have hdecomp :
      socialWelfare (Function.update reports i (trueTypes i)) aStar =
        trueTypes i aStar + welfareWithout reports i aStar := by
    simpa [Function.update, welfareWithout_update_self reports i (trueTypes i) aStar] using
      socialWelfare_eq_value_add_welfareWithout
        (Function.update reports i (trueTypes i)) i aStar
  simp [MechanismWithTransfers.quasiLinearUtility, valueOfAllocation,
    VCGTransferMechanism, VCGMechanism, vcgPayment]
  dsimp [aStar] at hdecomp
  linarith

/-- If agent `i` reports truthfully in the VCG mechanism, then their
quasi-linear utility is nonnegative against arbitrary reports by the other
agents, assuming `i`'s true valuation is nonnegative. -/
theorem VCGMechanism_truthful_quasiLinearUtility_nonneg
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) (r : ∀ _ : I, Valuation A ℝ) :
    0 ≤ MechanismWithTransfers.quasiLinearUtility
      VCGTransferMechanism valueOfAllocation id id (Function.update r i (v i)) v i := by
  let reports := Function.update r i (v i)
  let aStar := efficientAllocation reports
  have hi_nonneg : ∀ a : A, 0 ≤ reports i a := by
    intro a
    simp [reports, hnonneg i a]
  have hmax_le :
      maxWelfareWithout reports i ≤ socialWelfare reports aStar := by
    rw [maxWelfareWithout]
    exact Finset.sup'_le Finset.univ_nonempty (welfareWithout reports i)
      (fun a _ =>
        le_trans (welfareWithout_le_socialWelfare_of_nonneg_i reports i hi_nonneg a)
          (efficientAllocation_isOptimal reports a))
  have hdecomp :
      socialWelfare reports aStar = reports i aStar + welfareWithout reports i aStar :=
    socialWelfare_eq_value_add_welfareWithout reports i aStar
  have hreport_i : reports i aStar = v i aStar := by
    simp [reports]
  simp [MechanismWithTransfers.quasiLinearUtility, valueOfAllocation,
    VCGTransferMechanism, VCGMechanism, vcgPayment]
  dsimp [reports, aStar] at hmax_le hdecomp hreport_i
  linarith

/-- The same nonnegative-utility result for the fully truthful report profile. -/
theorem VCGMechanism_truthful_profile_quasiLinearUtility_nonneg
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) :
    0 ≤ MechanismWithTransfers.quasiLinearUtility
      VCGTransferMechanism valueOfAllocation id id v v i := by
  simpa [Function.update_eq_self] using
    VCGMechanism_truthful_quasiLinearUtility_nonneg (v := v) hnonneg i v

/-- VCG satisfies the `MechanismWithTransfers.isExPostIR` predicate under the
ambient assumption that every valuation in the unrestricted type space is
nonnegative. For concrete domains, this assumption is usually enforced by
choosing a nonnegative valuation subtype. -/
theorem VCGMechanism_isExPostIR_of_all_nonnegative
    (hnonneg :
      ∀ v : (∀ _ : I, Valuation A ℝ), ∀ i : I, ∀ a : A, 0 ≤ v i a) :
    MechanismWithTransfers.isQuasiLinearExPostIR
      (M := (VCGTransferMechanism :
        MechanismWithTransfers I (fun _ => Valuation A ℝ) A ℝ))
      valueOfAllocation id id := by
  intro trueTypes i r
  simpa [MechanismWithTransfers.quasiLinearUtility, MechanismWithTransfers.isQuasiLinearExPostIR,
    valueOfAllocation, VCGTransferMechanism, VCGMechanism] using
    VCGMechanism_truthful_quasiLinearUtility_nonneg
      (v := trueTypes) (hnonneg trueTypes) i r

/-- The finite-allocation VCG mechanism is dominant-strategy incentive
compatible for quasi-linear utilities.

The final arguments `id id` instantiate the two conversion maps in
`MechanismWithTransfers.isQuasiLinearDSIC`:

* `valueToUtility : ℝ → ℝ`, converting valuation values to utilities;
* `paymentToUtility : ℝ → ℝ`, converting payments to utilities.

For VCG, values, payments, and utilities all live in `ℝ`, so both conversions
are the identity map. -/
theorem VCGMechanism_isDSIC :
    MechanismWithTransfers.isQuasiLinearDSIC
      (M := (VCGTransferMechanism :
        MechanismWithTransfers I (fun _ => Valuation A ℝ) A ℝ))
      valueOfAllocation id id := by
  intro trueTypes i
  unfold IsWeaklyDominant WeaklyDominates
  intro s' reports
  let truthfulReports : ∀ _ : I, Valuation A ℝ := Function.update reports i (trueTypes i)
  let deviatingReports : ∀ _ : I, Valuation A ℝ := Function.update reports i s'
  have hopt :
      socialWelfare truthfulReports (efficientAllocation deviatingReports) ≤
        socialWelfare truthfulReports (efficientAllocation truthfulReports) :=
    efficientAllocation_isOptimal truthfulReports (efficientAllocation deviatingReports)
  have hdevUtility :
      MechanismWithTransfers.quasiLinearUtility
          VCGTransferMechanism valueOfAllocation id id deviatingReports trueTypes i =
        socialWelfare truthfulReports (efficientAllocation deviatingReports) -
          maxWelfareWithout reports i := by
    rw [VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout]
    have hreports : Function.update deviatingReports i (trueTypes i) = truthfulReports := by
      funext j
      by_cases hji : j = i <;> simp [truthfulReports, deviatingReports, Function.update, hji]
    have hmax : maxWelfareWithout deviatingReports i = maxWelfareWithout reports i := by
      simpa [deviatingReports] using maxWelfareWithout_update_self reports i s'
    rw [hreports, hmax]
  have htruthUtility :
      MechanismWithTransfers.quasiLinearUtility
          VCGTransferMechanism valueOfAllocation id id truthfulReports trueTypes i =
        socialWelfare truthfulReports (efficientAllocation truthfulReports) -
          maxWelfareWithout reports i := by
    rw [VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout]
    have hreports : Function.update truthfulReports i (trueTypes i) = truthfulReports := by
      funext j
      by_cases hji : j = i <;> simp [truthfulReports, Function.update, hji]
    have hmax : maxWelfareWithout truthfulReports i = maxWelfareWithout reports i := by
      simpa [truthfulReports] using maxWelfareWithout_update_self reports i (trueTypes i)
    rw [hreports, hmax]
  change
    MechanismWithTransfers.quasiLinearUtility
        VCGTransferMechanism valueOfAllocation id id deviatingReports trueTypes i ≤
      MechanismWithTransfers.quasiLinearUtility
        VCGTransferMechanism valueOfAllocation id id truthfulReports trueTypes i
  rw [hdevUtility, htruthUtility]
  linarith

end vcg

end MultipleParameterMechanism
