/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.OpenProblem.New.RevenueOptimalDSICAuction.Problem

/-!
# RevenueOptimalDSICAuction: supporting material

Auxiliary definitions and lemmas for the problem statement.
-/

section

/-!
## Revenue-optimal multi-bidder DSIC auctions

[WJP24, Section 2] uses bidder-specific report domains, independent bidder priors,
feasible allocation lotteries, and risk-neutral utility. Item values within a bidder
may be correlated. The type domains are distinct from the support and need not be full
boxes. Continuity conventions are kept separate: vector atomlessness does not imply a
multidimensional density. Payments are nonnegative conditional expectations; IR is
before the allocation lottery.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- Both valuation classes have a uniform finite bound on every admissible bundle. -/
theorem AuctionEnvironment.bundleValue_le {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (i : Fin bidders)
    (v : ItemValues items) (hv : v ∈ E.typeDomain i) (S : Finset (Fin items)) :
    bundleValue E.valuationClass v S ≤ (items + 1 : ℕ) * E.valueMax := by
  have coord := fun j => (E.domain_bounded i v hv j).2
  have hcard : S.card ≤ items := by simpa using Finset.card_le_univ S
  cases E.valuationClass with
  | additive =>
      simp only [bundleValue]
      calc
        ∑ j ∈ S, v j ≤ ∑ _j ∈ S, E.valueMax :=
          Finset.sum_le_sum fun j _ => coord j
        _ = (S.card : ℝ) * E.valueMax := by simp
        _ ≤ (items + 1 : ℕ) * E.valueMax :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard.trans (Nat.le_succ items))
            E.valueMax_nonnegative
  | unitDemand =>
      simp only [bundleValue]
      split_ifs with hS
      · calc
          S.sup' hS v ≤ E.valueMax := Finset.sup'_le _ _ fun j _ => coord j
          _ ≤ (items + 1 : ℕ) * E.valueMax := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (show (1 : ℝ) ≤ (items + 1 : ℕ) by exact_mod_cast Nat.succ_pos items)
                E.valueMax_nonnegative
      · exact mul_nonneg (Nat.cast_nonneg _) E.valueMax_nonnegative

/-- A full-dimensional density cannot concentrate any item value at a fixed constant. -/
theorem AuctionEnvironment.bidderDensity_coordinate_null {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (h : E.HasContinuousPrior .bidderDensity)
    (i : Fin bidders) (j : Fin items) (c : ℝ) :
    (E.prior.map (fun v => v i)) {v | v j = c} = 0 := by
  exact h i (Measure.pi_hyperplane (fun _ : Fin items => (volume : Measure ℝ)) j c)

/-- IR bounds every admissible payment; no integrability assumption is added. -/
theorem RandomizedAuction.payment_le_of_isIR {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items)
    (hIR : A.IsIR E) (v : ValueProfile bidders items)
    (hv : E.IsAdmissibleProfile v) (i : Fin bidders) :
    A.payment v i ≤ (items + 1 : ℕ) * E.valueMax := by
  have hu := hIR v hv i
  have hb : Lottery.expectedValue (A.allocation v)
      (fun allocation => bundleValue E.valuationClass (v i) (assignedBundle allocation i)) ≤
      (items + 1 : ℕ) * E.valueMax := by
    calc
      _ ≤ Lottery.expectedValue (A.allocation v)
          (fun _ => (items + 1 : ℕ) * E.valueMax) :=
        Lottery.expectedValue_mono fun allocation =>
          E.bundleValue_le i (v i) (hv i) (assignedBundle allocation i)
      _ = _ := Lottery.expectedValue_const _ _
  exact (le_of_sub_nonneg hu).trans hb

/-- Bounded reports, IR and measurability make each payment integrable under the prior. -/
theorem RandomizedAuction.payment_integrable_of_isIR {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items)
    (hIR : A.IsIR E) (i : Fin bidders) :
    Integrable (fun v => A.payment v i) E.prior := by
  letI : IsProbabilityMeasure E.prior := E.probability
  refine (integrable_const ((items + 1 : ℕ) * E.valueMax)).mono'
    (A.payment_measurable i).aestronglyMeasurable ?_
  filter_upwards [E.supported] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (A.payment_nonnegative v i)]
  exact A.payment_le_of_isIR E hIR v hv i

/-- Expected revenue uses a genuine integrable sum, never the nonintegrable default. -/
theorem RandomizedAuction.revenue_integrable_of_isIR {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items)
    (hIR : A.IsIR E) :
    Integrable (fun v => ∑ i, A.payment v i) E.prior := by
  exact integrable_finsetSum _ fun i _ => A.payment_integrable_of_isIR E hIR i

/-- Nonnegative transfers give nonnegative expected revenue. -/
theorem expectedRevenue_nonnegative {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) :
    0 ≤ expectedRevenue E A := by
  exact integral_nonneg fun v => Finset.sum_nonneg fun i _ => A.payment_nonnegative v i

end
end EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

end


section

/-!
## Certifying an explicit optimal-auction candidate

Both research routes require a concrete prior, at least two bidders and two items, and
exact global revenue optimality. No polynomial learning bound is stated. An answer
must supply its mathematical environment and auction; an existence proof alone does
not supply an explicit formula or learned network. The reference witness requires
multidimensional density, excluding diagonal single-parameter priors. We retain
broader continuity variants explicitly.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

/-- Existence for one environment in the chosen valuation class. -/
def RevenueOptimalDSICAuctionStatement
    (kind : AuctionValuationClass) (continuity : ContinuityConvention) : Prop :=
  ∃ bidders items : ℕ, ∃ E : AuctionEnvironment bidders items,
    E.valuationClass = kind ∧ ∃ A : RandomizedAuction bidders items,
      RevenueOptimalDSICAuctionQuestion continuity E A

/-- Existence of a reference-domain answer is weaker than explicitly exhibiting one. -/
def ReferenceRevenueOptimalAuctionStatement (kind : AuctionValuationClass) : Prop :=
  ∃ answer : AuctionAnswer,
    answer.environment.valuationClass = kind ∧ answer.IsCorrect

end EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

end
