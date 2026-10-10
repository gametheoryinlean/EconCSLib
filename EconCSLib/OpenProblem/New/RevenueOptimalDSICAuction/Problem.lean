/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic

/-!
# 21. Revenue-optimal DSIC auctions
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

/-- Additive and unit-demand classes are separate; a misreport cannot change the class. -/
inductive AuctionValuationClass where
  | additive
  | unitDemand
  deriving DecidableEq

/-- Singleton-value vectors; their bounds are imposed by the environment. -/
abbrev ItemValues (items : ℕ) := Fin items → ℝ

/-- Value/report profiles, with admissibility checked by the environment. -/
abbrev ValueProfile (bidders items : ℕ) := Fin bidders → ItemValues items

/-- Additive bundle value is a sum; unit-demand value is a maximum, zero on the empty
bundle. -/
def bundleValue {items : ℕ} (kind : AuctionValuationClass)
    (v : ItemValues items) (S : Finset (Fin items)) : ℝ :=
  match kind with
  | .additive => ∑ j ∈ S, v j
  | .unitDemand => if h : S.Nonempty then S.sup' h v else 0

/-- Every item has one owner or is unsold; a buyer may receive multiple items. -/
abbrev AuctionAllocation (bidders items : ℕ) := Fin items → Option (Fin bidders)

/-- The bundle assigned to a bidder by an owner function. -/
def assignedBundle {bidders items : ℕ}
    (A : AuctionAllocation bidders items) (i : Fin bidders) : Finset (Fin items) :=
  Finset.univ.filter (fun j => A j = some i)

/-- A known-prior environment with measurable bounded bidder-specific domains. Neither
full support, positive density, nor item independence is imposed here. -/
structure AuctionEnvironment (bidders items : ℕ) where
  valuationClass : AuctionValuationClass
  valueMax : ℝ
  valueMax_nonnegative : 0 ≤ valueMax
  typeDomain : Fin bidders → Set (ItemValues items)
  domain_measurable : ∀ i, MeasurableSet (typeDomain i)
  domain_bounded : ∀ i v, v ∈ typeDomain i → ∀ j, v j ∈ Set.Icc 0 valueMax
  prior : Measure (ValueProfile bidders items)
  probability : IsProbabilityMeasure prior
  independent : iIndepFun (fun i (v : ValueProfile bidders items) => v i) prior
  supported : ∀ᵐ v ∂prior, ∀ i, v i ∈ typeDomain i

/-- Every coordinate lies in its published report domain. -/
def AuctionEnvironment.IsAdmissibleProfile {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (v : ValueProfile bidders items) : Prop :=
  ∀ i, v i ∈ E.typeDomain i

/-- Distinct continuity notions. `bidderDensity` is absolute continuity with respect to
multidimensional Lebesgue measure, without item independence. -/
inductive ContinuityConvention where
  | bidderAtomless
  | coordinateAtomless
  | bidderDensity
  deriving DecidableEq

/-- Continuity is imposed separately on every bidder marginal. -/
def AuctionEnvironment.HasContinuousPrior {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (mode : ContinuityConvention) : Prop :=
  match mode with
  | .bidderAtomless =>
      ∀ i : Fin bidders, NoAtoms (E.prior.map (fun v => v i))
  | .coordinateAtomless =>
      ∀ (i : Fin bidders) (j : Fin items),
        NoAtoms (E.prior.map (fun v => v i j))
  | .bidderDensity =>
      ∀ i : Fin bidders,
        (E.prior.map (fun v => v i)) ≪
          Measure.pi (fun _ : Fin items => (volume : Measure ℝ))

/-- A direct auction on the common report space. Full allocation lotteries preserve
correlations relevant to unit-demand utility. -/
structure RandomizedAuction (bidders items : ℕ) where
  allocation : ValueProfile bidders items → Lottery ℝ (AuctionAllocation bidders items)
  payment : ValueProfile bidders items → Fin bidders → ℝ
  allocation_measurable : ∀ A, Measurable (fun b => (allocation b).val A)
  payment_measurable : ∀ i, Measurable (fun b => payment b i)
  payment_nonnegative : ∀ b i, 0 ≤ payment b i

/-- The true valuation is fixed under deviations; expectation is only over the allocation
lottery. -/
def RandomizedAuction.utility {bidders items : ℕ}
    (A : RandomizedAuction bidders items) (kind : AuctionValuationClass)
    (trueValue : ItemValues items) (reports : ValueProfile bidders items)
    (i : Fin bidders) : ℝ :=
  Lottery.expectedValue (A.allocation reports)
    (fun allocation => bundleValue kind trueValue (assignedBundle allocation i)) -
      A.payment reports i

/-- Exact DSIC for all admissible opponent reports, not BIC or grid-only truthfulness. -/
def RandomizedAuction.IsDSIC {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  ∀ truth, E.IsAdmissibleProfile truth → ∀ i fake, fake ∈ E.typeDomain i →
    A.utility E.valuationClass (truth i) (Function.update truth i fake) i ≤
      A.utility E.valuationClass (truth i) truth i

/-- IR for every admissible profile before the allocation lottery, with zero outside
option. -/
def RandomizedAuction.IsIR {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  ∀ truth, E.IsAdmissibleProfile truth → ∀ i,
    0 ≤ A.utility E.valuationClass (truth i) truth i

/-- Expected revenue under the specified prior, not empirical revenue or welfare. -/
def expectedRevenue {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : ℝ :=
  ∫ values, (∑ i, A.payment values i) ∂E.prior

/-- The comparison class contains every DSIC and IR auction. IR bounds nonnegative
payments by the bounded bundle values, ensuring integrability. -/
def IsAdmissibleAuction {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  A.IsDSIC E ∧ A.IsIR E

/-- The candidate must attain global optimum against all admissible allocation lotteries. -/
def IsRevenueOptimal {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  IsAdmissibleAuction E A ∧
    ∀ other : RandomizedAuction bidders items, IsAdmissibleAuction E other →
      expectedRevenue E other ≤ expectedRevenue E A

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

/-- The mathematical correctness contract for a supplied candidate under a stated
continuity convention. -/
def RevenueOptimalDSICAuctionQuestion {bidders items : ℕ}
    (continuity : ContinuityConvention)
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  1 < bidders ∧ 1 < items ∧ E.HasContinuousPrior continuity ∧ IsRevenueOptimal E A

/-- The reference witness has a genuinely multidimensional continuous prior. Absolute
continuity excludes point masses and diagonal single-parameter priors; it does not
impose independent item values or a positive density everywhere. -/
def ReferenceRevenueOptimalAuctionQuestion {bidders items : ℕ}
    (E : AuctionEnvironment bidders items) (A : RandomizedAuction bidders items) : Prop :=
  0 < E.valueMax ∧ RevenueOptimalDSICAuctionQuestion .bidderDensity E A

/-- Mathematical data supplied by either the computational or characterization route. A
submission must also exhibit the formula or learned representation, rather than merely
obtaining these functions from an abstract existence theorem. -/
structure AuctionAnswer where
  bidders : ℕ
  items : ℕ
  environment : AuctionEnvironment bidders items
  auction : RandomizedAuction bidders items

/-- Exact feasibility, truthfulness, IR, and global optimality for a supplied answer. -/
def AuctionAnswer.IsCorrect (answer : AuctionAnswer) : Prop :=
  ReferenceRevenueOptimalAuctionQuestion answer.environment answer.auction

end EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction

/-- Exhibit a concrete genuinely multidimensional continuous environment and its optimal
auction. -/
theorem revenueOptimalDSICAuction :
    AuctionAnswer.IsCorrect (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.RevenueOptimalDSICAuction
