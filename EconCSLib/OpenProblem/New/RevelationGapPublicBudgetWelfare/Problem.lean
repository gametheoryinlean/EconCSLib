/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Foundation.Utility.Lottery
import EconCSLib.MechanismDesign.Auction.MechBayesian
import EconCSLib.OpenProblem.Util.Answer
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# 20. The public-budget welfare revelation gap
-/



section

/-!
## Welfare with a common public budget

[FH18, Definition 2.1 and Section 5] distinguishes the priors used to assess
performance from those on which the fixed mechanism must be truthful. Values lie in a
bounded interval, payments are nonnegative and hard-budget feasible. Random
allocations and deterministic conditional expected payments represent risk-neutral
outcomes, without imposing outcome-by-outcome IR.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- A bounded nonnegative value prior, allowing atoms and a zero upper bound. -/
structure PublicBudgetDistribution where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  supportUpper : ℝ
  supportUpper_nonnegative : 0 ≤ supportUpper
  supported : measure (Set.Icc 0 supportUpper) = 1

/-- Public-budget welfare regularity means a concave CDF [FH18, Definition 2.1], not
monotone revenue virtual value. -/
def PublicBudgetDistribution.IsRegular (F : PublicBudgetDistribution) : Prop :=
  ConcaveOn ℝ (Set.Icc 0 F.supportUpper)
    (fun v => (F.measure (Set.Iic v)).toReal)

/-- Independent coordinates with a common distribution. -/
def iidValueProfileMeasure (F : PublicBudgetDistribution) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  letI : IsProbabilityMeasure F.measure := F.probability
  Measure.pi (fun _ : Fin n => F.measure)

/-- A fixed allocation/payment rule. Total allocation probability is at most one; prior
independence belongs to the quantified family, not this outcome type. -/
structure PublicBudgetOutcome (n : ℕ) where
  allocation : (Fin n → ℝ) → Fin n → ℝ
  payment : (Fin n → ℝ) → Fin n → ℝ
  allocation_mem : ∀ reports i,
    0 ≤ allocation reports i ∧ allocation reports i ≤ 1
  feasible : ∀ reports, ∑ i, allocation reports i ≤ 1
  payment_nonnegative : ∀ reports i, 0 ≤ payment reports i
  allocation_measurable : ∀ i, Measurable (fun reports => allocation reports i)
  payment_measurable : ∀ i, Measurable (fun reports => payment reports i)

/-- Expected social welfare. -/
def PublicBudgetOutcome.expectedWelfare {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetDistribution) : ℝ :=
  ∫ values, (∑ i, values i * A.allocation values i)
    ∂iidValueProfileMeasure F n

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## Separate revenue and position-environment questions

Welfare regularity is not revenue regularity [FH18, Definition 2.1]. This module
states objective-specific truthful approximation questions and a concrete
position-allocation model. The smooth revenue-regular subclass is named explicitly.
Position weights are public, and all IID truthfulness is required independently of the
class of priors used to assess performance.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Welfare and revenue are distinct objectives on the same economic outcomes. -/
inductive Objective where
  | welfare
  | revenue
  deriving DecidableEq

/-- Revenue needs at least two bidders in the no-sample, unknown-prior model [FH18,
Theorem 8.2]; welfare also admits the one-bidder case. -/
def Objective.AllowsPopulation : Objective → ℕ → Prop
  | .welfare, n => 0 < n
  | .revenue, n => 2 ≤ n

/-- The expected sum of payments; it is finite for budget-feasible mechanisms. -/
def PublicBudgetOutcome.expectedRevenue {n : ℕ} (A : PublicBudgetOutcome n)
    (F : PublicBudgetDistribution) : ℝ :=
  ∫ values, (∑ i, A.payment values i) ∂iidValueProfileMeasure F n

/-- Select the actual economic objective. -/
def PublicBudgetOutcome.expectedObjective {n : ℕ} (A : PublicBudgetOutcome n)
    (objective : Objective) (F : PublicBudgetDistribution) : ℝ :=
  match objective with
  | .welfare => A.expectedWelfare F
  | .revenue => A.expectedRevenue F

/-- The evaluation class is fixed before selecting a prior-independent family. -/
abbrev PriorClass := Set PublicBudgetDistribution

/-- Public service weights of n positions; fewer positions are padded by zero weights. -/
structure PositionEnvironment (n : ℕ) where
  weight : Fin n → ℝ
  weight_mem : ∀ j, 0 ≤ weight j ∧ weight j ≤ 1
  decreasing : Antitone weight

/-- A partial matching from positions to bidders. No bidder receives two positions. -/
abbrev PositionAssignment (n : ℕ) :=
  {owner : Fin n → Option (Fin n) //
    ∀ j k i, owner j = some i → owner k = some i → j = k}

/-- Expected service weight for a bidder, under a feasible assignment lottery. -/
def PositionEnvironment.service {n : ℕ} (E : PositionEnvironment n)
    (L : Lottery ℝ (PositionAssignment n)) (i : Fin n) : ℝ :=
  Lottery.expectedValue L (fun a => ∑ j, if a.val j = some i then E.weight j else 0)

/-- A direct position-auction outcome rule; withholding positions is allowed. -/
structure PositionOutcome (n : ℕ) where
  allocation : (Fin n → ℝ) → Lottery ℝ (PositionAssignment n)
  payment : (Fin n → ℝ) → Fin n → ℝ
  allocation_measurable : ∀ a, Measurable (fun reports => (allocation reports).val a)
  payment_measurable : ∀ i, Measurable (fun reports => payment reports i)
  payment_nonnegative : ∀ reports i, 0 ≤ payment reports i

/-- Quasilinear utility for a public position environment. -/
def PositionOutcome.utility {n : ℕ} (A : PositionOutcome n) (E : PositionEnvironment n)
    (v : ℝ) (reports : Fin n → ℝ) (i : Fin n) : ℝ :=
  v * E.service (A.allocation reports) i - A.payment reports i

/-- The hard budget holds on every report in the stated interval. -/
def PositionOutcome.IsBudgetFeasibleOn {n : ℕ} (A : PositionOutcome n) (B h : ℝ) : Prop :=
  ∀ reports, (∀ i, reports i ∈ Set.Icc 0 h) → ∀ i, A.payment reports i ≤ B

/-- Interim utility integrates only opponents' values, overwriting the own report. -/
def PositionOutcome.interimUtility {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) (F : PublicBudgetDistribution)
    (i : Fin n) (v report : ℝ) : ℝ :=
  ∫ values, A.utility E v (Function.update values i report) i
    ∂iidValueProfileMeasure F n

/-- Bayesian incentive compatibility on the whole published type interval. -/
def PositionOutcome.IsBIC {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) (F : PublicBudgetDistribution) : Prop :=
  ∀ i v report, v ∈ Set.Icc 0 F.supportUpper → report ∈ Set.Icc 0 F.supportUpper →
    A.interimUtility E F i v report ≤ A.interimUtility E F i v v

/-- Interim individual rationality with zero outside option. -/
def PositionOutcome.IsInterimIR {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) (F : PublicBudgetDistribution) : Prop :=
  ∀ i v, v ∈ Set.Icc 0 F.supportUpper → 0 ≤ A.interimUtility E F i v v

/-- A prior-informed admissible position-auction benchmark. -/
def PositionOutcome.IsBayesianAdmissible {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) (B : ℝ) (F : PublicBudgetDistribution) : Prop :=
  A.IsBudgetFeasibleOn B F.supportUpper ∧ A.IsBIC E F ∧ A.IsInterimIR E F

/-- Welfare uses the allocated service weights; revenue uses actual payments. -/
def PositionOutcome.expectedObjective {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) (objective : Objective) (F : PublicBudgetDistribution) : ℝ :=
  ∫ values, (match objective with
    | .welfare => ∑ i, values i * E.service (A.allocation values) i
    | .revenue => ∑ i, A.payment values i) ∂iidValueProfileMeasure F n

/-- Public weights and budget may be inputs; the value prior may not. -/
abbrev PositionMechanismFamily := (n : ℕ) → PositionEnvironment n → ℝ → PositionOutcome n

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## Strategic public-budget auctions and actual revelation gaps

A mechanism fixes its action space and feasible assignment/payment rules before the
prior. Bayesian strategies may use the prior, but each player's action uses only her
own value. Outcomes are actual lotteries over feasible assignments, reusing `Lottery`
and `PositionOutcome`; no supplied denotation or arbitrary equilibrium predicate
determines welfare. Every pure deviation is compared with the equilibrium action, with
integrability and interim IR explicit.

FH18 Section 2 assumes symmetric auctions. The symmetry mode is therefore a parameter
fixed before choosing either mechanism class. The reference question uses symmetric
mechanisms; it does not assume every equilibrium is symmetric. This is a
strategic-form model.
-/
namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Whether the mechanism class requires invariance under relabeling bidders. -/
inductive SymmetryMode where
  | unrestricted
  | symmetric
  deriving DecidableEq

/-- A mode is fixed externally, not selected separately by an algorithmic witness. -/
def SymmetryMode.Accepts (mode : SymmetryMode) (symmetric : Prop) : Prop :=
  match mode with
  | .unrestricted => True
  | .symmetric => symmetric

/-- Symmetry concerns service and payments, keeping the public position weights fixed. -/
def PositionOutcome.IsSymmetric {n : ℕ} (A : PositionOutcome n)
    (E : PositionEnvironment n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) reports i,
    E.service (A.allocation (reports ∘ σ)) i = E.service (A.allocation reports) (σ i) ∧
    A.payment (reports ∘ σ) i = A.payment reports (σ i)

/-- A single item is a unit-weight first position with all remaining weights zero. -/
def singleItemEnvironment (n : ℕ) : PositionEnvironment n where
  weight j := if j.val = 0 then 1 else 0
  weight_mem j := by split_ifs <;> norm_num
  decreasing := by
    intro i j hij
    by_cases hj : j.val = 0
    · have hi : i.val = 0 := Nat.eq_zero_of_le_zero (hj ▸ hij)
      simp [hi, hj]
    · simp only [hj, ↓reduceIte]
      split_ifs <;> norm_num

/-- Which public environments are included in a uniform factor. -/
inductive EnvironmentScope where
  | singleItem
  | positions
  deriving DecidableEq

/-- The single-item question fixes the above embedding; positions range over all weights. -/
def EnvironmentScope.Accepts {n : ℕ} (scope : EnvironmentScope)
    (E : PositionEnvironment n) : Prop :=
  match scope with
  | .singleItem => E = singleItemEnvironment n
  | .positions => True

/-- Selected equilibrium and guarantees robust to every admissible equilibrium differ. -/
inductive EquilibriumSelection where
  | selected
  | robust
  deriving DecidableEq

/-- Actual action-dependent feasible assignments and nonnegative payments. The common
action space allows symmetric auctions without restricting reports to bids. -/
structure StrategicPositionMechanism (n : ℕ) where
  Action : Type
  toMechanismWithTransfers :
    MechanismWithTransfers (Fin n) (fun _ => Action) (Lottery ℝ (PositionAssignment n)) ℝ
  payment_nonnegative : ∀ actions i, 0 ≤ toMechanismWithTransfers.paymentRule actions i

/-- The allocation rule is the library's native transfer-mechanism allocation. -/
abbrev StrategicPositionMechanism.allocation {n : ℕ} (M : StrategicPositionMechanism n) :=
  M.toMechanismWithTransfers.allocationRule

/-- The payment rule is the library's native transfer-mechanism payment. -/
abbrev StrategicPositionMechanism.payment {n : ℕ} (M : StrategicPositionMechanism n) :=
  M.toMechanismWithTransfers.paymentRule

/-- The hard budget holds at every action profile, including deviations. -/
def StrategicPositionMechanism.IsBudgetFeasible {n : ℕ}
    (M : StrategicPositionMechanism n) (B : ℝ) : Prop :=
  ∀ actions i, M.payment actions i ≤ B

/-- Anonymous service and payments under every bidder permutation. -/
def StrategicPositionMechanism.IsSymmetric {n : ℕ}
    (M : StrategicPositionMechanism n) (E : PositionEnvironment n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) actions i,
    E.service (M.allocation (actions ∘ σ)) i = E.service (M.allocation actions) (σ i) ∧
    M.payment (actions ∘ σ) i = M.payment actions (σ i)

/-- A common withdrawal action gives zero service and payment against every profile. -/
structure StrategicPositionMechanism.Withdrawal {n : ℕ}
    (M : StrategicPositionMechanism n) (E : PositionEnvironment n) where
  action : M.Action
  service_zero : ∀ actions i,
    E.service (M.allocation (Function.update actions i action)) i = 0
  payment_zero : ∀ actions i, M.payment (Function.update actions i action) i = 0

/-- Private-value strategies: no agent's action reads an opponent's realized value. -/
abbrev StrategicPositionMechanism.Strategy {n : ℕ} (M : StrategicPositionMechanism n) :=
  BayesianMechanism.StrategyProfile (fun _ : Fin n => ℝ) (fun _ => M.Action)

/-- Realized action profile under a strategy family. -/
def StrategicPositionMechanism.actions {n : ℕ} {M : StrategicPositionMechanism n}
    (strategy : M.Strategy) (values : Fin n → ℝ) : Fin n → M.Action :=
  BayesianMechanism.inducedMessages strategy values

/-- Conditional utility from one action against the opponents' strategies. -/
def StrategicPositionMechanism.deviationUtility {n : ℕ}
    (M : StrategicPositionMechanism n) (E : PositionEnvironment n)
    (strategy : M.Strategy) (i : Fin n) (v : ℝ) (a : M.Action)
    (values : Fin n → ℝ) : ℝ :=
  let profile := Function.update (M.actions strategy values) i a
  v * E.service (M.allocation profile) i - M.payment profile i

/-- The own value coordinate is overwritten, so only opponents' values matter. -/
def StrategicPositionMechanism.interimUtility {n : ℕ}
    (M : StrategicPositionMechanism n) (E : PositionEnvironment n)
    (F : PublicBudgetDistribution) (strategy : M.Strategy)
    (i : Fin n) (v : ℝ) (a : M.Action) : ℝ :=
  ∫ values, M.deviationUtility E strategy i v a values ∂iidValueProfileMeasure F n

/-- A measurable induced outcome with actual Bayesian deviations. The induced
allocation/payment equalities prevent a strategy from inventing welfare. IR is derived
from withdrawal, not used to discard unfavorable equilibria. Budget bounds make the
integrability condition routine for measurable deviations. -/
structure StrategicPositionEquilibrium {n : ℕ} (M : StrategicPositionMechanism n)
    (E : PositionEnvironment n) (F : PublicBudgetDistribution) where
  strategy : M.Strategy
  induced : PositionOutcome n
  allocation_eq : ∀ values, induced.allocation values = M.allocation (M.actions strategy values)
  payment_eq : ∀ values i, induced.payment values i = M.payment (M.actions strategy values) i
  deviation_integrable : ∀ i v, v ∈ Set.Icc 0 F.supportUpper → ∀ a,
    Integrable (M.deviationUtility E strategy i v a) (iidValueProfileMeasure F n)
  best_response : ∀ i v, v ∈ Set.Icc 0 F.supportUpper → ∀ a,
    M.interimUtility E F strategy i v a ≤
      M.interimUtility E F strategy i v (strategy i v)

/-- Public population, weights and budget are allowed inputs; the prior is not. -/
abbrev StrategicPositionFamily :=
  (n : ℕ) → PositionEnvironment n → ℝ → StrategicPositionMechanism n

/-- Compare a realized strategic outcome with every admissible prior-informed benchmark. -/
def StrategicPositionEquilibrium.AchievesFactor {n : ℕ}
    {M : StrategicPositionMechanism n} {E : PositionEnvironment n}
    {F : PublicBudgetDistribution} (e : StrategicPositionEquilibrium M E F)
    (mode : SymmetryMode) (objective : Objective) (B β : ℝ) : Prop :=
  ∀ A : PositionOutcome n, A.IsBayesianAdmissible E B F →
    mode.Accepts (A.IsSymmetric E) →
      A.expectedObjective E objective F ≤ β * e.induced.expectedObjective E objective F

/-- Optimal non-revelation performance in the specified, fixed strategic-form class. -/
def StrategicPositionGuarantee (scope : EnvironmentScope) (mode : SymmetryMode)
    (selection : EquilibriumSelection) (objective : Objective)
    (priors : PriorClass) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ M : StrategicPositionFamily,
    (∀ n E, scope.Accepts E → ∀ B, 0 ≤ B →
      (M n E B).IsBudgetFeasible B ∧ mode.Accepts ((M n E B).IsSymmetric E) ∧
        Nonempty ((M n E B).Withdrawal E)) ∧
    ∀ n, objective.AllowsPopulation n → ∀ E, scope.Accepts E →
      ∀ B, 0 ≤ B → ∀ F ∈ priors,
        match selection with
        | .selected => ∃ e : StrategicPositionEquilibrium (M n E B) E F,
            e.AchievesFactor mode objective B β
        | .robust => Nonempty (StrategicPositionEquilibrium (M n E B) E F) ∧
            ∀ e : StrategicPositionEquilibrium (M n E B) E F,
              e.AchievesFactor mode objective B β

/-- The truthful class uses the same symmetry and benchmark conventions. Truthfulness and
IR still hold for every bounded IID prior. -/
def SymmetryPositionTruthfulGuarantee (scope : EnvironmentScope) (mode : SymmetryMode)
    (objective : Objective) (priors : PriorClass) (β : ℝ) : Prop :=
  1 ≤ β ∧ ∃ M : PositionMechanismFamily,
    (∀ n E, scope.Accepts E → ∀ B, 0 ≤ B →
      (∀ reports, (∀ i, 0 ≤ reports i) → ∀ i, (M n E B).payment reports i ≤ B) ∧
      mode.Accepts ((M n E B).IsSymmetric E) ∧
      ∀ F : PublicBudgetDistribution, (M n E B).IsBIC E F ∧ (M n E B).IsInterimIR E F) ∧
    ∀ n, objective.AllowsPopulation n → ∀ E, scope.Accepts E →
      ∀ B, 0 ≤ B → ∀ F ∈ priors,
        ∀ A : PositionOutcome n, A.IsBayesianAdmissible E B F →
          mode.Accepts (A.IsSymmetric E) →
            A.expectedObjective E objective F ≤ β * (M n E B).expectedObjective E objective F

/-- A finite infimum is characterized without requiring an optimal mechanism to exist. -/
def IsTightStrategicFactor (guarantee : ℝ → Prop) (β : ℝ) : Prop :=
  1 ≤ β ∧ (∀ γ : ℝ, β < γ → guarantee γ) ∧
    ∀ γ : ℝ, 1 ≤ γ → γ < β → ¬ guarantee γ

/-- Both independently optimized factors and their ratio, rather than only the numerator. -/
def StrategicRevelationGapQuestion (scope : EnvironmentScope) (mode : SymmetryMode)
    (selection : EquilibriumSelection) (objective : Objective) (priors : PriorClass)
    (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  IsTightStrategicFactor (SymmetryPositionTruthfulGuarantee scope mode objective priors)
      truthfulFactor ∧
    IsTightStrategicFactor (StrategicPositionGuarantee scope mode selection objective priors)
      strategicFactor ∧ gap = truthfulFactor / strategicFactor

end
end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


section

/-!
## The truthful prior-independent public-budget welfare factor

The central question identifies the tight factor against a prior-informed Bayesian
benchmark on welfare-regular IID priors. FH18's all-pay result motivates calling this
the revelation gap; that result is not assumed as an axiom. Truthfulness on all IID
priors and only regular IID priors are separate. Revenue and position variants require
their own objectives and feasibility.
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

noncomputable section

end

/-- The literal symmetric-auction strategic-form gap, with robust equilibrium performance.
The old reference factor above remains a separately named, unrestricted-symmetry
numerator. -/
noncomputable def ReferencePublicBudgetRevelationGapQuestion
    (truthfulFactor strategicFactor gap : ℝ) : Prop :=
  StrategicRevelationGapQuestion .singleItem .symmetric .robust .welfare
    {F | F.IsRegular} truthfulFactor strategicFactor gap

/-- An answer identifies numerical factors. -/
structure PublicBudgetGapAnswer where
  truthfulFactor : ℝ
  strategicFactor : ℝ
  gap : ℝ

/-- Correctness against the explicit symmetric, robust strategic-action reference. -/
noncomputable def PublicBudgetGapAnswer.IsCorrect (answer : PublicBudgetGapAnswer) : Prop :=
  ReferencePublicBudgetRevelationGapQuestion answer.truthfulFactor answer.strategicFactor answer.gap

end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

end


/-!
## Questions and answers
-/

namespace EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget

/-- Supply the numerical factors and gap for the reference symmetric public-budget model. -/
theorem publicBudgetRevelationGap :
    PublicBudgetGapAnswer.IsCorrect (answer(sorry)) := by
  sorry

end EconCSLib.OpenProblem.New.EconCSBench.RevelationGapPublicBudget
